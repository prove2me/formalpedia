-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1124_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:11:02.640728+00:00
-- url     : https://prove2.me/submissions/1ab58e2f-6311-4cee-90d2-fb854ff8f3a6

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Definitions.Def_HlawkaSchatten_DiagonalCutoff6_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff6_signed_majorant
/- Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa,
bwdaugherty and Yuxuan Xu. All new numerical implications are checked below. -/
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalConstruction

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The coordinate `p`-norm is nonnegative. -/
theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

/-- The coordinate `p`-norm agrees with the `PiLp` norm. -/
theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

/-- The `p`-norm of zero is zero. -/
@[simp]
theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

/-- The `p`-norm is invariant under negation. -/
@[simp]
theorem lpNorm_neg (p : ℝ) (x : ι → E) : lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]

/-- Minkowski's inequality for the coordinate `p`-norm. -/
theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

/-- Each coordinate norm is at most the `p`-norm. -/
theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

/-- Raising the `p`-norm to the `p`-th power recovers the sum of `p`-th powers. -/
theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm vanishes iff the vector is zero. -/
theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ‖x i‖ ^ p) = 0 := by
      rw [← lpNorm_rpow hp x, h, Real.zero_rpow hp.ne']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)).mp hs
    funext i
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg (x i)) hp.ne').mp
      (hi i (Finset.mem_univ i)))
  · rintro rfl
    exact lpNorm_zero hp

/-- A nonzero vector has strictly positive `p`-norm. -/
theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))

/-- The `p`-norm of a constant vector. -/
theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The `p`-norm scales homogeneously. -/
theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- The coordinate `p`-norm is convex for `p ≥ 1`. -/
theorem convexOn_lpNorm [NormedSpace ℝ E] {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (lpNorm p : (ι → E) → ℝ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb _
  have hp0 := zero_lt_one.trans_le hp
  simpa only [lpNorm_smul hp0, abs_of_nonneg ha, abs_of_nonneg hb, smul_eq_mul]
    using lpNorm_add hp (a • x) (b • y)

/-- The coordinate `p`-norm is continuous. -/
theorem continuous_lpNorm {p : ℝ} (hp : 0 < p) :
    Continuous (lpNorm p : (ι → E) → ℝ) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).norm.rpow_const (fun _ ↦ Or.inr hp.le)).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

/-- The `p`-norm is at most `n^(1/p) * M` when each coordinate norm is at most `M`. -/
theorem lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by
  have hsum : (∑ i, ‖x i‖ ^ p) ≤ (Fintype.card ι : ℝ) * M ^ p := by
    calc
      _ ≤ ∑ _ : ι, M ^ p :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM _),
    ← Real.rpow_mul hM, mul_one_div_cancel hp.ne', Real.rpow_one] at h
  exact h

/-- The `p`-norm of real coordinates equals the `p`-norm of their complex embeddings. -/
theorem lpNorm_ofReal (p : ℝ) (x : ι → ℝ) :
    lpNorm p (fun i ↦ (x i : ℂ)) = lpNorm p x := by
  simp [lpNorm]

/-- Appending zero coordinates does not change the `p`-norm. -/
theorem lpNorm_fin_append_zero {p : ℝ} (hp : 0 < p) {n : ℕ}
    (x : Fin n → E) (m : ℕ) :
    lpNorm p (Fin.append x (0 : Fin m → E)) = lpNorm p x := by
  simp [lpNorm, Fin.sum_univ_add, hp.ne']

/-- A Hlawka constant in dimension `n` is also admissible in every lower dimension. -/
theorem hasHlawkaConstant_fin_of_le {p C : ℝ} (hp : 0 < p)
    {m n : ℕ} (hn : m ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin m → E) → ℝ) C := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  intro x y z
  have h := hC (Fin.append x (0 : Fin k → E))
    (Fin.append y (0 : Fin k → E)) (Fin.append z (0 : Fin k → E))
  have hadd (u v : Fin m → E) :
      Fin.append u (0 : Fin k → E) + Fin.append v (0 : Fin k → E) =
        Fin.append (u + v) (0 : Fin k → E) := by
    ext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_fin_append_zero hp] using h

/-- A Hlawka constant in dimension `n ≥ 3` is admissible in dimension 3. -/
theorem hasHlawkaConstant_fin_three_of_ge {p C : ℝ} (hp : 0 < p)
    {n : ℕ} (hn : 3 ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C :=
  hasHlawkaConstant_fin_of_le hp hn hC

/-- The `p`-norm is invariant under coordinate permutation. -/
theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

/-- The `p`-norm restricted to a subtype equals the full norm when unsupported entries vanish. -/
theorem lpNorm_subtype {p : ℝ} (hp : 0 < p) (x : ι → E)
    (P : ι → Prop) [DecidablePred P] (hx : ∀ i, ¬P i → x i = 0) :
    lpNorm p (fun i : Subtype P ↦ x i.1) = lpNorm p x := by
  unfold lpNorm
  congr 1
  have hzero : (∑ i : {i : ι // ¬P i}, ‖x i.1‖ ^ p) = 0 := by
    exact Finset.sum_eq_zero fun i _ ↦ by simp [hx i.1 i.2, hp.ne']
  rw [← Fintype.sum_subtype_add_sum_subtype P (fun i ↦ ‖x i‖ ^ p), hzero, add_zero]

/-- A Hlawka constant in dimension 3 lifts to any index type of cardinality at most 3. -/
theorem hasHlawkaConstant_of_card_le_three {p C : ℝ} (hp : 0 < p)
    (hcard : Fintype.card ι ≤ 3)
    (hC : HasHlawkaConstant (lpNorm p : (Fin 3 → E) → ℝ) C) :
    HasHlawkaConstant (lpNorm p : (ι → E) → ℝ) C := by
  let e := (Fintype.equivFin ι).symm
  have hf := hasHlawkaConstant_fin_of_le hp hcard hC
  intro x y z
  have h := hf (x ∘ e) (y ∘ e) (z ∘ e)
  have hadd (u v : ι → E) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
  simpa only [tripleGap, pairGapSum, pairGap, hadd, lpNorm_comp_equiv] using h

/-- The pair deficit is nonneg for `p ≥ 1` by Minkowski. -/
theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

/-- The sum of pair deficits is nonneg for `p ≥ 1`. -/
theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)

end HlawkaSchatten.DiagonalConstruction
namespace HlawkaSchatten.DiagonalRealBundle
theorem sum3 (f : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∑ l, f l = f i + f j + f k := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring
theorem lpNorm_eq3 (p : ℝ) (x : Fin 3 → ℝ) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : lpNorm p x = (|x i| ^ p + |x j| ^ p + |x k| ^ p) ^ (1/p) := by
  unfold lpNorm
  rw [sum3 (fun l ↦ ‖x l‖ ^ p) hij hik hjk]
  simp [Real.norm_eq_abs]
end HlawkaSchatten.DiagonalRealBundle
namespace HlawkaSchatten.DiagonalRealBundle
theorem le_rpow_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (m k : ℕ) (hk : 0 < k)
    (h : X ^ k ≤ x ^ m) : X ≤ x ^ ((m : ℝ) / k) := by
  rcases le_or_gt X 0 with hX | hX
  · exact hX.trans (Real.rpow_nonneg hx _)
  · have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
      rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
    rw [e]
    calc X = (X ^ k) ^ ((k : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hX.le hk.ne').symm
      _ ≤ (x ^ m) ^ ((k : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) h (by positivity)
theorem rpow_le_of_pow_le {x X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) (m k : ℕ) (hk : 0 < k)
    (h : x ^ m ≤ X ^ k) : x ^ ((m : ℝ) / k) ≤ X := by
  have e : x ^ ((m : ℝ) / k) = (x ^ m) ^ ((k : ℝ)⁻¹) := by
    rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  rw [e]
  calc (x ^ m) ^ ((k : ℝ)⁻¹) ≤ (X ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = X := Real.pow_rpow_inv_natCast hX hk.ne'
end HlawkaSchatten.DiagonalRealBundle

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff12
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators

theorem norm_support {ι : Type*} [Fintype ι] {p q : ℝ}
    (hpq : p.HolderConjugate q) (w x : ι → ℝ)
    (hw : (∑ i, |w i| ^ q) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have h := Real.inner_le_Lp_mul_Lq Finset.univ w x hpq.symm
  have hq : 0 ≤ 1/q := hpq.symm.one_div_nonneg
  have hr := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (w i)) q) hw hq
  rw [Real.one_rpow] at hr
  have hn := lpNorm_nonneg p x
  have hm := mul_le_mul_of_nonneg_right hr hn
  simpa only [lpNorm, Real.norm_eq_abs, one_mul] using h.trans hm

theorem power12over11_upper {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x^12 ≤ y^11) : x^(12/11 : ℝ) ≤ y := by
  have hr := Real.rpow_le_rpow (pow_nonneg hx 12) h (by norm_num : (0 : ℝ) ≤ 1/11)
  rw [← Real.rpow_natCast x 12, ← Real.rpow_natCast y 11,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy] at hr
  norm_num at hr ⊢
  exact hr

theorem norm_support12 (w v x : Fin 3 → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hp : ∀ i, |w i|^12 ≤ (v i)^11)
    (hs : (∑ i, v i) ≤ 1) : (∑ i, w i*x i) ≤ lpNorm 12 x := by
  apply norm_support (q := 12/11)
    (Real.holderConjugate_iff.mpr (by norm_num))
  exact (Finset.sum_le_sum fun i _ => power12over11_upper (abs_nonneg _) (hv i) (hp i)).trans hs

theorem power_ratio_upper {x y : ℝ} (m n : ℕ) (hn : 0 < n)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x^m ≤ y^n) :
    x^((m : ℝ)/(n : ℝ)) ≤ y := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hr := Real.rpow_le_rpow (pow_nonneg hx m) h (one_div_nonneg.mpr hn0.le)
  rw [← Real.rpow_natCast x m, ← Real.rpow_natCast y n,
    ← Real.rpow_mul hx, ← Real.rpow_mul hy,
    mul_one_div_cancel hn0.ne', Real.rpow_one] at hr
  simpa only [div_eq_mul_inv, one_div, one_mul] using hr

theorem norm_support_interval {p b : ℝ} (hp : 1 < p) (hb : 1 < b)
    (hpb : p ≤ b) (w x : Fin 3 → ℝ)
    (hw1 : ∀ i, |w i| ≤ 1)
    (hw : (∑ i, |w i|^(b/(b-1))) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  have hqp : b/(b-1) ≤ p/(p-1) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith
  have hq0 : 0 ≤ b/(b-1) := div_nonneg (by linarith) (by linarith)
  apply norm_support (q := p/(p-1))
    ((Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl)
  apply le_trans _ hw
  exact Finset.sum_le_sum fun i _ => Real.rpow_le_rpow_of_exponent_ge'
    (abs_nonneg _) (hw1 i) hq0 hqp

theorem norm_support_interval_cert {p b : ℝ} (m n : ℕ) (hn : 0 < n)
    (hp : 1 < p) (hb : 1 < b) (hpb : p ≤ b)
    (hconj : b/(b-1) = (m : ℝ)/(n : ℝ))
    (w v x : Fin 3 → ℝ) (hw1 : ∀ i, |w i| ≤ 1) (hv : ∀ i, 0 ≤ v i)
    (hpowers : ∀ i, |w i|^m ≤ (v i)^n) (hs : (∑ i, v i) ≤ 1) :
    (∑ i, w i*x i) ≤ lpNorm p x := by
  apply norm_support_interval hp hb hpb w x hw1
  rw [hconj]
  exact (Finset.sum_le_sum fun i _ =>
    power_ratio_upper m n hn (abs_nonneg _) (hv i) (hpowers i)).trans hs

end HlawkaSchatten.DiagonalCutoff12


set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6




theorem total_eq (X : Fin 3 → Fin 3 → ℝ) : total X = X 0+X 1+X 2 := by
  simp [total,Fin.sum_univ_three]
theorem pair0 (X : Fin 3 → Fin 3 → ℝ) : pair X 0 = X 1+X 2 := by
  rw [pair,total_eq];abel
theorem pair1 (X : Fin 3 → Fin 3 → ℝ) : pair X 1 = X 0+X 2 := by
  rw [pair,total_eq];abel
theorem pair2 (X : Fin 3 → Fin 3 → ℝ) : pair X 2 = X 0+X 1 := by
  rw [pair,total_eq];abel


theorem oriented_frame {p q k d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : RelativeOrientedData p q k d X) : Frame p k (3*q) d X := by
  constructor
  · simpa [Fin.sum_univ_three] using h.sum
  · simpa [total_eq] using h.norm_le_total
  · simpa [total_eq] using h.total_one
  · simpa [total_eq] using h.total_cap.le
  · intro i;fin_cases i
    · simpa [pair0] using h.main0
    · simpa [pair1] using h.main1
    · simpa [pair2] using h.main2
  · intro i h';fin_cases i
    · simpa [pair0] using h.max0 h'
    · simpa [pair1] using h.max1 h'
    · simpa [pair2] using h.max2 h'
  · simpa [total_eq,Fin.sum_univ_three,pair0,pair1,pair2] using h.linear_failure

theorem total_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) :
    total (relabel e X) = total X ∘ e := by
  ext h
  simp only [total,Finset.sum_apply,relabel,Function.comp_apply]
  exact Equiv.sum_comp e (fun j => X j (e h))

theorem pair_relabel (e : Equiv.Perm (Fin 3)) (X : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    pair (relabel e X) i = pair X (e i) ∘ e := by
  ext h
  simp [pair,total_relabel,relabel]

theorem frame_relabel {p k A d : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (h : Frame p k A d X) (e : Equiv.Perm (Fin 3)) : Frame p k A d (relabel e X) := by
  have hr (j : Fin 3) : lpNorm p (relabel e X j) = lpNorm p (X (e j)) :=
    lpNorm_comp_equiv p (X (e j)) e
  have ht : lpNorm p (total (relabel e X)) = lpNorm p (total X) := by
    rw [total_relabel,lpNorm_comp_equiv]
  have hp (i : Fin 3) : lpNorm p (pair (relabel e X) i) = lpNorm p (pair X (e i)) := by
    rw [pair_relabel,lpNorm_comp_equiv]
  constructor
  · simp_rw [hr];rw [Equiv.sum_comp e (fun j => lpNorm p (X j))];exact h.sum
  · intro j;rw [hr,ht];exact h.row_total (e j)
  · rw [ht];exact h.total_one
  · rw [ht];exact h.total_cap
  · intro i;rw [hp,pair_relabel];exact h.main (e i)
  · intro i j;rw [pair_relabel];exact h.maximal (e i) (e j)
  · simp_rw [ht,hp];rw [Equiv.sum_comp e (fun i => lpNorm p (pair X i))];exact h.linear_failure

theorem frame_box_of_base {p k A d ell u v w rho : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_ratio_of_base {p k A d rho R : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) :
    ∀ i h, i ≠ h → |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201

end HlawkaSchatten.DiagonalCutoff6

set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction
open scoped BigOperators
namespace HlawkaSchatten.DiagonalCutoff6


theorem pair_eq_of_distinct (X : Fin 3 → Fin 3 → ℝ) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : pair X i = X j+X l := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
  all_goals first
    | exact pair0 X
    | exact (pair0 X).trans (add_comm _ _)
    | exact pair1 X
    | exact (pair1 X).trans (add_comm _ _)
    | exact pair2 X
    | exact (pair2 X).trans (add_comm _ _)

theorem frame_linear_data {p k A d : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : Frame p k A d X) :
    LinearData k A d X (fun j => lpNorm p (X j))
      (fun i => lpNorm p (pair X i)) (lpNorm p (total X)) := by
  have hn (j : Fin 3) := lpNorm_nonneg p (X j)
  have hs : lpNorm p (X 0)+lpNorm p (X 1)+lpNorm p (X 2)=3 := by
    simpa [Fin.sum_univ_three] using h.sum
  constructor
  · exact hs
  · exact hn
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap
  · intro j i;exact abs_le.mp (norm_apply_le_lpNorm hp (X j) i)
  · intro i;simpa [total_eq] using abs_le.mp (norm_apply_le_lpNorm hp (total X) i)
  · intro i;exact lpNorm_nonneg p (pair X i)
  · intro i;fin_cases i
    · change lpNorm p (pair X 0) ≤ 3-lpNorm p (X 0)
      rw [pair0];linarith only [lpNorm_add hp (X 1) (X 2),hs]
    · change lpNorm p (pair X 1) ≤ 3-lpNorm p (X 1)
      rw [pair1];linarith only [lpNorm_add hp (X 0) (X 2),hs]
    · change lpNorm p (pair X 2) ≤ 3-lpNorm p (X 2)
      rw [pair2];linarith only [lpNorm_add hp (X 0) (X 1),hs]
  · exact h.main
  · exact h.maximal
  · intro i
    have hh := lpNorm_add hp (total X) (-X i)
    simpa [pair,sub_eq_add_neg] using hh
  · intro i
    have hh := lpNorm_add hp (pair X i) (X i)
    simpa [pair] using hh
  · intro i j l hij hil hjl
    rw [pair_eq_of_distinct X i j l hij hil hjl]
    have hh := lpNorm_add hp (X j+X l) (-X l)
    have he : X j+X l+-X l = X j := by abel
    rw [he,lpNorm_neg] at hh
    linarith
  · simpa [Fin.sum_univ_three] using h.linear_failure

theorem linear_data_bounds {k A d T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : LinearData k A d X N P T) (hA : A ≤ 3) :
    (∀ j i, -3 ≤ X j i ∧ X j i ≤ 3) ∧
    (∀ j, -3 ≤ N j ∧ N j ≤ 3) ∧ (∀ i, -3 ≤ P i ∧ P i ≤ 3) ∧ (-3 ≤ T ∧ T ≤ 3) := by
  have hN (j : Fin 3) : 0 ≤ N j ∧ N j ≤ 3 := by
    refine ⟨h.Nnonneg j,?_⟩
    exact ((h.Ntotal j).trans h.Tcap).trans hA
  refine ⟨?_,?_,?_,?_⟩
  · intro j i;have hc := h.coord j i;have hn := hN j;constructor <;> linarith
  · intro j;have hn := hN j;constructor <;> linarith
  · intro i;have hn := hN i;have ht := h.Ptriangle i
    have hz := h.Pnonneg i;constructor <;> linarith
  · constructor <;> linarith only [h.Tone,h.Tcap,hA]

theorem positive_pair_majorant {p a rho alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha)
    (hc1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hc2 : 1+2*rho^a ≤ (1+2*alpha*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hm : ∀ i, 0 ≤ pair X i i)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ pair X i i+alpha*(pair X i j+pair X i l) := by
  rw [HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p _ hij hil hjl]
  have hh := signed_majorant hp ha hap hrho hrho1 halpha hc1 hc2 (hm i)
    (hratio i j hij) (hratio i l hil)
  simpa only [abs_of_nonneg (hsign i j hij),abs_of_nonneg (hsign i l hil)] using hh

theorem frame_weaken {p k A d k' A' d' : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (hp : 1 ≤ p) (h : Frame p k A d X) (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    Frame p k' A' d' X := by
  have f := frame_linear_data hp X h
  have hs : (∑ i, lpNorm p (pair X i)) ≤ 6 := by
    rw [Fin.sum_univ_three]
    have hh := f.sum
    linarith only [f.Ptriangle 0,f.Ptriangle 1,f.Ptriangle 2,hh]
  constructor
  · exact h.sum
  · exact h.row_total
  · exact h.total_one
  · exact h.total_cap.trans hA
  · intro i
    exact (mul_le_mul_of_nonneg_right hd (lpNorm_nonneg p (pair X i))).trans (h.main i)
  · exact h.maximal
  · have hh := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hs)
    linarith only [hh,h.linear_failure]

end HlawkaSchatten.DiagonalCutoff6
set_option autoImplicit false
set_option maxHeartbeats 4000000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -u ≤ X j i ∧ X j i ≤ -ell else v ≤ X j i ∧ X j i ≤ w := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      -u ≤ X (e 0) (e 0) ∧ X (e 0) (e 0) ≤ -ell ∧
      v ≤ X (e 0) (e 1) ∧ X (e 0) (e 1) ≤ w := by
    apply base (relabel e X) (frame_relabel hX e)
    · intro i j hij
      rw [pair_relabel]
      exact hsign (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hratio (e i) (e j) (e.injective.ne hij)
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro j i
  fin_cases j <;> fin_cases i <;> simp only [ite_true,ite_false]
  · exact ⟨h0.1,h0.2.1⟩
  · exact h0.2.2
  · exact h12.2.2
  · exact h01.2.2
  · exact ⟨h01.1,h01.2.1⟩
  · exact h120.2.2
  · exact h201.2.2
  · exact h02.2.2
  · exact ⟨h02.1,h02.2.1⟩

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
    simpa only [pair_relabel,Function.comp_apply] using hh
  have h0 := permuted (Equiv.refl (Fin 3))
  have h01 := permuted (Equiv.swap (0 : Fin 3) 1)
  have h02 := permuted (Equiv.swap (0 : Fin 3) 2)
  have h12 := permuted (Equiv.swap (1 : Fin 3) 2)
  have h120 := permuted ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1))
  have h201 := permuted ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2))
  norm_num [Equiv.swap_apply_def] at h0 h01 h02 h12 h120 h201
  intro i j hij
  rw [abs_of_nonneg (hsign i j hij)]
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals first | exact h0 | exact h01 | exact h02 | exact h12 | exact h120 | exact h201


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

end HlawkaSchatten.DiagonalCutoff4

set_option autoImplicit false
namespace HlawkaSchatten.DiagonalCutoff4

theorem rational_powers_le (a b c d m n : ℕ) (hb : 0 < b) (hd : 0 < d)
    (h : a^m*d^n ≤ c^n*b^m) :
    ((a : ℝ)/b)^m ≤ ((c : ℝ)/d)^n := by
  rw [div_pow,div_pow]
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  apply (div_le_div_iff₀ (pow_pos hb' m) (pow_pos hd' n)).mpr
  exact_mod_cast h

theorem rectangle_budgets {a lo hi c alpha pl ph : ℝ}
    (hl : lo^a ≤ pl) (hh : hi^a ≤ ph)
    (h00 : 1+2*pl ≤ (c+2*alpha*lo)^a)
    (h10 : 1+ph+pl ≤ (c+alpha*(hi+lo))^a)
    (h11 : 1+2*ph ≤ (c+2*alpha*hi)^a) :
    1+2*lo^a ≤ (c+2*alpha*lo)^a ∧
    1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a ∧
    1+2*hi^a ≤ (c+2*alpha*hi)^a := by
  constructor
  · linarith only [hl,h00]
  constructor
  · linarith only [hl,hh,h10]
  · linarith only [hh,h11]

theorem sum_two_bounds {x y X Y z : ℝ} (hx : x ≤ X) (hy : y ≤ Y)
    (hz : X+2*Y ≤ z) : x+2*y ≤ z := by
  linarith only [hx,hy,hz]

theorem three_bounds {x X : ℝ} (hx : x ≤ X) (hX : 3*X ≤ 1) : x+x+x ≤ 1 := by
  linarith only [hx,hX]

end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1124_s6_0 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-21754903/100000000 : ℝ)*x 0 + (215749517/400000000 : ℝ)*x 1 + (5265085731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21754903/100000000 : ℝ)^8317 ≤ (2643478391961/20000000000000 : ℝ)^6269 := by
    have hnat : (21754903 : ℕ)^8317*20000000000000^6269 ≤ 2643478391961^6269*100000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21754903 100000000 2643478391961 20000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215749517/400000000 : ℝ)^8317 ≤ (44086109150859/100000000000000 : ℝ)^6269 := by
    have hnat : (215749517 : ℕ)^8317*100000000000000^6269 ≤ 44086109150859^6269*400000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215749517 400000000 44086109150859 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265085731/10000000000 : ℝ)^8317 ≤ (5337062358789/12500000000000 : ℝ)^6269 := by
    have hnat : (5265085731 : ℕ)^8317*12500000000000^6269 ≤ 5337062358789^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265085731 10000000000 5337062358789 12500000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21754903/100000000 : ℝ), (215749517/400000000 : ℝ), (5265085731/10000000000 : ℝ)] ![(2643478391961/20000000000000 : ℝ), (44086109150859/100000000000000 : ℝ), (5337062358789/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21754903/100000000 : ℝ)|^8317 ≤ (2643478391961/20000000000000 : ℝ)^6269
        have hw : |(-21754903/100000000 : ℝ)|=(21754903/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215749517/400000000 : ℝ)|^8317 ≤ (44086109150859/100000000000000 : ℝ)^6269
        have hw : |(215749517/400000000 : ℝ)|=(215749517/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265085731/10000000000 : ℝ)|^8317 ≤ (5337062358789/12500000000000 : ℝ)^6269
        have hw : |(5265085731/10000000000 : ℝ)|=(5265085731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s6_1 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672458441/5000000000 : ℝ)*x 0 + (-2240754891/10000000000 : ℝ)*x 1 + (164533929/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672458441/5000000000 : ℝ)^8317 ≤ (21778744613087/50000000000000 : ℝ)^6269 := by
    have hnat : (2672458441 : ℕ)^8317*50000000000000^6269 ≤ 21778744613087^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672458441 5000000000 21778744613087 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2240754891/10000000000 : ℝ)^8317 ≤ (6873005961553/50000000000000 : ℝ)^6269 := by
    have hnat : (2240754891 : ℕ)^8317*50000000000000^6269 ≤ 6873005961553^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240754891 10000000000 6873005961553 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164533929/312500000 : ℝ)^8317 ≤ (10674124709509/25000000000000 : ℝ)^6269 := by
    have hnat : (164533929 : ℕ)^8317*25000000000000^6269 ≤ 10674124709509^6269*312500000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164533929 312500000 10674124709509 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672458441/5000000000 : ℝ), (-2240754891/10000000000 : ℝ), (164533929/312500000 : ℝ)] ![(21778744613087/50000000000000 : ℝ), (6873005961553/50000000000000 : ℝ), (10674124709509/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672458441/5000000000 : ℝ)|^8317 ≤ (21778744613087/50000000000000 : ℝ)^6269
        have hw : |(2672458441/5000000000 : ℝ)|=(2672458441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2240754891/10000000000 : ℝ)|^8317 ≤ (6873005961553/50000000000000 : ℝ)^6269
        have hw : |(-2240754891/10000000000 : ℝ)|=(2240754891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164533929/312500000 : ℝ)|^8317 ≤ (10674124709509/25000000000000 : ℝ)^6269
        have hw : |(164533929/312500000 : ℝ)|=(164533929/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s6_2 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534491687/1000000000 : ℝ)*x 0 + (2632542871/5000000000 : ℝ)*x 1 + (-280094361/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534491687/1000000000 : ℝ)^8317 ≤ (8711497819287/20000000000000 : ℝ)^6269 := by
    have hnat : (534491687 : ℕ)^8317*20000000000000^6269 ≤ 8711497819287^6269*1000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534491687 1000000000 8711497819287 20000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632542871/5000000000 : ℝ)^8317 ≤ (42696498988657/100000000000000 : ℝ)^6269 := by
    have hnat : (2632542871 : ℕ)^8317*100000000000000^6269 ≤ 42696498988657^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632542871 5000000000 42696498988657 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280094361/1250000000 : ℝ)^8317 ≤ (13746011898691/100000000000000 : ℝ)^6269 := by
    have hnat : (280094361 : ℕ)^8317*100000000000000^6269 ≤ 13746011898691^6269*1250000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280094361 1250000000 13746011898691 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534491687/1000000000 : ℝ), (2632542871/5000000000 : ℝ), (-280094361/1250000000 : ℝ)] ![(8711497819287/20000000000000 : ℝ), (42696498988657/100000000000000 : ℝ), (13746011898691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534491687/1000000000 : ℝ)|^8317 ≤ (8711497819287/20000000000000 : ℝ)^6269
        have hw : |(534491687/1000000000 : ℝ)|=(534491687/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632542871/5000000000 : ℝ)|^8317 ≤ (42696498988657/100000000000000 : ℝ)^6269
        have hw : |(2632542871/5000000000 : ℝ)|=(2632542871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-280094361/1250000000 : ℝ)|^8317 ≤ (13746011898691/100000000000000 : ℝ)^6269
        have hw : |(-280094361/1250000000 : ℝ)|=(280094361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s6_3 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2183598133/5000000000 : ℝ)*x 0 + (1060383343/2500000000 : ℝ)*x 1 + (2248290111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183598133/5000000000 : ℝ)^8317 ≤ (33316675491613/100000000000000 : ℝ)^6269 := by
    have hnat : (2183598133 : ℕ)^8317*100000000000000^6269 ≤ 33316675491613^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183598133 5000000000 33316675491613 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060383343/2500000000 : ℝ)^8317 ≤ (256406772973/800000000000 : ℝ)^6269 := by
    have hnat : (1060383343 : ℕ)^8317*800000000000^6269 ≤ 256406772973^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060383343 2500000000 256406772973 800000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248290111/5000000000 : ℝ)^8317 ≤ (3463247786579/10000000000000 : ℝ)^6269 := by
    have hnat : (2248290111 : ℕ)^8317*10000000000000^6269 ≤ 3463247786579^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248290111 5000000000 3463247786579 10000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183598133/5000000000 : ℝ), (1060383343/2500000000 : ℝ), (2248290111/5000000000 : ℝ)] ![(33316675491613/100000000000000 : ℝ), (256406772973/800000000000 : ℝ), (3463247786579/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183598133/5000000000 : ℝ)|^8317 ≤ (33316675491613/100000000000000 : ℝ)^6269
        have hw : |(2183598133/5000000000 : ℝ)|=(2183598133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060383343/2500000000 : ℝ)|^8317 ≤ (256406772973/800000000000 : ℝ)^6269
        have hw : |(1060383343/2500000000 : ℝ)|=(1060383343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248290111/5000000000 : ℝ)|^8317 ≤ (3463247786579/10000000000000 : ℝ)^6269
        have hw : |(2248290111/5000000000 : ℝ)|=(2248290111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s6_4 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2175495447/10000000000 : ℝ)*x 0 + (2632705247/5000000000 : ℝ)*x 1 + (5393411881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175495447/10000000000 : ℝ)^8317 ≤ (13217433446743/100000000000000 : ℝ)^6269 := by
    have hnat : (2175495447 : ℕ)^8317*100000000000000^6269 ≤ 13217433446743^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175495447 10000000000 13217433446743 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632705247/5000000000 : ℝ)^8317 ≤ (8539998579321/20000000000000 : ℝ)^6269 := by
    have hnat : (2632705247 : ℕ)^8317*20000000000000^6269 ≤ 8539998579321^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632705247 5000000000 8539998579321 20000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393411881/10000000000 : ℝ)^8317 ≤ (8816514727819/20000000000000 : ℝ)^6269 := by
    have hnat : (5393411881 : ℕ)^8317*20000000000000^6269 ≤ 8816514727819^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393411881 10000000000 8816514727819 20000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2175495447/10000000000 : ℝ), (2632705247/5000000000 : ℝ), (5393411881/10000000000 : ℝ)] ![(13217433446743/100000000000000 : ℝ), (8539998579321/20000000000000 : ℝ), (8816514727819/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2175495447/10000000000 : ℝ)|^8317 ≤ (13217433446743/100000000000000 : ℝ)^6269
        have hw : |(-2175495447/10000000000 : ℝ)|=(2175495447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632705247/5000000000 : ℝ)|^8317 ≤ (8539998579321/20000000000000 : ℝ)^6269
        have hw : |(2632705247/5000000000 : ℝ)|=(2632705247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393411881/10000000000 : ℝ)|^8317 ≤ (8816514727819/20000000000000 : ℝ)^6269
        have hw : |(5393411881/10000000000 : ℝ)|=(5393411881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s6_5 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656183067/5000000000 : ℝ)*x 0 + (-1056214369/5000000000 : ℝ)*x 1 + (539341187/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656183067/5000000000 : ℝ)^8317 ≤ (10801478461171/25000000000000 : ℝ)^6269 := by
    have hnat : (2656183067 : ℕ)^8317*25000000000000^6269 ≤ 10801478461171^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656183067 5000000000 10801478461171 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056214369/5000000000 : ℝ)^8317 ≤ (1588939076721/12500000000000 : ℝ)^6269 := by
    have hnat : (1056214369 : ℕ)^8317*12500000000000^6269 ≤ 1588939076721^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056214369 5000000000 1588939076721 12500000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539341187/1000000000 : ℝ)^8317 ≤ (5510321689977/12500000000000 : ℝ)^6269 := by
    have hnat : (539341187 : ℕ)^8317*12500000000000^6269 ≤ 5510321689977^6269*1000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539341187 1000000000 5510321689977 12500000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656183067/5000000000 : ℝ), (-1056214369/5000000000 : ℝ), (539341187/1000000000 : ℝ)] ![(10801478461171/25000000000000 : ℝ), (1588939076721/12500000000000 : ℝ), (5510321689977/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656183067/5000000000 : ℝ)|^8317 ≤ (10801478461171/25000000000000 : ℝ)^6269
        have hw : |(2656183067/5000000000 : ℝ)|=(2656183067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1056214369/5000000000 : ℝ)|^8317 ≤ (1588939076721/12500000000000 : ℝ)^6269
        have hw : |(-1056214369/5000000000 : ℝ)|=(1056214369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539341187/1000000000 : ℝ)|^8317 ≤ (5510321689977/12500000000000 : ℝ)^6269
        have hw : |(539341187/1000000000 : ℝ)|=(539341187/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s6_6 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312366199/10000000000 : ℝ)*x 0 + (2696705857/5000000000 : ℝ)*x 1 + (-2112428863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312366199/10000000000 : ℝ)^8317 ≤ (21602957273019/50000000000000 : ℝ)^6269 := by
    have hnat : (5312366199 : ℕ)^8317*50000000000000^6269 ≤ 21602957273019^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312366199 10000000000 21602957273019 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696705857/5000000000 : ℝ)^8317 ≤ (44082571828221/100000000000000 : ℝ)^6269 := by
    have hnat : (2696705857 : ℕ)^8317*100000000000000^6269 ≤ 44082571828221^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696705857 5000000000 44082571828221 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112428863/10000000000 : ℝ)^8317 ≤ (3177878402921/25000000000000 : ℝ)^6269 := by
    have hnat : (2112428863 : ℕ)^8317*25000000000000^6269 ≤ 3177878402921^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112428863 10000000000 3177878402921 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312366199/10000000000 : ℝ), (2696705857/5000000000 : ℝ), (-2112428863/10000000000 : ℝ)] ![(21602957273019/50000000000000 : ℝ), (44082571828221/100000000000000 : ℝ), (3177878402921/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312366199/10000000000 : ℝ)|^8317 ≤ (21602957273019/50000000000000 : ℝ)^6269
        have hw : |(5312366199/10000000000 : ℝ)|=(5312366199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696705857/5000000000 : ℝ)|^8317 ≤ (44082571828221/100000000000000 : ℝ)^6269
        have hw : |(2696705857/5000000000 : ℝ)|=(2696705857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2112428863/10000000000 : ℝ)|^8317 ≤ (3177878402921/25000000000000 : ℝ)^6269
        have hw : |(-2112428863/10000000000 : ℝ)|=(2112428863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s6_7 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4367206197/10000000000 : ℝ)*x 0 + (2247968081/5000000000 : ℝ)*x 1 + (4242179779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367206197/10000000000 : ℝ)^8317 ≤ (4164597000527/12500000000000 : ℝ)^6269 := by
    have hnat : (4367206197 : ℕ)^8317*12500000000000^6269 ≤ 4164597000527^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367206197 10000000000 4164597000527 12500000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247968081/5000000000 : ℝ)^8317 ≤ (34625896957821/100000000000000 : ℝ)^6269 := by
    have hnat : (2247968081 : ℕ)^8317*100000000000000^6269 ≤ 34625896957821^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247968081 5000000000 34625896957821 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4242179779/10000000000 : ℝ)^8317 ≤ (8014331755769/25000000000000 : ℝ)^6269 := by
    have hnat : (4242179779 : ℕ)^8317*25000000000000^6269 ≤ 8014331755769^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242179779 10000000000 8014331755769 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367206197/10000000000 : ℝ), (2247968081/5000000000 : ℝ), (4242179779/10000000000 : ℝ)] ![(4164597000527/12500000000000 : ℝ), (34625896957821/100000000000000 : ℝ), (8014331755769/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367206197/10000000000 : ℝ)|^8317 ≤ (4164597000527/12500000000000 : ℝ)^6269
        have hw : |(4367206197/10000000000 : ℝ)|=(4367206197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247968081/5000000000 : ℝ)|^8317 ≤ (34625896957821/100000000000000 : ℝ)^6269
        have hw : |(2247968081/5000000000 : ℝ)|=(2247968081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4242179779/10000000000 : ℝ)|^8317 ≤ (8014331755769/25000000000000 : ℝ)^6269
        have hw : |(4242179779/10000000000 : ℝ)|=(4242179779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1124_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11289/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5661/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14047/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11289/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14081/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11289/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11289/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14081/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11289/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11289/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14081/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11289/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (11289/100000 : ℝ) ^ (2079/512 : ℝ) ≤ (1778988556724511/12500000000000000000 : ℝ) := by
    have hpowers : (11289/100000 : ℝ)^2079 ≤ (1778988556724511/12500000000000000000 : ℝ)^512 := by
      have hnat : (11289 : ℕ)^2079*12500000000000000000^512 ≤ 1778988556724511^512*100000^2079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11289 100000 1778988556724511 12500000000000000000 2079 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11289/100000 : ℝ)) (X := (1778988556724511/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14081/100000 : ℝ) ^ (2079/512 : ℝ) ≤ (34912939256484933/100000000000000000000 : ℝ) := by
    have hpowers : (14081/100000 : ℝ)^2079 ≤ (34912939256484933/100000000000000000000 : ℝ)^512 := by
      have hnat : (14081 : ℕ)^2079*100000000000000000000^512 ≤ 34912939256484933^512*100000^2079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14081 100000 34912939256484933 100000000000000000000 2079 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14081/100000 : ℝ)) (X := (34912939256484933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251778988556724511/6250000000000000000 : ℝ) ≤ (1000070090963071/1000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (6251778988556724511/6250000000000000000 : ℝ)^512 ≤ (1000070090963071/1000000000000000 : ℝ)^2079 := by
      have hnat : (6251778988556724511 : ℕ)^512*1000000000000000^2079 ≤ 1000070090963071^2079*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251778988556724511 6250000000000000000 1000070090963071 1000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000070090963071/1000000000000000 : ℝ)) (X := (6251778988556724511/6250000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049144847710281021/100000000000000000000 : ℝ) ≤ (10001210077109317/10000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (100049144847710281021/100000000000000000000 : ℝ)^512 ≤ (10001210077109317/10000000000000000 : ℝ)^2079 := by
      have hnat : (100049144847710281021 : ℕ)^512*10000000000000000^2079 ≤ 10001210077109317^2079*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049144847710281021 100000000000000000000 10001210077109317 10000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001210077109317/10000000000000000 : ℝ)) (X := (100049144847710281021/100000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034912939256484933/50000000000000000000 : ℝ) ≤ (2500429811146981/2500000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (50034912939256484933/50000000000000000000 : ℝ)^512 ≤ (2500429811146981/2500000000000000 : ℝ)^2079 := by
      have hnat : (50034912939256484933 : ℕ)^512*2500000000000000^2079 ≤ 2500429811146981^2079*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034912939256484933 50000000000000000000 2500429811146981 2500000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500429811146981/2500000000000000 : ℝ)) (X := (50034912939256484933/50000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1778988556724511/12500000000000000000 : ℝ) ≤ ((13955230478178476737/13960000000000000000 : ℝ)+2*(509167478607/279200000000000 : ℝ)*(11289/100000 : ℝ))^(2079/512 : ℝ) := by
    rw [show (13955230478178476737/13960000000000000000 : ℝ)+2*(509167478607/279200000000000 : ℝ)*(11289/100000 : ℝ)=(1000070090963071/1000000000000000 : ℝ) by norm_num, show 1+2*(1778988556724511/12500000000000000000 : ℝ)=(6251778988556724511/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34912939256484933/100000000000000000000 : ℝ)+(1778988556724511/12500000000000000000 : ℝ) ≤ ((13955230478178476737/13960000000000000000 : ℝ)+(509167478607/279200000000000 : ℝ)*((14081/100000 : ℝ)+(11289/100000 : ℝ)))^(2079/512 : ℝ) := by
    rw [show (13955230478178476737/13960000000000000000 : ℝ)+(509167478607/279200000000000 : ℝ)*((14081/100000 : ℝ)+(11289/100000 : ℝ))=(10001210077109317/10000000000000000 : ℝ) by norm_num, show 1+(34912939256484933/100000000000000000000 : ℝ)+(1778988556724511/12500000000000000000 : ℝ)=(100049144847710281021/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34912939256484933/100000000000000000000 : ℝ) ≤ ((13955230478178476737/13960000000000000000 : ℝ)+2*(509167478607/279200000000000 : ℝ)*(14081/100000 : ℝ))^(2079/512 : ℝ) := by
    rw [show (13955230478178476737/13960000000000000000 : ℝ)+2*(509167478607/279200000000000 : ℝ)*(14081/100000 : ℝ)=(2500429811146981/2500000000000000 : ℝ) by norm_num, show 1+2*(34912939256484933/100000000000000000000 : ℝ)=(50034912939256484933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13955230478178476737/13960000000000000000 : ℝ)*(X 1 0+X 2 0)+(509167478607/279200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (11289/100000 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (13955230478178476737/13960000000000000000 : ℝ)) (alpha := (509167478607/279200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13955230478178476737/13960000000000000000 : ℝ)*(X 0 1+X 2 1)+(509167478607/279200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (11289/100000 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (13955230478178476737/13960000000000000000 : ℝ)) (alpha := (509167478607/279200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13955230478178476737/13960000000000000000 : ℝ)*(X 0 2+X 1 2)+(509167478607/279200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (11289/100000 : ℝ)) (hi := (14081/100000 : ℝ)) (c := (13955230478178476737/13960000000000000000 : ℝ)) (alpha := (509167478607/279200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-21754903/100000000 : ℝ)*X 0 0+(215749517/400000000 : ℝ)*X 0 1+(5265085731/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672458441/5000000000 : ℝ)*X 1 0+(-2240754891/10000000000 : ℝ)*X 1 1+(164533929/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534491687/1000000000 : ℝ)*X 2 0+(2632542871/5000000000 : ℝ)*X 2 1+(-280094361/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183598133/5000000000 : ℝ)*X 0 0+(1060383343/2500000000 : ℝ)*X 0 1+(2248290111/5000000000 : ℝ)*X 0 2+(2183598133/5000000000 : ℝ)*X 1 0+(1060383343/2500000000 : ℝ)*X 1 1+(2248290111/5000000000 : ℝ)*X 1 2+(2183598133/5000000000 : ℝ)*X 2 0+(1060383343/2500000000 : ℝ)*X 2 1+(2248290111/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2175495447/10000000000 : ℝ)*X 0 0+(2632705247/5000000000 : ℝ)*X 0 1+(5393411881/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656183067/5000000000 : ℝ)*X 1 0+(-1056214369/5000000000 : ℝ)*X 1 1+(539341187/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312366199/10000000000 : ℝ)*X 2 0+(2696705857/5000000000 : ℝ)*X 2 1+(-2112428863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4367206197/10000000000 : ℝ)*X 0 0+(2247968081/5000000000 : ℝ)*X 0 1+(4242179779/10000000000 : ℝ)*X 0 2+(4367206197/10000000000 : ℝ)*X 1 0+(2247968081/5000000000 : ℝ)*X 1 1+(4242179779/10000000000 : ℝ)*X 1 2+(4367206197/10000000000 : ℝ)*X 2 0+(2247968081/5000000000 : ℝ)*X 2 1+(4242179779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10227052637087541583569/2792000000000000000000000000 : ℝ) := by norm_num
    linear_combination (401325841/50000000000000 : ℝ)*(base19) + (89241113/12500000000000 : ℝ)*(base23) + (38094059/100000000000000 : ℝ)*(lower2) + (100115211/100000000000000 : ℝ)*(upper3) + (48466983/100000000000000 : ℝ)*(upper5) + (46775242087709/800000000000 : ℝ)*(major0) + (46775242087709/800000000000 : ℝ)*(major1) + (46775242087709/800000000000 : ℝ)*(major2) + (1554583630651837/20000000000000 : ℝ)*(sp0) + (48580868644449/625000000000 : ℝ)*(sp1) + (3886469535917309/50000000000000 : ℝ)*(sp2) + (980214685585943/25000000000000 : ℝ)*(sp3) + (21632504337/100000000000000 : ℝ)*(sp4) + (11871720467/100000000000000 : ℝ)*(sp7) + (3920870614064239/100000000000000 : ℝ)*(f.failure) + (3886469892881761/50000000000000 : ℝ)*(f.sum) + (6596596217829/2792000000000000000000000000 : ℝ)*base66 + (23980135606812467/11168000000000000000000000000000 : ℝ)*base68 + (8713936020636467/11168000000000000000000000000000 : ℝ)*base70 + (150124720562467533/11168000000000000000000000000000 : ℝ)*base71 + (13015256761141/2792000000000000000000000000 : ℝ)*base74 + (228451918910179533/11168000000000000000000000000000 : ℝ)*base75 + (18379434644572467/11168000000000000000000000000000 : ℝ)*base78 + (32033940534083533/11168000000000000000000000000000 : ℝ)*base79 + (5295729044819/2792000000000000000000000000 : ℝ)*base81 + (33564147/10000000000000000000000 : ℝ)*base90 + (33564147/10000000000000000000000 : ℝ)*base92 + (33564147/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1030328395517420578035416517/139600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1773459591/100000000000000 : ℝ)*(base19) + (1892910659/100000000000000 : ℝ)*(base23) + (10586973/25000000000000 : ℝ)*(upper2) + (149656341/100000000000000 : ℝ)*(upper3) + (252915269/100000000000000 : ℝ)*(upper5) + (1175320499876451/20000000000000 : ℝ)*(major0) + (1175320499876451/20000000000000 : ℝ)*(major1) + (1175320499876451/20000000000000 : ℝ)*(major2) + (51330911919/100000000000000 : ℝ)*(sp1) + (844309059/2000000000000 : ℝ)*(sp2) + (7812419495936319/100000000000000 : ℝ)*(sp4) + (7812366391564809/100000000000000 : ℝ)*(sp5) + (781237538757271/10000000000000 : ℝ)*(sp6) + (788157051361797/20000000000000 : ℝ)*(sp7) + (788157051361797/20000000000000 : ℝ)*(f.failure) + (7812419495936319/100000000000000 : ℝ)*(f.sum) + (10221660958227/2792000000000000000000000000 : ℝ)*base66 + (3027677049110270387/279200000000000000000000000000000 : ℝ)*base67 + (1422675412228670387/279200000000000000000000000000000 : ℝ)*base69 + (700788552552670387/279200000000000000000000000000000 : ℝ)*base71 + (5549662863851/2792000000000000000000000000 : ℝ)*base74 + (5729930436847070387/279200000000000000000000000000000 : ℝ)*base75 + (1401803681933470387/279200000000000000000000000000000 : ℝ)*base77 + (8935763403793470387/279200000000000000000000000000000 : ℝ)*base79 + (6089572246363/2792000000000000000000000000 : ℝ)*base82 + (3919281/2000000000000000000000 : ℝ)*base90 + (3919281/2000000000000000000000 : ℝ)*base92 + (3919281/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1124_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11289/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1124_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1124_s7_0 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2175518593/10000000000 : ℝ)*x 0 + (5393391891/10000000000 : ℝ)*x 1 + (5265413301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175518593/10000000000 : ℝ)^8317 ≤ (6608810006713/50000000000000 : ℝ)^6269 := by
    have hnat : (2175518593 : ℕ)^8317*50000000000000^6269 ≤ 6608810006713^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175518593 10000000000 6608810006713 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393391891/10000000000 : ℝ)^8317 ≤ (1377573652391/3125000000000 : ℝ)^6269 := by
    have hnat : (5393391891 : ℕ)^8317*3125000000000^6269 ≤ 1377573652391^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393391891 10000000000 1377573652391 3125000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265413301/10000000000 : ℝ)^8317 ≤ (42700023096571/100000000000000 : ℝ)^6269 := by
    have hnat : (5265413301 : ℕ)^8317*100000000000000^6269 ≤ 42700023096571^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265413301 10000000000 42700023096571 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2175518593/10000000000 : ℝ), (5393391891/10000000000 : ℝ), (5265413301/10000000000 : ℝ)] ![(6608810006713/50000000000000 : ℝ), (1377573652391/3125000000000 : ℝ), (42700023096571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2175518593/10000000000 : ℝ)|^8317 ≤ (6608810006713/50000000000000 : ℝ)^6269
        have hw : |(-2175518593/10000000000 : ℝ)|=(2175518593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393391891/10000000000 : ℝ)|^8317 ≤ (1377573652391/3125000000000 : ℝ)^6269
        have hw : |(5393391891/10000000000 : ℝ)|=(5393391891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265413301/10000000000 : ℝ)|^8317 ≤ (42700023096571/100000000000000 : ℝ)^6269
        have hw : |(5265413301/10000000000 : ℝ)|=(5265413301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s7_1 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668103813/1250000000 : ℝ)*x 0 + (-1120218323/5000000000 : ℝ)*x 1 + (1316353317/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668103813/1250000000 : ℝ)^8317 ≤ (8711311068703/20000000000000 : ℝ)^6269 := by
    have hnat : (668103813 : ℕ)^8317*20000000000000^6269 ≤ 8711311068703^6269*1250000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668103813 1250000000 8711311068703 20000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120218323/5000000000 : ℝ)^8317 ≤ (13743421907933/100000000000000 : ℝ)^6269 := by
    have hnat : (1120218323 : ℕ)^8317*100000000000000^6269 ≤ 13743421907933^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120218323 5000000000 13743421907933 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316353317/2500000000 : ℝ)^8317 ≤ (42700022741531/100000000000000 : ℝ)^6269 := by
    have hnat : (1316353317 : ℕ)^8317*100000000000000^6269 ≤ 42700022741531^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316353317 2500000000 42700022741531 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668103813/1250000000 : ℝ), (-1120218323/5000000000 : ℝ), (1316353317/2500000000 : ℝ)] ![(8711311068703/20000000000000 : ℝ), (13743421907933/100000000000000 : ℝ), (42700022741531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668103813/1250000000 : ℝ)|^8317 ≤ (8711311068703/20000000000000 : ℝ)^6269
        have hw : |(668103813/1250000000 : ℝ)|=(668103813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1120218323/5000000000 : ℝ)|^8317 ≤ (13743421907933/100000000000000 : ℝ)^6269
        have hw : |(-1120218323/5000000000 : ℝ)|=(1120218323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316353317/2500000000 : ℝ)|^8317 ≤ (42700022741531/100000000000000 : ℝ)^6269
        have hw : |(1316353317/2500000000 : ℝ)|=(1316353317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s7_2 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672415251/5000000000 : ℝ)*x 0 + (1053082653/2000000000 : ℝ)*x 1 + (-560109163/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672415251/5000000000 : ℝ)^8317 ≤ (10889138830473/25000000000000 : ℝ)^6269 := by
    have hnat : (2672415251 : ℕ)^8317*25000000000000^6269 ≤ 10889138830473^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672415251 5000000000 10889138830473 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053082653/2000000000 : ℝ)^8317 ≤ (21350011354627/50000000000000 : ℝ)^6269 := by
    have hnat : (1053082653 : ℕ)^8317*50000000000000^6269 ≤ 21350011354627^6269*2000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053082653 2000000000 21350011354627 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560109163/2500000000 : ℝ)^8317 ≤ (13743421956763/100000000000000 : ℝ)^6269 := by
    have hnat : (560109163 : ℕ)^8317*100000000000000^6269 ≤ 13743421956763^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560109163 2500000000 13743421956763 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672415251/5000000000 : ℝ), (1053082653/2000000000 : ℝ), (-560109163/2500000000 : ℝ)] ![(10889138830473/25000000000000 : ℝ), (21350011354627/50000000000000 : ℝ), (13743421956763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672415251/5000000000 : ℝ)|^8317 ≤ (10889138830473/25000000000000 : ℝ)^6269
        have hw : |(2672415251/5000000000 : ℝ)|=(2672415251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053082653/2000000000 : ℝ)|^8317 ≤ (21350011354627/50000000000000 : ℝ)^6269
        have hw : |(1053082653/2000000000 : ℝ)|=(1053082653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-560109163/2500000000 : ℝ)|^8317 ≤ (13743421956763/100000000000000 : ℝ)^6269
        have hw : |(-560109163/2500000000 : ℝ)|=(560109163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s7_3 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2183606713/5000000000 : ℝ)*x 0 + (1060549689/2500000000 : ℝ)*x 1 + (224795519/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183606713/5000000000 : ℝ)^8317 ≤ (16658424584833/50000000000000 : ℝ)^6269 := by
    have hnat : (2183606713 : ℕ)^8317*50000000000000^6269 ≤ 16658424584833^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183606713 5000000000 16658424584833 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060549689/2500000000 : ℝ)^8317 ≤ (8014379319351/25000000000000 : ℝ)^6269 := by
    have hnat : (1060549689 : ℕ)^8317*25000000000000^6269 ≤ 8014379319351^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060549689 2500000000 8014379319351 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224795519/500000000 : ℝ)^8317 ≤ (34625633527643/100000000000000 : ℝ)^6269 := by
    have hnat : (224795519 : ℕ)^8317*100000000000000^6269 ≤ 34625633527643^6269*500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224795519 500000000 34625633527643 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183606713/5000000000 : ℝ), (1060549689/2500000000 : ℝ), (224795519/500000000 : ℝ)] ![(16658424584833/50000000000000 : ℝ), (8014379319351/25000000000000 : ℝ), (34625633527643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183606713/5000000000 : ℝ)|^8317 ≤ (16658424584833/50000000000000 : ℝ)^6269
        have hw : |(2183606713/5000000000 : ℝ)|=(2183606713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060549689/2500000000 : ℝ)|^8317 ≤ (8014379319351/25000000000000 : ℝ)^6269
        have hw : |(1060549689/2500000000 : ℝ)|=(1060549689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224795519/500000000 : ℝ)|^8317 ≤ (34625633527643/100000000000000 : ℝ)^6269
        have hw : |(224795519/500000000 : ℝ)|=(224795519/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s7_4 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-54388089/250000000 : ℝ)*x 0 + (2632867381/5000000000 : ℝ)*x 1 + (1348267311/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54388089/250000000 : ℝ)^8317 ≤ (660883002483/5000000000000 : ℝ)^6269 := by
    have hnat : (54388089 : ℕ)^8317*5000000000000^6269 ≤ 660883002483^6269*250000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54388089 250000000 660883002483 5000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632867381/5000000000 : ℝ)^8317 ≤ (42703481667587/100000000000000 : ℝ)^6269 := by
    have hnat : (2632867381 : ℕ)^8317*100000000000000^6269 ≤ 42703481667587^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632867381 5000000000 42703481667587 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348267311/2500000000 : ℝ)^8317 ≤ (44078858273647/100000000000000 : ℝ)^6269 := by
    have hnat : (1348267311 : ℕ)^8317*100000000000000^6269 ≤ 44078858273647^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348267311 2500000000 44078858273647 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-54388089/250000000 : ℝ), (2632867381/5000000000 : ℝ), (1348267311/2500000000 : ℝ)] ![(660883002483/5000000000000 : ℝ), (42703481667587/100000000000000 : ℝ), (44078858273647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-54388089/250000000 : ℝ)|^8317 ≤ (660883002483/5000000000000 : ℝ)^6269
        have hw : |(-54388089/250000000 : ℝ)|=(54388089/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632867381/5000000000 : ℝ)|^8317 ≤ (42703481667587/100000000000000 : ℝ)^6269
        have hw : |(2632867381/5000000000 : ℝ)|=(2632867381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348267311/2500000000 : ℝ)|^8317 ≤ (44078858273647/100000000000000 : ℝ)^6269
        have hw : |(1348267311/2500000000 : ℝ)|=(1348267311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s7_5 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312450053/10000000000 : ℝ)*x 0 + (-1056390341/5000000000 : ℝ)*x 1 + (1348267311/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312450053/10000000000 : ℝ)^8317 ≤ (21603409668791/50000000000000 : ℝ)^6269 := by
    have hnat : (5312450053 : ℕ)^8317*50000000000000^6269 ≤ 21603409668791^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312450053 10000000000 21603409668791 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056390341/5000000000 : ℝ)^8317 ≤ (3178580593047/25000000000000 : ℝ)^6269 := by
    have hnat : (1056390341 : ℕ)^8317*25000000000000^6269 ≤ 3178580593047^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056390341 5000000000 3178580593047 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348267311/2500000000 : ℝ)^8317 ≤ (44078858273647/100000000000000 : ℝ)^6269 := by
    have hnat : (1348267311 : ℕ)^8317*100000000000000^6269 ≤ 44078858273647^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348267311 2500000000 44078858273647 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312450053/10000000000 : ℝ), (-1056390341/5000000000 : ℝ), (1348267311/2500000000 : ℝ)] ![(21603409668791/50000000000000 : ℝ), (3178580593047/25000000000000 : ℝ), (44078858273647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312450053/10000000000 : ℝ)|^8317 ≤ (21603409668791/50000000000000 : ℝ)^6269
        have hw : |(5312450053/10000000000 : ℝ)|=(5312450053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1056390341/5000000000 : ℝ)|^8317 ≤ (3178580593047/25000000000000 : ℝ)^6269
        have hw : |(-1056390341/5000000000 : ℝ)|=(1056390341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348267311/2500000000 : ℝ)|^8317 ≤ (44078858273647/100000000000000 : ℝ)^6269
        have hw : |(1348267311/2500000000 : ℝ)|=(1348267311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s7_6 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312450053/10000000000 : ℝ)*x 0 + (1348267311/2500000000 : ℝ)*x 1 + (-1056390341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312450053/10000000000 : ℝ)^8317 ≤ (21603409668791/50000000000000 : ℝ)^6269 := by
    have hnat : (5312450053 : ℕ)^8317*50000000000000^6269 ≤ 21603409668791^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312450053 10000000000 21603409668791 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348267311/2500000000 : ℝ)^8317 ≤ (44078858273647/100000000000000 : ℝ)^6269 := by
    have hnat : (1348267311 : ℕ)^8317*100000000000000^6269 ≤ 44078858273647^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348267311 2500000000 44078858273647 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056390341/5000000000 : ℝ)^8317 ≤ (3178580593047/25000000000000 : ℝ)^6269 := by
    have hnat : (1056390341 : ℕ)^8317*25000000000000^6269 ≤ 3178580593047^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056390341 5000000000 3178580593047 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312450053/10000000000 : ℝ), (1348267311/2500000000 : ℝ), (-1056390341/5000000000 : ℝ)] ![(21603409668791/50000000000000 : ℝ), (44078858273647/100000000000000 : ℝ), (3178580593047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312450053/10000000000 : ℝ)|^8317 ≤ (21603409668791/50000000000000 : ℝ)^6269
        have hw : |(5312450053/10000000000 : ℝ)|=(5312450053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348267311/2500000000 : ℝ)|^8317 ≤ (44078858273647/100000000000000 : ℝ)^6269
        have hw : |(1348267311/2500000000 : ℝ)|=(1348267311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1056390341/5000000000 : ℝ)|^8317 ≤ (3178580593047/25000000000000 : ℝ)^6269
        have hw : |(-1056390341/5000000000 : ℝ)|=(1056390341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s7_7 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1091805803/2500000000 : ℝ)*x 0 + (4495273003/10000000000 : ℝ)*x 1 + (2121419217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091805803/2500000000 : ℝ)^8317 ≤ (33316948214837/100000000000000 : ℝ)^6269 := by
    have hnat : (1091805803 : ℕ)^8317*100000000000000^6269 ≤ 33316948214837^6269*2500000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091805803 2500000000 33316948214837 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4495273003/10000000000 : ℝ)^8317 ≤ (17309560610479/50000000000000 : ℝ)^6269 := by
    have hnat : (4495273003 : ℕ)^8317*50000000000000^6269 ≤ 17309560610479^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495273003 10000000000 17309560610479 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121419217/5000000000 : ℝ)^8317 ≤ (8015982636449/25000000000000 : ℝ)^6269 := by
    have hnat : (2121419217 : ℕ)^8317*25000000000000^6269 ≤ 8015982636449^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121419217 5000000000 8015982636449 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091805803/2500000000 : ℝ), (4495273003/10000000000 : ℝ), (2121419217/5000000000 : ℝ)] ![(33316948214837/100000000000000 : ℝ), (17309560610479/50000000000000 : ℝ), (8015982636449/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091805803/2500000000 : ℝ)|^8317 ≤ (33316948214837/100000000000000 : ℝ)^6269
        have hw : |(1091805803/2500000000 : ℝ)|=(1091805803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4495273003/10000000000 : ℝ)|^8317 ≤ (17309560610479/50000000000000 : ℝ)^6269
        have hw : |(4495273003/10000000000 : ℝ)|=(4495273003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2121419217/5000000000 : ℝ)|^8317 ≤ (8015982636449/25000000000000 : ℝ)^6269
        have hw : |(2121419217/5000000000 : ℝ)|=(2121419217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1124_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11329/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (351/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14047/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5661/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14047/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5661/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14047/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5661/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14047/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5661/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14047/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5661/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14047/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5661/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (5661/50000 : ℝ) ^ (2079/512 : ℝ) ≤ (14401595393722229/100000000000000000000 : ℝ) := by
    have hpowers : (5661/50000 : ℝ)^2079 ≤ (14401595393722229/100000000000000000000 : ℝ)^512 := by
      have hnat : (5661 : ℕ)^2079*100000000000000000000^512 ≤ 14401595393722229^512*50000^2079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5661 50000 14401595393722229 100000000000000000000 2079 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5661/50000 : ℝ)) (X := (14401595393722229/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14047/100000 : ℝ) ^ (2079/512 : ℝ) ≤ (6914378905916019/20000000000000000000 : ℝ) := by
    have hpowers : (14047/100000 : ℝ)^2079 ≤ (6914378905916019/20000000000000000000 : ℝ)^512 := by
      have hnat : (14047 : ℕ)^2079*20000000000000000000^512 ≤ 6914378905916019^512*100000^2079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14047 100000 6914378905916019 20000000000000000000 2079 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14047/100000 : ℝ)) (X := (6914378905916019/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014401595393722229/50000000000000000000 : ℝ) ≤ (10000709265664157/10000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (50014401595393722229/50000000000000000000 : ℝ)^512 ≤ (10000709265664157/10000000000000000 : ℝ)^2079 := by
      have hnat : (50014401595393722229 : ℕ)^512*10000000000000000^2079 ≤ 10000709265664157^2079*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014401595393722229 50000000000000000000 10000709265664157 10000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000709265664157/10000000000000000 : ℝ)) (X := (50014401595393722229/50000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012243372480825581/25000000000000000000 : ℝ) ≤ (12501507323253/12500000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (25012243372480825581/25000000000000000000 : ℝ)^512 ≤ (12501507323253/12500000000000 : ℝ)^2079 := by
      have hnat : (25012243372480825581 : ℕ)^512*12500000000000^2079 ≤ 12501507323253^2079*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012243372480825581 25000000000000000000 12501507323253 12500000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12501507323253/12500000000000 : ℝ)) (X := (25012243372480825581/25000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006914378905916019/10000000000000000000 : ℝ) ≤ (10001702451540643/10000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (10006914378905916019/10000000000000000000 : ℝ)^512 ≤ (10001702451540643/10000000000000000 : ℝ)^2079 := by
      have hnat : (10006914378905916019 : ℕ)^512*10000000000000000^2079 ≤ 10001702451540643^2079*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006914378905916019 10000000000000000000 10001702451540643 10000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001702451540643/10000000000000000 : ℝ)) (X := (10006914378905916019/10000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14401595393722229/100000000000000000000 : ℝ) ≤ ((27240687898441253333/27250000000000000000 : ℝ)+2*(496592938243/272500000000000 : ℝ)*(5661/50000 : ℝ))^(2079/512 : ℝ) := by
    rw [show (27240687898441253333/27250000000000000000 : ℝ)+2*(496592938243/272500000000000 : ℝ)*(5661/50000 : ℝ)=(10000709265664157/10000000000000000 : ℝ) by norm_num, show 1+2*(14401595393722229/100000000000000000000 : ℝ)=(50014401595393722229/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6914378905916019/20000000000000000000 : ℝ)+(14401595393722229/100000000000000000000 : ℝ) ≤ ((27240687898441253333/27250000000000000000 : ℝ)+(496592938243/272500000000000 : ℝ)*((14047/100000 : ℝ)+(5661/50000 : ℝ)))^(2079/512 : ℝ) := by
    rw [show (27240687898441253333/27250000000000000000 : ℝ)+(496592938243/272500000000000 : ℝ)*((14047/100000 : ℝ)+(5661/50000 : ℝ))=(12501507323253/12500000000000 : ℝ) by norm_num, show 1+(6914378905916019/20000000000000000000 : ℝ)+(14401595393722229/100000000000000000000 : ℝ)=(25012243372480825581/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6914378905916019/20000000000000000000 : ℝ) ≤ ((27240687898441253333/27250000000000000000 : ℝ)+2*(496592938243/272500000000000 : ℝ)*(14047/100000 : ℝ))^(2079/512 : ℝ) := by
    rw [show (27240687898441253333/27250000000000000000 : ℝ)+2*(496592938243/272500000000000 : ℝ)*(14047/100000 : ℝ)=(10001702451540643/10000000000000000 : ℝ) by norm_num, show 1+2*(6914378905916019/20000000000000000000 : ℝ)=(10006914378905916019/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27240687898441253333/27250000000000000000 : ℝ)*(X 1 0+X 2 0)+(496592938243/272500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (14047/100000 : ℝ)) (c := (27240687898441253333/27250000000000000000 : ℝ)) (alpha := (496592938243/272500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27240687898441253333/27250000000000000000 : ℝ)*(X 0 1+X 2 1)+(496592938243/272500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (14047/100000 : ℝ)) (c := (27240687898441253333/27250000000000000000 : ℝ)) (alpha := (496592938243/272500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27240687898441253333/27250000000000000000 : ℝ)*(X 0 2+X 1 2)+(496592938243/272500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (5661/50000 : ℝ)) (hi := (14047/100000 : ℝ)) (c := (27240687898441253333/27250000000000000000 : ℝ)) (alpha := (496592938243/272500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2175518593/10000000000 : ℝ)*X 0 0+(5393391891/10000000000 : ℝ)*X 0 1+(5265413301/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668103813/1250000000 : ℝ)*X 1 0+(-1120218323/5000000000 : ℝ)*X 1 1+(1316353317/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672415251/5000000000 : ℝ)*X 2 0+(1053082653/2000000000 : ℝ)*X 2 1+(-560109163/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2183606713/5000000000 : ℝ)*X 0 0+(1060549689/2500000000 : ℝ)*X 0 1+(224795519/500000000 : ℝ)*X 0 2+(2183606713/5000000000 : ℝ)*X 1 0+(1060549689/2500000000 : ℝ)*X 1 1+(224795519/500000000 : ℝ)*X 1 2+(2183606713/5000000000 : ℝ)*X 2 0+(1060549689/2500000000 : ℝ)*X 2 1+(224795519/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-54388089/250000000 : ℝ)*X 0 0+(2632867381/5000000000 : ℝ)*X 0 1+(1348267311/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312450053/10000000000 : ℝ)*X 1 0+(-1056390341/5000000000 : ℝ)*X 1 1+(1348267311/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312450053/10000000000 : ℝ)*X 2 0+(1348267311/2500000000 : ℝ)*X 2 1+(-1056390341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1091805803/2500000000 : ℝ)*X 0 0+(4495273003/10000000000 : ℝ)*X 0 1+(2121419217/5000000000 : ℝ)*X 0 2+(1091805803/2500000000 : ℝ)*X 1 0+(4495273003/10000000000 : ℝ)*X 1 1+(2121419217/5000000000 : ℝ)*X 1 2+(1091805803/2500000000 : ℝ)*X 2 0+(4495273003/10000000000 : ℝ)*X 2 1+(2121419217/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (396384580644924344499/109000000000000000000000000 : ℝ) := by norm_num
    linear_combination (358064789/50000000000000 : ℝ)*(base19) + (309406691/50000000000000 : ℝ)*(base23) + (5045109/10000000000000 : ℝ)*(lower2) + (5053137/5000000000000 : ℝ)*(upper3) + (1284699/6250000000000 : ℝ)*(upper5) + (47021383374421/800000000000 : ℝ)*(major0) + (47021383374421/800000000000 : ℝ)*(major1) + (47021383374421/800000000000 : ℝ)*(major2) + (19534565071229/250000000000 : ℝ)*(sp0) + (312553677435989/4000000000000 : ℝ)*(sp1) + (7813842033215921/100000000000000 : ℝ)*(sp2) + (1970745919070967/50000000000000 : ℝ)*(sp3) + (2077942213/12500000000000 : ℝ)*(sp4) + (11232215473/100000000000000 : ℝ)*(sp7) + (123171970948669/3125000000000 : ℝ)*(f.failure) + (976730331503663/12500000000000 : ℝ)*(f.sum) + (58040409223/109000000000000000000000000 : ℝ)*base65 + (257174015964304807/21800000000000000000000000000000 : ℝ)*base68 + (376281227883095193/21800000000000000000000000000000 : ℝ)*base69 + (418072948724504807/21800000000000000000000000000000 : ℝ)*base72 + (96286990223/54500000000000000000000000 : ℝ)*base73 + (288884942339895193/21800000000000000000000000000000 : ℝ)*base75 + (174950867260104807/21800000000000000000000000000000 : ℝ)*base78 + (281928865665095193/21800000000000000000000000000000 : ℝ)*base79 + (257021261913/109000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (308463/312500000000000000000 : ℝ)*base89 + (308463/312500000000000000000 : ℝ)*base91 + (308463/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14631252405300801046096926897/1362500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (985259477/50000000000000 : ℝ)*(base19) + (1071026289/50000000000000 : ℝ)*(base23) + (215718043/100000000000000 : ℝ)*(upper3) + (77969837/100000000000000 : ℝ)*(lower4) + (109430593/50000000000000 : ℝ)*(upper5) + (5907376299546897/100000000000000 : ℝ)*(major0) + (5907376299546897/100000000000000 : ℝ)*(major1) + (5907376299546897/100000000000000 : ℝ)*(major2) + (27107481307/50000000000000 : ℝ)*(sp1) + (58278079303/100000000000000 : ℝ)*(sp2) + (7853330411075979/100000000000000 : ℝ)*(sp4) + (785327422559441/10000000000000 : ℝ)*(sp5) + (245414687217003/3125000000000 : ℝ)*(sp6) + (247588864379167/6250000000000 : ℝ)*(sp7) + (247588864379167/6250000000000 : ℝ)*(f.failure) + (7853330411075979/100000000000000 : ℝ)*(f.sum) + (20903615395029/13625000000000000000000000000 : ℝ)*base66 + (4449635479261842299/2725000000000000000000000000000000 : ℝ)*base68 + (45307982955988157701/2725000000000000000000000000000000 : ℝ)*base69 + (25107134637361842299/2725000000000000000000000000000000 : ℝ)*base72 + (31660423839029/13625000000000000000000000000 : ℝ)*base74 + (119491206454888157701/2725000000000000000000000000000000 : ℝ)*base75 + (4658705240838157701/2725000000000000000000000000000000 : ℝ)*base77 + (74696202681013157701/2725000000000000000000000000000000 : ℝ)*base79 + (34093697165529/13625000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/50000000000000 : ℝ)*base88 + (861709/625000000000000000000 : ℝ)*base89 + (861709/625000000000000000000 : ℝ)*base91 + (861709/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1124_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11329/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (351/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1124_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1124_s8_0 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-87020951/400000000 : ℝ)*x 0 + (5393320789/10000000000 : ℝ)*x 1 + (5265481081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87020951/400000000 : ℝ)^8317 ≤ (103262982677/781250000000 : ℝ)^6269 := by
    have hnat : (87020951 : ℕ)^8317*781250000000^6269 ≤ 103262982677^6269*400000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87020951 400000000 103262982677 781250000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393320789/10000000000 : ℝ)^8317 ≤ (22040792940241/50000000000000 : ℝ)^6269 := by
    have hnat : (5393320789 : ℕ)^8317*50000000000000^6269 ≤ 22040792940241^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393320789 10000000000 22040792940241 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265481081/10000000000 : ℝ)^8317 ≤ (42700752329973/100000000000000 : ℝ)^6269 := by
    have hnat : (5265481081 : ℕ)^8317*100000000000000^6269 ≤ 42700752329973^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265481081 10000000000 42700752329973 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87020951/400000000 : ℝ), (5393320789/10000000000 : ℝ), (5265481081/10000000000 : ℝ)] ![(103262982677/781250000000 : ℝ), (22040792940241/50000000000000 : ℝ), (42700752329973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87020951/400000000 : ℝ)|^8317 ≤ (103262982677/781250000000 : ℝ)^6269
        have hw : |(-87020951/400000000 : ℝ)|=(87020951/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393320789/10000000000 : ℝ)|^8317 ≤ (22040792940241/50000000000000 : ℝ)^6269
        have hw : |(5393320789/10000000000 : ℝ)|=(5393320789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265481081/10000000000 : ℝ)|^8317 ≤ (42700752329973/100000000000000 : ℝ)^6269
        have hw : |(5265481081/10000000000 : ℝ)|=(5265481081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s8_1 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344812939/10000000000 : ℝ)*x 0 + (-2240370339/10000000000 : ℝ)*x 1 + (210619243/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344812939/10000000000 : ℝ)^8317 ≤ (8711273087743/20000000000000 : ℝ)^6269 := by
    have hnat : (5344812939 : ℕ)^8317*20000000000000^6269 ≤ 8711273087743^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344812939 10000000000 8711273087743 20000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2240370339/10000000000 : ℝ)^8317 ≤ (3435720572019/25000000000000 : ℝ)^6269 := by
    have hnat : (2240370339 : ℕ)^8317*25000000000000^6269 ≤ 3435720572019^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240370339 10000000000 3435720572019 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210619243/400000000 : ℝ)^8317 ≤ (2135037613271/5000000000000 : ℝ)^6269 := by
    have hnat : (210619243 : ℕ)^8317*5000000000000^6269 ≤ 2135037613271^6269*400000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210619243 400000000 2135037613271 5000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344812939/10000000000 : ℝ), (-2240370339/10000000000 : ℝ), (210619243/400000000 : ℝ)] ![(8711273087743/20000000000000 : ℝ), (3435720572019/25000000000000 : ℝ), (2135037613271/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344812939/10000000000 : ℝ)|^8317 ≤ (8711273087743/20000000000000 : ℝ)^6269
        have hw : |(5344812939/10000000000 : ℝ)|=(5344812939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2240370339/10000000000 : ℝ)|^8317 ≤ (3435720572019/25000000000000 : ℝ)^6269
        have hw : |(-2240370339/10000000000 : ℝ)|=(2240370339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210619243/400000000 : ℝ)|^8317 ≤ (2135037613271/5000000000000 : ℝ)^6269
        have hw : |(210619243/400000000 : ℝ)|=(210619243/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s8_2 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344812937/10000000000 : ℝ)*x 0 + (5265481079/10000000000 : ℝ)*x 1 + (-70011573/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344812937/10000000000 : ℝ)^8317 ≤ (10889091354273/25000000000000 : ℝ)^6269 := by
    have hnat : (5344812937 : ℕ)^8317*25000000000000^6269 ≤ 10889091354273^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344812937 10000000000 10889091354273 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265481079/10000000000 : ℝ)^8317 ≤ (5337594038557/12500000000000 : ℝ)^6269 := by
    have hnat : (5265481079 : ℕ)^8317*12500000000000^6269 ≤ 5337594038557^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265481079 10000000000 5337594038557 12500000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70011573/312500000 : ℝ)^8317 ≤ (6871441131831/50000000000000 : ℝ)^6269 := by
    have hnat : (70011573 : ℕ)^8317*50000000000000^6269 ≤ 6871441131831^6269*312500000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70011573 312500000 6871441131831 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344812937/10000000000 : ℝ), (5265481079/10000000000 : ℝ), (-70011573/312500000 : ℝ)] ![(10889091354273/25000000000000 : ℝ), (5337594038557/12500000000000 : ℝ), (6871441131831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344812937/10000000000 : ℝ)|^8317 ≤ (10889091354273/25000000000000 : ℝ)^6269
        have hw : |(5344812937/10000000000 : ℝ)|=(5344812937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265481079/10000000000 : ℝ)|^8317 ≤ (5337594038557/12500000000000 : ℝ)^6269
        have hw : |(5265481079/10000000000 : ℝ)|=(5265481079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-70011573/312500000 : ℝ)|^8317 ≤ (6871441131831/50000000000000 : ℝ)^6269
        have hw : |(-70011573/312500000 : ℝ)|=(70011573/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s8_3 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4367216959/10000000000 : ℝ)*x 0 + (4242336027/10000000000 : ℝ)*x 1 + (449577219/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4367216959/10000000000 : ℝ)^8317 ≤ (6663376985507/20000000000000 : ℝ)^6269 := by
    have hnat : (4367216959 : ℕ)^8317*20000000000000^6269 ≤ 6663376985507^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4367216959 10000000000 6663376985507 20000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4242336027/10000000000 : ℝ)^8317 ≤ (32058893499091/100000000000000 : ℝ)^6269 := by
    have hnat : (4242336027 : ℕ)^8317*100000000000000^6269 ≤ 32058893499091^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242336027 10000000000 32058893499091 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449577219/1000000000 : ℝ)^8317 ≤ (4328027695729/12500000000000 : ℝ)^6269 := by
    have hnat : (449577219 : ℕ)^8317*12500000000000^6269 ≤ 4328027695729^6269*1000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449577219 1000000000 4328027695729 12500000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4367216959/10000000000 : ℝ), (4242336027/10000000000 : ℝ), (449577219/1000000000 : ℝ)] ![(6663376985507/20000000000000 : ℝ), (32058893499091/100000000000000 : ℝ), (4328027695729/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4367216959/10000000000 : ℝ)|^8317 ≤ (6663376985507/20000000000000 : ℝ)^6269
        have hw : |(4367216959/10000000000 : ℝ)|=(4367216959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4242336027/10000000000 : ℝ)|^8317 ≤ (32058893499091/100000000000000 : ℝ)^6269
        have hw : |(4242336027/10000000000 : ℝ)|=(4242336027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449577219/1000000000 : ℝ)|^8317 ≤ (4328027695729/12500000000000 : ℝ)^6269
        have hw : |(449577219/1000000000 : ℝ)|=(449577219/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s8_4 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-217552869/1000000000 : ℝ)*x 0 + (5265801887/10000000000 : ℝ)*x 1 + (2696499413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217552869/1000000000 : ℝ)^8317 ≤ (13217701399777/100000000000000 : ℝ)^6269 := by
    have hnat : (217552869 : ℕ)^8317*100000000000000^6269 ≤ 13217701399777^6269*1000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217552869 1000000000 13217701399777 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265801887/10000000000 : ℝ)^8317 ≤ (8540840773669/20000000000000 : ℝ)^6269 := by
    have hnat : (5265801887 : ℕ)^8317*20000000000000^6269 ≤ 8540840773669^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265801887 10000000000 8540840773669 20000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696499413/5000000000 : ℝ)^8317 ≤ (44078094709493/100000000000000 : ℝ)^6269 := by
    have hnat : (2696499413 : ℕ)^8317*100000000000000^6269 ≤ 44078094709493^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696499413 5000000000 44078094709493 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-217552869/1000000000 : ℝ), (5265801887/10000000000 : ℝ), (2696499413/5000000000 : ℝ)] ![(13217701399777/100000000000000 : ℝ), (8540840773669/20000000000000 : ℝ), (44078094709493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-217552869/1000000000 : ℝ)|^8317 ≤ (13217701399777/100000000000000 : ℝ)^6269
        have hw : |(-217552869/1000000000 : ℝ)|=(217552869/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265801887/10000000000 : ℝ)|^8317 ≤ (8540840773669/20000000000000 : ℝ)^6269
        have hw : |(5265801887/10000000000 : ℝ)|=(5265801887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696499413/5000000000 : ℝ)|^8317 ≤ (44078094709493/100000000000000 : ℝ)^6269
        have hw : |(2696499413/5000000000 : ℝ)|=(2696499413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s8_5 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312467609/10000000000 : ℝ)*x 0 + (-2112852597/10000000000 : ℝ)*x 1 + (674124853/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312467609/10000000000 : ℝ)^8317 ≤ (21603504384427/50000000000000 : ℝ)^6269 := by
    have hnat : (5312467609 : ℕ)^8317*50000000000000^6269 ≤ 21603504384427^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312467609 10000000000 21603504384427 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112852597/10000000000 : ℝ)^8317 ≤ (12714896527163/100000000000000 : ℝ)^6269 := by
    have hnat : (2112852597 : ℕ)^8317*100000000000000^6269 ≤ 12714896527163^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112852597 10000000000 12714896527163 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674124853/1250000000 : ℝ)^8317 ≤ (22039047343903/50000000000000 : ℝ)^6269 := by
    have hnat : (674124853 : ℕ)^8317*50000000000000^6269 ≤ 22039047343903^6269*1250000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674124853 1250000000 22039047343903 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312467609/10000000000 : ℝ), (-2112852597/10000000000 : ℝ), (674124853/1250000000 : ℝ)] ![(21603504384427/50000000000000 : ℝ), (12714896527163/100000000000000 : ℝ), (22039047343903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312467609/10000000000 : ℝ)|^8317 ≤ (21603504384427/50000000000000 : ℝ)^6269
        have hw : |(5312467609/10000000000 : ℝ)|=(5312467609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2112852597/10000000000 : ℝ)|^8317 ≤ (12714896527163/100000000000000 : ℝ)^6269
        have hw : |(-2112852597/10000000000 : ℝ)|=(2112852597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674124853/1250000000 : ℝ)|^8317 ≤ (22039047343903/50000000000000 : ℝ)^6269
        have hw : |(674124853/1250000000 : ℝ)|=(674124853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s8_6 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664058453/1250000000 : ℝ)*x 0 + (5392998821/10000000000 : ℝ)*x 1 + (-2112852581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664058453/1250000000 : ℝ)^8317 ≤ (21603504465353/50000000000000 : ℝ)^6269 := by
    have hnat : (664058453 : ℕ)^8317*50000000000000^6269 ≤ 21603504465353^6269*1250000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664058453 1250000000 21603504465353 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392998821/10000000000 : ℝ)^8317 ≤ (11019523663819/25000000000000 : ℝ)^6269 := by
    have hnat : (5392998821 : ℕ)^8317*25000000000000^6269 ≤ 11019523663819^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392998821 10000000000 11019523663819 25000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112852581/10000000000 : ℝ)^8317 ≤ (6357448199711/50000000000000 : ℝ)^6269 := by
    have hnat : (2112852581 : ℕ)^8317*50000000000000^6269 ≤ 6357448199711^6269*10000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112852581 10000000000 6357448199711 50000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664058453/1250000000 : ℝ), (5392998821/10000000000 : ℝ), (-2112852581/10000000000 : ℝ)] ![(21603504465353/50000000000000 : ℝ), (11019523663819/25000000000000 : ℝ), (6357448199711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664058453/1250000000 : ℝ)|^8317 ≤ (21603504465353/50000000000000 : ℝ)^6269
        have hw : |(664058453/1250000000 : ℝ)|=(664058453/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392998821/10000000000 : ℝ)|^8317 ≤ (11019523663819/25000000000000 : ℝ)^6269
        have hw : |(5392998821/10000000000 : ℝ)|=(5392998821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2112852581/10000000000 : ℝ)|^8317 ≤ (6357448199711/50000000000000 : ℝ)^6269
        have hw : |(-2112852581/10000000000 : ℝ)|=(2112852581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1124_s8_7 (p : ℝ) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2183613359/5000000000 : ℝ)*x 0 + (899027241/2000000000 : ℝ)*x 1 + (2121487149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183613359/5000000000 : ℝ)^8317 ≤ (33316983699463/100000000000000 : ℝ)^6269 := by
    have hnat : (2183613359 : ℕ)^8317*100000000000000^6269 ≤ 33316983699463^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183613359 5000000000 33316983699463 100000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899027241/2000000000 : ℝ)^8317 ≤ (3461772354663/10000000000000 : ℝ)^6269 := by
    have hnat : (899027241 : ℕ)^8317*10000000000000^6269 ≤ 3461772354663^6269*2000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899027241 2000000000 3461772354663 10000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121487149/5000000000 : ℝ)^8317 ≤ (3206529272851/10000000000000 : ℝ)^6269 := by
    have hnat : (2121487149 : ℕ)^8317*10000000000000^6269 ≤ 3206529272851^6269*5000000000^8317 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121487149 5000000000 3206529272851 10000000000000 8317 6269 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8317/2048 : ℝ)) 8317 6269 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183613359/5000000000 : ℝ), (899027241/2000000000 : ℝ), (2121487149/5000000000 : ℝ)] ![(33316983699463/100000000000000 : ℝ), (3461772354663/10000000000000 : ℝ), (3206529272851/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183613359/5000000000 : ℝ)|^8317 ≤ (33316983699463/100000000000000 : ℝ)^6269
        have hw : |(2183613359/5000000000 : ℝ)|=(2183613359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899027241/2000000000 : ℝ)|^8317 ≤ (3461772354663/10000000000000 : ℝ)^6269
        have hw : |(899027241/2000000000 : ℝ)|=(899027241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2121487149/5000000000 : ℝ)|^8317 ≤ (3206529272851/10000000000000 : ℝ)^6269
        have hw : |(2121487149/5000000000 : ℝ)|=(2121487149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1124_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (351/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11329/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1133/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7019/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (351/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11329/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (351/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11329/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (351/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11329/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (351/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11329/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (351/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11329/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (351/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11329/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (11329/100000 : ℝ) ^ (2079/512 : ℝ) ≤ (2887556950629621/20000000000000000000 : ℝ) := by
    have hpowers : (11329/100000 : ℝ)^2079 ≤ (2887556950629621/20000000000000000000 : ℝ)^512 := by
      have hnat : (11329 : ℕ)^2079*20000000000000000000^512 ≤ 2887556950629621^512*100000^2079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11329 100000 2887556950629621 20000000000000000000 2079 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11329/100000 : ℝ)) (X := (2887556950629621/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hpowhi : (351/2500 : ℝ) ^ (2079/512 : ℝ) ≤ (34501992309412453/100000000000000000000 : ℝ) := by
    have hpowers : (351/2500 : ℝ)^2079 ≤ (34501992309412453/100000000000000000000 : ℝ)^512 := by
      have hnat : (351 : ℕ)^2079*100000000000000000000^512 ≤ 34501992309412453^512*2500^2079 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        351 2500 34501992309412453 100000000000000000000 2079 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (351/2500 : ℝ)) (X := (34501992309412453/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002887556950629621/10000000000000000000 : ℝ) ≤ (10000711047763763/10000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (10002887556950629621/10000000000000000000 : ℝ)^512 ≤ (10000711047763763/10000000000000000 : ℝ)^2079 := by
      have hnat : (10002887556950629621 : ℕ)^512*10000000000000000^2079 ≤ 10000711047763763^2079*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002887556950629621 10000000000000000000 10000711047763763 10000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000711047763763/10000000000000000 : ℝ)) (X := (10002887556950629621/10000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024469888531280279/50000000000000000000 : ℝ) ≤ (5000602514327219/5000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (50024469888531280279/50000000000000000000 : ℝ)^512 ≤ (5000602514327219/5000000000000000 : ℝ)^2079 := by
      have hnat : (50024469888531280279 : ℕ)^512*5000000000000000^2079 ≤ 5000602514327219^2079*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024469888531280279 50000000000000000000 5000602514327219 5000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000602514327219/5000000000000000 : ℝ)) (X := (50024469888531280279/50000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034501992309412453/50000000000000000000 : ℝ) ≤ (10001699009545113/10000000000000000 : ℝ) ^ (2079/512 : ℝ) := by
    have hpowers : (50034501992309412453/50000000000000000000 : ℝ)^512 ≤ (10001699009545113/10000000000000000 : ℝ)^2079 := by
      have hnat : (50034501992309412453 : ℕ)^512*10000000000000000^2079 ≤ 10001699009545113^2079*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034501992309412453 50000000000000000000 10001699009545113 10000000000000000 512 2079 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001699009545113/10000000000000000 : ℝ)) (X := (50034501992309412453/50000000000000000000 : ℝ)) (by norm_num) 2079 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2887556950629621/20000000000000000000 : ℝ) ≤ ((27100735031466647343/27110000000000000000 : ℝ)+2*(19759235627/10844000000000 : ℝ)*(11329/100000 : ℝ))^(2079/512 : ℝ) := by
    rw [show (27100735031466647343/27110000000000000000 : ℝ)+2*(19759235627/10844000000000 : ℝ)*(11329/100000 : ℝ)=(10000711047763763/10000000000000000 : ℝ) by norm_num, show 1+2*(2887556950629621/20000000000000000000 : ℝ)=(10002887556950629621/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34501992309412453/100000000000000000000 : ℝ)+(2887556950629621/20000000000000000000 : ℝ) ≤ ((27100735031466647343/27110000000000000000 : ℝ)+(19759235627/10844000000000 : ℝ)*((351/2500 : ℝ)+(11329/100000 : ℝ)))^(2079/512 : ℝ) := by
    rw [show (27100735031466647343/27110000000000000000 : ℝ)+(19759235627/10844000000000 : ℝ)*((351/2500 : ℝ)+(11329/100000 : ℝ))=(5000602514327219/5000000000000000 : ℝ) by norm_num, show 1+(34501992309412453/100000000000000000000 : ℝ)+(2887556950629621/20000000000000000000 : ℝ)=(50024469888531280279/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34501992309412453/100000000000000000000 : ℝ) ≤ ((27100735031466647343/27110000000000000000 : ℝ)+2*(19759235627/10844000000000 : ℝ)*(351/2500 : ℝ))^(2079/512 : ℝ) := by
    rw [show (27100735031466647343/27110000000000000000 : ℝ)+2*(19759235627/10844000000000 : ℝ)*(351/2500 : ℝ)=(10001699009545113/10000000000000000 : ℝ) by norm_num, show 1+2*(34501992309412453/100000000000000000000 : ℝ)=(50034501992309412453/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27100735031466647343/27110000000000000000 : ℝ)*(X 1 0+X 2 0)+(19759235627/10844000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (11329/100000 : ℝ)) (hi := (351/2500 : ℝ)) (c := (27100735031466647343/27110000000000000000 : ℝ)) (alpha := (19759235627/10844000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27100735031466647343/27110000000000000000 : ℝ)*(X 0 1+X 2 1)+(19759235627/10844000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (11329/100000 : ℝ)) (hi := (351/2500 : ℝ)) (c := (27100735031466647343/27110000000000000000 : ℝ)) (alpha := (19759235627/10844000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27100735031466647343/27110000000000000000 : ℝ)*(X 0 2+X 1 2)+(19759235627/10844000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2079/512 : ℝ)) (lo := (11329/100000 : ℝ)) (hi := (351/2500 : ℝ)) (c := (27100735031466647343/27110000000000000000 : ℝ)) (alpha := (19759235627/10844000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-87020951/400000000 : ℝ)*X 0 0+(5393320789/10000000000 : ℝ)*X 0 1+(5265481081/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344812939/10000000000 : ℝ)*X 1 0+(-2240370339/10000000000 : ℝ)*X 1 1+(210619243/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344812937/10000000000 : ℝ)*X 2 0+(5265481079/10000000000 : ℝ)*X 2 1+(-70011573/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4367216959/10000000000 : ℝ)*X 0 0+(4242336027/10000000000 : ℝ)*X 0 1+(449577219/1000000000 : ℝ)*X 0 2+(4367216959/10000000000 : ℝ)*X 1 0+(4242336027/10000000000 : ℝ)*X 1 1+(449577219/1000000000 : ℝ)*X 1 2+(4367216959/10000000000 : ℝ)*X 2 0+(4242336027/10000000000 : ℝ)*X 2 1+(449577219/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-217552869/1000000000 : ℝ)*X 0 0+(5265801887/10000000000 : ℝ)*X 0 1+(2696499413/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312467609/10000000000 : ℝ)*X 1 0+(-2112852597/10000000000 : ℝ)*X 1 1+(674124853/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664058453/1250000000 : ℝ)*X 2 0+(5392998821/10000000000 : ℝ)*X 2 1+(-2112852581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2183613359/5000000000 : ℝ)*X 0 0+(899027241/2000000000 : ℝ)*X 0 1+(2121487149/5000000000 : ℝ)*X 0 2+(2183613359/5000000000 : ℝ)*X 1 0+(899027241/2000000000 : ℝ)*X 1 1+(2121487149/5000000000 : ℝ)*X 1 2+(2183613359/5000000000 : ℝ)*X 2 0+(899027241/2000000000 : ℝ)*X 2 1+(2121487149/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1124_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1306929071025954506772034893/169437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (762525999/50000000000000 : ℝ)*(base19) + (707371929/50000000000000 : ℝ)*(base23) + (28696581/50000000000000 : ℝ)*(lower2) + (192027911/100000000000000 : ℝ)*(upper3) + (465827/400000000000 : ℝ)*(upper5) + (735511862970117/12500000000000 : ℝ)*(major0) + (735511862970117/12500000000000 : ℝ)*(major1) + (735511862970117/12500000000000 : ℝ)*(major2) + (1955584693418363/25000000000000 : ℝ)*(sp0) + (7822378444253883/100000000000000 : ℝ)*(sp1) + (7822378554562023/100000000000000 : ℝ)*(sp2) + (1972893544255973/50000000000000 : ℝ)*(sp3) + (10298908107/25000000000000 : ℝ)*(sp4) + (11246296347/50000000000000 : ℝ)*(sp7) + (1541331867619/39062500000 : ℝ)*(f.failure) + (7822379969305881/100000000000000 : ℝ)*(f.sum) + (2501300266707/1355500000000000000000000000 : ℝ)*base65 + (1779640223920550869/338875000000000000000000000000000 : ℝ)*base68 + (2292866959042550869/338875000000000000000000000000000 : ℝ)*base70 + (489489627437324131/338875000000000000000000000000000 : ℝ)*base71 + (1682727755727/542200000000000000000000000 : ℝ)*base73 + (5858602250721925869/338875000000000000000000000000000 : ℝ)*base76 + (1560368713518074131/338875000000000000000000000000000 : ℝ)*base77 + (5557648329693425869/338875000000000000000000000000000 : ℝ)*base80 + (47908130953/84718750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (47387/3906250000000000000 : ℝ)*base90 + (47387/3906250000000000000 : ℝ)*base92 + (47387/3906250000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2005450976128747228611/338875000000000000000000000 : ℝ) := by norm_num
    linear_combination (1070832421/100000000000000 : ℝ)*(base19) + (151495011/12500000000000 : ℝ)*(base23) + (371676901/100000000000000 : ℝ)*(lower1) + (120083359/100000000000000 : ℝ)*(upper3) + (50425307/100000000000000 : ℝ)*(lower4) + (14831281/12500000000000 : ℝ)*(upper5) + (591374267787777/10000000000000 : ℝ)*(major0) + (591374267787777/10000000000000 : ℝ)*(major1) + (591374267787777/10000000000000 : ℝ)*(major2) + (3943579731/100000000000000 : ℝ)*(sp2) + (1965448526214863/25000000000000 : ℝ)*(sp4) + (7861793034027031/100000000000000 : ℝ)*(sp5) + (7861788949319633/100000000000000 : ℝ)*(sp6) + (991422763407623/25000000000000 : ℝ)*(sp7) + (991422763407623/25000000000000 : ℝ)*(f.failure) + (1965448526214863/25000000000000 : ℝ)*(f.sum) + (4578508181307/1355500000000000000000000000 : ℝ)*base65 + (17991661276230026511/271100000000000000000000000000000 : ℝ)*base67 + (6767318637552373489/271100000000000000000000000000000 : ℝ)*base70 + (34185501138573926511/271100000000000000000000000000000 : ℝ)*base71 + (8760109758967/2711000000000000000000000000 : ℝ)*base73 + (16157194678403573489/271100000000000000000000000000000 : ℝ)*base76 + (443879219007926511/271100000000000000000000000000000 : ℝ)*base77 + (5978506377799773489/271100000000000000000000000000000 : ℝ)*base80 + (7286838388447/2711000000000000000000000000 : ℝ)*base82 + (36414379/2500000000000000000000 : ℝ)*base90 + (36414379/2500000000000000000000 : ℝ)*base92 + (36414379/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1124_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (351/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11329/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7019/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1124_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1124_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11289/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7019/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1124_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1124_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1124_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2079/512 : ℝ) ≤ p) (hpb : p ≤ (8317/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149122627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14081/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11289/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1133/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7019/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1124_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

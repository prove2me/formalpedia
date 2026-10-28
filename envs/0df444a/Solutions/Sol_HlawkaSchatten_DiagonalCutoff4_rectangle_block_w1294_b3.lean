-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1294_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:27:34.905612+00:00
-- url     : https://prove2.me/submissions/d5ee4258-0c7a-4029-a45c-77013d1a6b60

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
theorem support_rectangle_w1294_box_0 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-23937641/125000000 : ℝ)*x 0 + (5391927903/10000000000 : ℝ)*x 1 + (5391927371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23937641/125000000 : ℝ)^2127 ≤ (11339649960129/100000000000000 : ℝ)^1615 := by
    have hnat : (23937641 : ℕ)^2127*100000000000000^1615 ≤ 11339649960129^1615*125000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23937641 125000000 11339649960129 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391927903/10000000000 : ℝ)^2127 ≤ (8866035579177/20000000000000 : ℝ)^1615 := by
    have hnat : (5391927903 : ℕ)^2127*20000000000000^1615 ≤ 8866035579177^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391927903 10000000000 8866035579177 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391927371/10000000000 : ℝ)^2127 ≤ (44330172135361/100000000000000 : ℝ)^1615 := by
    have hnat : (5391927371 : ℕ)^2127*100000000000000^1615 ≤ 44330172135361^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391927371 10000000000 44330172135361 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-23937641/125000000 : ℝ), (5391927903/10000000000 : ℝ), (5391927371/10000000000 : ℝ)] ![(11339649960129/100000000000000 : ℝ), (8866035579177/20000000000000 : ℝ), (44330172135361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-23937641/125000000 : ℝ)|^2127 ≤ (11339649960129/100000000000000 : ℝ)^1615
        have hw : |(-23937641/125000000 : ℝ)|=(23937641/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391927903/10000000000 : ℝ)|^2127 ≤ (8866035579177/20000000000000 : ℝ)^1615
        have hw : |(5391927903/10000000000 : ℝ)|=(5391927903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391927371/10000000000 : ℝ)|^2127 ≤ (44330172135361/100000000000000 : ℝ)^1615
        have hw : |(5391927371/10000000000 : ℝ)|=(5391927371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_box_1 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1321101417/2500000000 : ℝ)*x 0 + (-2062065133/10000000000 : ℝ)*x 1 + (1078385559/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321101417/2500000000 : ℝ)^2127 ≤ (43169618508153/100000000000000 : ℝ)^1615 := by
    have hnat : (1321101417 : ℕ)^2127*100000000000000^1615 ≤ 43169618508153^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321101417 2500000000 43169618508153 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062065133/10000000000 : ℝ)^2127 ≤ (6250102378113/50000000000000 : ℝ)^1615 := by
    have hnat : (2062065133 : ℕ)^2127*50000000000000^1615 ≤ 6250102378113^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062065133 10000000000 6250102378113 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078385559/2000000000 : ℝ)^2127 ≤ (8866035345291/20000000000000 : ℝ)^1615 := by
    have hnat : (1078385559 : ℕ)^2127*20000000000000^1615 ≤ 8866035345291^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078385559 2000000000 8866035345291 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321101417/2500000000 : ℝ), (-2062065133/10000000000 : ℝ), (1078385559/2000000000 : ℝ)] ![(43169618508153/100000000000000 : ℝ), (6250102378113/50000000000000 : ℝ), (8866035345291/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321101417/2500000000 : ℝ)|^2127 ≤ (43169618508153/100000000000000 : ℝ)^1615
        have hw : |(1321101417/2500000000 : ℝ)|=(1321101417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2062065133/10000000000 : ℝ)|^2127 ≤ (6250102378113/50000000000000 : ℝ)^1615
        have hw : |(-2062065133/10000000000 : ℝ)|=(2062065133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078385559/2000000000 : ℝ)|^2127 ≤ (8866035345291/20000000000000 : ℝ)^1615
        have hw : |(1078385559/2000000000 : ℝ)|=(1078385559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_box_2 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2642203009/5000000000 : ℝ)*x 0 + (673990961/1250000000 : ℝ)*x 1 + (-412412961/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642203009/5000000000 : ℝ)^2127 ≤ (5396202784231/12500000000000 : ℝ)^1615 := by
    have hnat : (2642203009 : ℕ)^2127*12500000000000^1615 ≤ 5396202784231^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642203009 5000000000 5396202784231 12500000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673990961/1250000000 : ℝ)^2127 ≤ (22165087783927/50000000000000 : ℝ)^1615 := by
    have hnat : (673990961 : ℕ)^2127*50000000000000^1615 ≤ 22165087783927^1615*1250000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673990961 1250000000 22165087783927 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (412412961/2000000000 : ℝ)^2127 ≤ (12500202137539/100000000000000 : ℝ)^1615 := by
    have hnat : (412412961 : ℕ)^2127*100000000000000^1615 ≤ 12500202137539^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412412961 2000000000 12500202137539 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642203009/5000000000 : ℝ), (673990961/1250000000 : ℝ), (-412412961/2000000000 : ℝ)] ![(5396202784231/12500000000000 : ℝ), (22165087783927/50000000000000 : ℝ), (12500202137539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642203009/5000000000 : ℝ)|^2127 ≤ (5396202784231/12500000000000 : ℝ)^1615
        have hw : |(2642203009/5000000000 : ℝ)|=(2642203009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673990961/1250000000 : ℝ)|^2127 ≤ (22165087783927/50000000000000 : ℝ)^1615
        have hw : |(673990961/1250000000 : ℝ)|=(673990961/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-412412961/2000000000 : ℝ)|^2127 ≤ (12500202137539/100000000000000 : ℝ)^1615
        have hw : |(-412412961/2000000000 : ℝ)|=(412412961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_box_3 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (448869981/1000000000 : ℝ)*x 0 + (2134323843/5000000000 : ℝ)*x 1 + (4268647887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448869981/1000000000 : ℝ)^2127 ≤ (34820346387483/100000000000000 : ℝ)^1615 := by
    have hnat : (448869981 : ℕ)^2127*100000000000000^1615 ≤ 34820346387483^1615*1000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448869981 1000000000 34820346387483 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2134323843/5000000000 : ℝ)^2127 ≤ (32589825791869/100000000000000 : ℝ)^1615 := by
    have hnat : (2134323843 : ℕ)^2127*100000000000000^1615 ≤ 32589825791869^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134323843 5000000000 32589825791869 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4268647887/10000000000 : ℝ)^2127 ≤ (6517965562589/20000000000000 : ℝ)^1615 := by
    have hnat : (4268647887 : ℕ)^2127*20000000000000^1615 ≤ 6517965562589^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268647887 10000000000 6517965562589 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(448869981/1000000000 : ℝ), (2134323843/5000000000 : ℝ), (4268647887/10000000000 : ℝ)] ![(34820346387483/100000000000000 : ℝ), (32589825791869/100000000000000 : ℝ), (6517965562589/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(448869981/1000000000 : ℝ)|^2127 ≤ (34820346387483/100000000000000 : ℝ)^1615
        have hw : |(448869981/1000000000 : ℝ)|=(448869981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2134323843/5000000000 : ℝ)|^2127 ≤ (32589825791869/100000000000000 : ℝ)^1615
        have hw : |(2134323843/5000000000 : ℝ)|=(2134323843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4268647887/10000000000 : ℝ)|^2127 ≤ (6517965562589/20000000000000 : ℝ)^1615
        have hw : |(4268647887/10000000000 : ℝ)|=(4268647887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_box_4 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2260114853/10000000000 : ℝ)*x 0 + (5263750497/10000000000 : ℝ)*x 1 + (263187477/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2260114853/10000000000 : ℝ)^2127 ≤ (14104960832173/100000000000000 : ℝ)^1615 := by
    have hnat : (2260114853 : ℕ)^2127*100000000000000^1615 ≤ 14104960832173^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260114853 10000000000 14104960832173 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263750497/10000000000 : ℝ)^2127 ≤ (4294752471891/10000000000000 : ℝ)^1615 := by
    have hnat : (5263750497 : ℕ)^2127*10000000000000^1615 ≤ 4294752471891^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263750497 10000000000 4294752471891 10000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263187477/500000000 : ℝ)^2127 ≤ (21473757217601/50000000000000 : ℝ)^1615 := by
    have hnat : (263187477 : ℕ)^2127*50000000000000^1615 ≤ 21473757217601^1615*500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263187477 500000000 21473757217601 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2260114853/10000000000 : ℝ), (5263750497/10000000000 : ℝ), (263187477/500000000 : ℝ)] ![(14104960832173/100000000000000 : ℝ), (4294752471891/10000000000000 : ℝ), (21473757217601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2260114853/10000000000 : ℝ)|^2127 ≤ (14104960832173/100000000000000 : ℝ)^1615
        have hw : |(-2260114853/10000000000 : ℝ)|=(2260114853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263750497/10000000000 : ℝ)|^2127 ≤ (4294752471891/10000000000000 : ℝ)^1615
        have hw : |(5263750497/10000000000 : ℝ)|=(5263750497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263187477/500000000 : ℝ)|^2127 ≤ (21473757217601/50000000000000 : ℝ)^1615
        have hw : |(263187477/500000000 : ℝ)|=(263187477/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_box_5 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1343655019/2500000000 : ℝ)*x 0 + (-422629211/2000000000 : ℝ)*x 1 + (5263750021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343655019/2500000000 : ℝ)^2127 ≤ (44142863261133/100000000000000 : ℝ)^1615 := by
    have hnat : (1343655019 : ℕ)^2127*100000000000000^1615 ≤ 44142863261133^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343655019 2500000000 44142863261133 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422629211/2000000000 : ℝ)^2127 ≤ (12909617113693/100000000000000 : ℝ)^1615 := by
    have hnat : (422629211 : ℕ)^2127*100000000000000^1615 ≤ 12909617113693^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422629211 2000000000 12909617113693 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263750021/10000000000 : ℝ)^2127 ≤ (536843995049/1250000000000 : ℝ)^1615 := by
    have hnat : (5263750021 : ℕ)^2127*1250000000000^1615 ≤ 536843995049^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263750021 10000000000 536843995049 1250000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343655019/2500000000 : ℝ), (-422629211/2000000000 : ℝ), (5263750021/10000000000 : ℝ)] ![(44142863261133/100000000000000 : ℝ), (12909617113693/100000000000000 : ℝ), (536843995049/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343655019/2500000000 : ℝ)|^2127 ≤ (44142863261133/100000000000000 : ℝ)^1615
        have hw : |(1343655019/2500000000 : ℝ)|=(1343655019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422629211/2000000000 : ℝ)|^2127 ≤ (12909617113693/100000000000000 : ℝ)^1615
        have hw : |(-422629211/2000000000 : ℝ)|=(422629211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263750021/10000000000 : ℝ)|^2127 ≤ (536843995049/1250000000000 : ℝ)^1615
        have hw : |(5263750021/10000000000 : ℝ)|=(5263750021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_box_6 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5374620457/10000000000 : ℝ)*x 0 + (328984373/625000000 : ℝ)*x 1 + (-1056572807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374620457/10000000000 : ℝ)^2127 ≤ (22071433691209/50000000000000 : ℝ)^1615 := by
    have hnat : (5374620457 : ℕ)^2127*50000000000000^1615 ≤ 22071433691209^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374620457 10000000000 22071433691209 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328984373/625000000 : ℝ)^2127 ≤ (21473759517197/50000000000000 : ℝ)^1615 := by
    have hnat : (328984373 : ℕ)^2127*50000000000000^1615 ≤ 21473759517197^1615*625000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328984373 625000000 21473759517197 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056572807/5000000000 : ℝ)^2127 ≤ (12909613565417/100000000000000 : ℝ)^1615 := by
    have hnat : (1056572807 : ℕ)^2127*100000000000000^1615 ≤ 12909613565417^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056572807 5000000000 12909613565417 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374620457/10000000000 : ℝ), (328984373/625000000 : ℝ), (-1056572807/5000000000 : ℝ)] ![(22071433691209/50000000000000 : ℝ), (21473759517197/50000000000000 : ℝ), (12909613565417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374620457/10000000000 : ℝ)|^2127 ≤ (22071433691209/50000000000000 : ℝ)^1615
        have hw : |(5374620457/10000000000 : ℝ)|=(5374620457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328984373/625000000 : ℝ)|^2127 ≤ (21473759517197/50000000000000 : ℝ)^1615
        have hw : |(328984373/625000000 : ℝ)|=(328984373/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1056572807/5000000000 : ℝ)|^2127 ≤ (12909613565417/100000000000000 : ℝ)^1615
        have hw : |(-1056572807/5000000000 : ℝ)|=(1056572807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_box_7 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4189110477/10000000000 : ℝ)*x 0 + (883677467/2000000000 : ℝ)*x 1 + (1104596751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4189110477/10000000000 : ℝ)^2127 ≤ (7948110722249/25000000000000 : ℝ)^1615 := by
    have hnat : (4189110477 : ℕ)^2127*25000000000000^1615 ≤ 7948110722249^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4189110477 10000000000 7948110722249 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (883677467/2000000000 : ℝ)^2127 ≤ (2131486264461/6250000000000 : ℝ)^1615 := by
    have hnat : (883677467 : ℕ)^2127*6250000000000^1615 ≤ 2131486264461^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883677467 2000000000 2131486264461 6250000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1104596751/2500000000 : ℝ)^2127 ≤ (34103776866557/100000000000000 : ℝ)^1615 := by
    have hnat : (1104596751 : ℕ)^2127*100000000000000^1615 ≤ 34103776866557^1615*2500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104596751 2500000000 34103776866557 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4189110477/10000000000 : ℝ), (883677467/2000000000 : ℝ), (1104596751/2500000000 : ℝ)] ![(7948110722249/25000000000000 : ℝ), (2131486264461/6250000000000 : ℝ), (34103776866557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4189110477/10000000000 : ℝ)|^2127 ≤ (7948110722249/25000000000000 : ℝ)^1615
        have hw : |(4189110477/10000000000 : ℝ)|=(4189110477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(883677467/2000000000 : ℝ)|^2127 ≤ (2131486264461/6250000000000 : ℝ)^1615
        have hw : |(883677467/2000000000 : ℝ)|=(883677467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1104596751/2500000000 : ℝ)|^2127 ≤ (34103776866557/100000000000000 : ℝ)^1615
        have hw : |(1104596751/2500000000 : ℝ)|=(1104596751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_box_8 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2187779229/10000000000 : ℝ)*x 0 + (2587871003/5000000000 : ℝ)*x 1 + (2702982251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187779229/10000000000 : ℝ)^2127 ≤ (3378362294243/25000000000000 : ℝ)^1615 := by
    have hnat : (2187779229 : ℕ)^2127*25000000000000^1615 ≤ 3378362294243^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187779229 10000000000 3378362294243 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587871003/5000000000 : ℝ)^2127 ≤ (42004321197301/100000000000000 : ℝ)^1615 := by
    have hnat : (2587871003 : ℕ)^2127*100000000000000^1615 ≤ 42004321197301^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587871003 5000000000 42004321197301 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702982251/5000000000 : ℝ)^2127 ≤ (1112055740281/2500000000000 : ℝ)^1615 := by
    have hnat : (2702982251 : ℕ)^2127*2500000000000^1615 ≤ 1112055740281^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702982251 5000000000 1112055740281 2500000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2187779229/10000000000 : ℝ), (2587871003/5000000000 : ℝ), (2702982251/5000000000 : ℝ)] ![(3378362294243/25000000000000 : ℝ), (42004321197301/100000000000000 : ℝ), (1112055740281/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2187779229/10000000000 : ℝ)|^2127 ≤ (3378362294243/25000000000000 : ℝ)^1615
        have hw : |(-2187779229/10000000000 : ℝ)|=(2187779229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587871003/5000000000 : ℝ)|^2127 ≤ (42004321197301/100000000000000 : ℝ)^1615
        have hw : |(2587871003/5000000000 : ℝ)|=(2587871003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702982251/5000000000 : ℝ)|^2127 ≤ (1112055740281/2500000000000 : ℝ)^1615
        have hw : |(2702982251/5000000000 : ℝ)|=(2702982251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_box_9 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (329657529/625000000 : ℝ)*x 0 + (-2056334713/10000000000 : ℝ)*x 1 + (1081192939/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (329657529/625000000 : ℝ)^2127 ≤ (2691455868477/6250000000000 : ℝ)^1615 := by
    have hnat : (329657529 : ℕ)^2127*6250000000000^1615 ≤ 2691455868477^1615*625000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329657529 625000000 2691455868477 6250000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2056334713/10000000000 : ℝ)^2127 ≤ (3113618597153/25000000000000 : ℝ)^1615 := by
    have hnat : (2056334713 : ℕ)^2127*25000000000000^1615 ≤ 3113618597153^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056334713 10000000000 3113618597153 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081192939/2000000000 : ℝ)^2127 ≤ (22241115851389/50000000000000 : ℝ)^1615 := by
    have hnat : (1081192939 : ℕ)^2127*50000000000000^1615 ≤ 22241115851389^1615*2000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081192939 2000000000 22241115851389 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(329657529/625000000 : ℝ), (-2056334713/10000000000 : ℝ), (1081192939/2000000000 : ℝ)] ![(2691455868477/6250000000000 : ℝ), (3113618597153/25000000000000 : ℝ), (22241115851389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(329657529/625000000 : ℝ)|^2127 ≤ (2691455868477/6250000000000 : ℝ)^1615
        have hw : |(329657529/625000000 : ℝ)|=(329657529/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2056334713/10000000000 : ℝ)|^2127 ≤ (3113618597153/25000000000000 : ℝ)^1615
        have hw : |(-2056334713/10000000000 : ℝ)|=(2056334713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081192939/2000000000 : ℝ)|^2127 ≤ (22241115851389/50000000000000 : ℝ)^1615
        have hw : |(1081192939/2000000000 : ℝ)|=(1081192939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_box_10 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5274520669/10000000000 : ℝ)*x 0 + (168936369/312500000 : ℝ)*x 1 + (-1028167821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274520669/10000000000 : ℝ)^2127 ≤ (8612659219989/20000000000000 : ℝ)^1615 := by
    have hnat : (5274520669 : ℕ)^2127*20000000000000^1615 ≤ 8612659219989^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274520669 10000000000 8612659219989 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168936369/312500000 : ℝ)^2127 ≤ (355857776723/800000000000 : ℝ)^1615 := by
    have hnat : (168936369 : ℕ)^2127*800000000000^1615 ≤ 355857776723^1615*312500000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168936369 312500000 355857776723 800000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028167821/5000000000 : ℝ)^2127 ≤ (12454481799023/100000000000000 : ℝ)^1615 := by
    have hnat : (1028167821 : ℕ)^2127*100000000000000^1615 ≤ 12454481799023^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028167821 5000000000 12454481799023 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274520669/10000000000 : ℝ), (168936369/312500000 : ℝ), (-1028167821/5000000000 : ℝ)] ![(8612659219989/20000000000000 : ℝ), (355857776723/800000000000 : ℝ), (12454481799023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274520669/10000000000 : ℝ)|^2127 ≤ (8612659219989/20000000000000 : ℝ)^1615
        have hw : |(5274520669/10000000000 : ℝ)|=(5274520669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168936369/312500000 : ℝ)|^2127 ≤ (355857776723/800000000000 : ℝ)^1615
        have hw : |(168936369/312500000 : ℝ)|=(168936369/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1028167821/5000000000 : ℝ)|^2127 ≤ (12454481799023/100000000000000 : ℝ)^1615
        have hw : |(-1028167821/5000000000 : ℝ)|=(1028167821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_box_11 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2260474007/5000000000 : ℝ)*x 0 + (4252235709/10000000000 : ℝ)*x 1 + (4252236369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2260474007/5000000000 : ℝ)^2127 ≤ (7030037762369/20000000000000 : ℝ)^1615 := by
    have hnat : (2260474007 : ℕ)^2127*20000000000000^1615 ≤ 7030037762369^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260474007 5000000000 7030037762369 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4252235709/10000000000 : ℝ)^2127 ≤ (32424902271449/100000000000000 : ℝ)^1615 := by
    have hnat : (4252235709 : ℕ)^2127*100000000000000^1615 ≤ 32424902271449^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252235709 10000000000 32424902271449 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4252236369/10000000000 : ℝ)^2127 ≤ (810622722493/2500000000000 : ℝ)^1615 := by
    have hnat : (4252236369 : ℕ)^2127*2500000000000^1615 ≤ 810622722493^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252236369 10000000000 810622722493 2500000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2260474007/5000000000 : ℝ), (4252235709/10000000000 : ℝ), (4252236369/10000000000 : ℝ)] ![(7030037762369/20000000000000 : ℝ), (32424902271449/100000000000000 : ℝ), (810622722493/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2260474007/5000000000 : ℝ)|^2127 ≤ (7030037762369/20000000000000 : ℝ)^1615
        have hw : |(2260474007/5000000000 : ℝ)|=(2260474007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4252235709/10000000000 : ℝ)|^2127 ≤ (32424902271449/100000000000000 : ℝ)^1615
        have hw : |(4252235709/10000000000 : ℝ)|=(4252235709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4252236369/10000000000 : ℝ)|^2127 ≤ (810622722493/2500000000000 : ℝ)^1615
        have hw : |(4252236369/10000000000 : ℝ)|=(4252236369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_box_12 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-248472723/1250000000 : ℝ)*x 0 + (5477616987/10000000000 : ℝ)*x 1 + (5252725433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (248472723/1250000000 : ℝ)^2127 ≤ (372204875749/3125000000000 : ℝ)^1615 := by
    have hnat : (248472723 : ℕ)^2127*3125000000000^1615 ≤ 372204875749^1615*1250000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248472723 1250000000 372204875749 3125000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5477616987/10000000000 : ℝ)^2127 ≤ (45260352768223/100000000000000 : ℝ)^1615 := by
    have hnat : (5477616987 : ℕ)^2127*100000000000000^1615 ≤ 45260352768223^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477616987 10000000000 45260352768223 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252725433/10000000000 : ℝ)^2127 ≤ (42829091197691/100000000000000 : ℝ)^1615 := by
    have hnat : (5252725433 : ℕ)^2127*100000000000000^1615 ≤ 42829091197691^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252725433 10000000000 42829091197691 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-248472723/1250000000 : ℝ), (5477616987/10000000000 : ℝ), (5252725433/10000000000 : ℝ)] ![(372204875749/3125000000000 : ℝ), (45260352768223/100000000000000 : ℝ), (42829091197691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-248472723/1250000000 : ℝ)|^2127 ≤ (372204875749/3125000000000 : ℝ)^1615
        have hw : |(-248472723/1250000000 : ℝ)|=(248472723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5477616987/10000000000 : ℝ)|^2127 ≤ (45260352768223/100000000000000 : ℝ)^1615
        have hw : |(5477616987/10000000000 : ℝ)|=(5477616987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252725433/10000000000 : ℝ)|^2127 ≤ (42829091197691/100000000000000 : ℝ)^1615
        have hw : |(5252725433/10000000000 : ℝ)|=(5252725433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_box_13 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5382376797/10000000000 : ℝ)*x 0 + (-2117433287/10000000000 : ℝ)*x 1 + (2626362649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382376797/10000000000 : ℝ)^2127 ≤ (552834838343/1250000000000 : ℝ)^1615 := by
    have hnat : (5382376797 : ℕ)^2127*1250000000000^1615 ≤ 552834838343^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382376797 10000000000 552834838343 1250000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117433287/10000000000 : ℝ)^2127 ≤ (2588824634801/20000000000000 : ℝ)^1615 := by
    have hnat : (2117433287 : ℕ)^2127*20000000000000^1615 ≤ 2588824634801^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117433287 10000000000 2588824634801 20000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626362649/5000000000 : ℝ)^2127 ≤ (5353636218497/12500000000000 : ℝ)^1615 := by
    have hnat : (2626362649 : ℕ)^2127*12500000000000^1615 ≤ 5353636218497^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626362649 5000000000 5353636218497 12500000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382376797/10000000000 : ℝ), (-2117433287/10000000000 : ℝ), (2626362649/5000000000 : ℝ)] ![(552834838343/1250000000000 : ℝ), (2588824634801/20000000000000 : ℝ), (5353636218497/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382376797/10000000000 : ℝ)|^2127 ≤ (552834838343/1250000000000 : ℝ)^1615
        have hw : |(5382376797/10000000000 : ℝ)|=(5382376797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2117433287/10000000000 : ℝ)|^2127 ≤ (2588824634801/20000000000000 : ℝ)^1615
        have hw : |(-2117433287/10000000000 : ℝ)|=(2117433287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626362649/5000000000 : ℝ)|^2127 ≤ (5353636218497/12500000000000 : ℝ)^1615
        have hw : |(2626362649/5000000000 : ℝ)|=(2626362649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_box_14 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2691188431/5000000000 : ℝ)*x 0 + (262636277/500000000 : ℝ)*x 1 + (-2117432877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691188431/5000000000 : ℝ)^2127 ≤ (11056696942717/25000000000000 : ℝ)^1615 := by
    have hnat : (2691188431 : ℕ)^2127*25000000000000^1615 ≤ 11056696942717^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691188431 5000000000 11056696942717 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262636277/500000000 : ℝ)^2127 ≤ (1713163693869/4000000000000 : ℝ)^1615 := by
    have hnat : (262636277 : ℕ)^2127*4000000000000^1615 ≤ 1713163693869^1615*500000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262636277 500000000 1713163693869 4000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117432877/10000000000 : ℝ)^2127 ≤ (6472059936517/50000000000000 : ℝ)^1615 := by
    have hnat : (2117432877 : ℕ)^2127*50000000000000^1615 ≤ 6472059936517^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117432877 10000000000 6472059936517 50000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691188431/5000000000 : ℝ), (262636277/500000000 : ℝ), (-2117432877/10000000000 : ℝ)] ![(11056696942717/25000000000000 : ℝ), (1713163693869/4000000000000 : ℝ), (6472059936517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691188431/5000000000 : ℝ)|^2127 ≤ (11056696942717/25000000000000 : ℝ)^1615
        have hw : |(2691188431/5000000000 : ℝ)|=(2691188431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262636277/500000000 : ℝ)|^2127 ≤ (1713163693869/4000000000000 : ℝ)^1615
        have hw : |(262636277/500000000 : ℝ)|=(262636277/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2117432877/10000000000 : ℝ)|^2127 ≤ (6472059936517/50000000000000 : ℝ)^1615
        have hw : |(-2117432877/10000000000 : ℝ)|=(2117432877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1294_box_15 (p : ℝ) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2081447603/5000000000 : ℝ)*x 0 + (4431256621/10000000000 : ℝ)*x 1 + (2215628183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2081447603/5000000000 : ℝ)^2127 ≤ (7882668238917/25000000000000 : ℝ)^1615 := by
    have hnat : (2081447603 : ℕ)^2127*25000000000000^1615 ≤ 7882668238917^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081447603 5000000000 7882668238917 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4431256621/10000000000 : ℝ)^2127 ≤ (34234664811867/100000000000000 : ℝ)^1615 := by
    have hnat : (4431256621 : ℕ)^2127*100000000000000^1615 ≤ 34234664811867^1615*10000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4431256621 10000000000 34234664811867 100000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2215628183/5000000000 : ℝ)^2127 ≤ (8558665554311/25000000000000 : ℝ)^1615 := by
    have hnat : (2215628183 : ℕ)^2127*25000000000000^1615 ≤ 8558665554311^1615*5000000000^2127 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215628183 5000000000 8558665554311 25000000000000 2127 1615 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2127/512 : ℝ)) 2127 1615 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2081447603/5000000000 : ℝ), (4431256621/10000000000 : ℝ), (2215628183/5000000000 : ℝ)] ![(7882668238917/25000000000000 : ℝ), (34234664811867/100000000000000 : ℝ), (8558665554311/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2081447603/5000000000 : ℝ)|^2127 ≤ (7882668238917/25000000000000 : ℝ)^1615
        have hw : |(2081447603/5000000000 : ℝ)|=(2081447603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4431256621/10000000000 : ℝ)|^2127 ≤ (34234664811867/100000000000000 : ℝ)^1615
        have hw : |(4431256621/10000000000 : ℝ)|=(4431256621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2215628183/5000000000 : ℝ)|^2127 ≤ (8558665554311/25000000000000 : ℝ)^1615
        have hw : |(2215628183/5000000000 : ℝ)|=(2215628183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1294_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(1571/2500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58849/100000 : ℝ) ∧ (79669/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84163/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14673/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11033/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14673/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11033/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14673/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11033/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14673/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11033/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14673/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11033/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14673/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11033/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11033/100000 : ℝ) ^ (4253/1024 : ℝ) ≤ (10568174096760983/100000000000000000000 : ℝ) := by
    have hpowers : (11033/100000 : ℝ)^4253 ≤ (10568174096760983/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11033 : ℕ)^4253*100000000000000000000^1024 ≤ 10568174096760983^1024*100000^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11033 100000 10568174096760983 100000000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11033/100000 : ℝ)) (X := (10568174096760983/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14673/100000 : ℝ) ^ (4253/1024 : ℝ) ≤ (34537117660353979/100000000000000000000 : ℝ) := by
    have hpowers : (14673/100000 : ℝ)^4253 ≤ (34537117660353979/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14673 : ℕ)^4253*100000000000000000000^1024 ≤ 34537117660353979^1024*100000^4253 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14673 100000 34537117660353979 100000000000000000000 4253 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14673/100000 : ℝ)) (X := (34537117660353979/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010568174096760983/50000000000000000000 : ℝ) ≤ (5000254430803603/5000000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (50010568174096760983/50000000000000000000 : ℝ)^1024 ≤ (5000254430803603/5000000000000000 : ℝ)^4253 := by
      have hnat : (50010568174096760983 : ℕ)^1024*5000000000000000^4253 ≤ 5000254430803603^4253*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010568174096760983 50000000000000000000 5000254430803603 5000000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000254430803603/5000000000000000 : ℝ)) (X := (50010568174096760983/50000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022552645878557481/50000000000000000000 : ℝ) ≤ (5000542909855241/5000000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (50022552645878557481/50000000000000000000 : ℝ)^1024 ≤ (5000542909855241/5000000000000000 : ℝ)^4253 := by
      have hnat : (50022552645878557481 : ℕ)^1024*5000000000000000^4253 ≤ 5000542909855241^4253*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022552645878557481 50000000000000000000 5000542909855241 5000000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000542909855241/5000000000000000 : ℝ)) (X := (50022552645878557481/50000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034537117660353979/50000000000000000000 : ℝ) ≤ (5000831388906879/5000000000000000 : ℝ) ^ (4253/1024 : ℝ) := by
    have hpowers : (50034537117660353979/50000000000000000000 : ℝ)^1024 ≤ (5000831388906879/5000000000000000 : ℝ)^4253 := by
      have hnat : (50034537117660353979 : ℕ)^1024*5000000000000000^4253 ≤ 5000831388906879^4253*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034537117660353979 50000000000000000000 5000831388906879 5000000000000000 1024 4253 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000831388906879/5000000000000000 : ℝ)) (X := (50034537117660353979/50000000000000000000 : ℝ)) (by norm_num) 4253 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10568174096760983/100000000000000000000 : ℝ) ≤ ((4548640137342917703/4550000000000000000 : ℝ)+2*(144239525819/91000000000000 : ℝ)*(11033/100000 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (4548640137342917703/4550000000000000000 : ℝ)+2*(144239525819/91000000000000 : ℝ)*(11033/100000 : ℝ)=(5000254430803603/5000000000000000 : ℝ) by norm_num, show 1+2*(10568174096760983/100000000000000000000 : ℝ)=(50010568174096760983/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34537117660353979/100000000000000000000 : ℝ)+(10568174096760983/100000000000000000000 : ℝ) ≤ ((4548640137342917703/4550000000000000000 : ℝ)+(144239525819/91000000000000 : ℝ)*((14673/100000 : ℝ)+(11033/100000 : ℝ)))^(4253/1024 : ℝ) := by
    rw [show (4548640137342917703/4550000000000000000 : ℝ)+(144239525819/91000000000000 : ℝ)*((14673/100000 : ℝ)+(11033/100000 : ℝ))=(5000542909855241/5000000000000000 : ℝ) by norm_num, show 1+(34537117660353979/100000000000000000000 : ℝ)+(10568174096760983/100000000000000000000 : ℝ)=(50022552645878557481/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34537117660353979/100000000000000000000 : ℝ) ≤ ((4548640137342917703/4550000000000000000 : ℝ)+2*(144239525819/91000000000000 : ℝ)*(14673/100000 : ℝ))^(4253/1024 : ℝ) := by
    rw [show (4548640137342917703/4550000000000000000 : ℝ)+2*(144239525819/91000000000000 : ℝ)*(14673/100000 : ℝ)=(5000831388906879/5000000000000000 : ℝ) by norm_num, show 1+2*(34537117660353979/100000000000000000000 : ℝ)=(50034537117660353979/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4548640137342917703/4550000000000000000 : ℝ)*(X 1 0+X 2 0)+(144239525819/91000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (11033/100000 : ℝ)) (hi := (14673/100000 : ℝ)) (c := (4548640137342917703/4550000000000000000 : ℝ)) (alpha := (144239525819/91000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4548640137342917703/4550000000000000000 : ℝ)*(X 0 1+X 2 1)+(144239525819/91000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (11033/100000 : ℝ)) (hi := (14673/100000 : ℝ)) (c := (4548640137342917703/4550000000000000000 : ℝ)) (alpha := (144239525819/91000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4548640137342917703/4550000000000000000 : ℝ)*(X 0 2+X 1 2)+(144239525819/91000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4253/1024 : ℝ)) (lo := (11033/100000 : ℝ)) (hi := (14673/100000 : ℝ)) (c := (4548640137342917703/4550000000000000000 : ℝ)) (alpha := (144239525819/91000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-23937641/125000000 : ℝ)*X 0 0+(5391927903/10000000000 : ℝ)*X 0 1+(5391927371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1321101417/2500000000 : ℝ)*X 1 0+(-2062065133/10000000000 : ℝ)*X 1 1+(1078385559/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642203009/5000000000 : ℝ)*X 2 0+(673990961/1250000000 : ℝ)*X 2 1+(-412412961/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((448869981/1000000000 : ℝ)*X 0 0+(2134323843/5000000000 : ℝ)*X 0 1+(4268647887/10000000000 : ℝ)*X 0 2+(448869981/1000000000 : ℝ)*X 1 0+(2134323843/5000000000 : ℝ)*X 1 1+(4268647887/10000000000 : ℝ)*X 1 2+(448869981/1000000000 : ℝ)*X 2 0+(2134323843/5000000000 : ℝ)*X 2 1+(4268647887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2260114853/10000000000 : ℝ)*X 0 0+(5263750497/10000000000 : ℝ)*X 0 1+(263187477/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1343655019/2500000000 : ℝ)*X 1 0+(-422629211/2000000000 : ℝ)*X 1 1+(5263750021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5374620457/10000000000 : ℝ)*X 2 0+(328984373/625000000 : ℝ)*X 2 1+(-1056572807/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4189110477/10000000000 : ℝ)*X 0 0+(883677467/2000000000 : ℝ)*X 0 1+(1104596751/2500000000 : ℝ)*X 0 2+(4189110477/10000000000 : ℝ)*X 1 0+(883677467/2000000000 : ℝ)*X 1 1+(1104596751/2500000000 : ℝ)*X 1 2+(4189110477/10000000000 : ℝ)*X 2 0+(883677467/2000000000 : ℝ)*X 2 1+(1104596751/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2187779229/10000000000 : ℝ)*X 0 0+(2587871003/5000000000 : ℝ)*X 0 1+(2702982251/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((329657529/625000000 : ℝ)*X 1 0+(-2056334713/10000000000 : ℝ)*X 1 1+(1081192939/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5274520669/10000000000 : ℝ)*X 2 0+(168936369/312500000 : ℝ)*X 2 1+(-1028167821/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2260474007/5000000000 : ℝ)*X 0 0+(4252235709/10000000000 : ℝ)*X 0 1+(4252236369/10000000000 : ℝ)*X 0 2+(2260474007/5000000000 : ℝ)*X 1 0+(4252235709/10000000000 : ℝ)*X 1 1+(4252236369/10000000000 : ℝ)*X 1 2+(2260474007/5000000000 : ℝ)*X 2 0+(4252235709/10000000000 : ℝ)*X 2 1+(4252236369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-248472723/1250000000 : ℝ)*X 0 0+(5477616987/10000000000 : ℝ)*X 0 1+(5252725433/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5382376797/10000000000 : ℝ)*X 1 0+(-2117433287/10000000000 : ℝ)*X 1 1+(2626362649/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2691188431/5000000000 : ℝ)*X 2 0+(262636277/500000000 : ℝ)*X 2 1+(-2117432877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2081447603/5000000000 : ℝ)*X 0 0+(4431256621/10000000000 : ℝ)*X 0 1+(2215628183/5000000000 : ℝ)*X 0 2+(2081447603/5000000000 : ℝ)*X 1 0+(4431256621/10000000000 : ℝ)*X 1 1+(2215628183/5000000000 : ℝ)*X 1 2+(2081447603/5000000000 : ℝ)*X 2 0+(4431256621/10000000000 : ℝ)*X 2 1+(2215628183/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1294_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-1571/2500 : ℝ) ≤ (-5498254035181953621320842065963/8750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40593959/100000000000000 : ℝ)*(upper0) + (96533363/100000000000000 : ℝ)*(lower2) + (66258571/50000000000000 : ℝ)*(upper4) + (893661/4000000000000 : ℝ)*(upper5) + (1433225518286497/50000000000000 : ℝ)*(major0) + (1433225518286497/50000000000000 : ℝ)*(major1) + (1433225518286497/50000000000000 : ℝ)*(major2) + (4505028323/50000000000000 : ℝ)*(sp1) + (70381297/12500000000000 : ℝ)*(sp3) + (3878372762527433/100000000000000 : ℝ)*(sp4) + (775676998143597/20000000000000 : ℝ)*(sp5) + (3878394000774631/100000000000000 : ℝ)*(sp6) + (468863309744701/25000000000000 : ℝ)*(sp7) + (10619123599/50000000000000 : ℝ)*(sp8) + (93772690101459/5000000000000 : ℝ)*(f.failure) + (3878394000774631/100000000000000 : ℝ)*(f.sum) + (122617041667/21875000000000000000000000 : ℝ)*base65 + (238943392773985107/17500000000000000000000000000000 : ℝ)*base67 + (126349192891485107/17500000000000000000000000000000 : ℝ)*base69 + (21279551431485107/17500000000000000000000000000000 : ℝ)*base71 + (686887396143/87500000000000000000000000 : ℝ)*base73 + (114788569708985107/17500000000000000000000000000000 : ℝ)*base75 + (184720976798985107/17500000000000000000000000000000 : ℝ)*base77 + (221947770441485107/17500000000000000000000000000000 : ℝ)*base79 + (557776722861/175000000000000000000000000 : ℝ)*base81 + (6160777/500000000000000000000 : ℝ)*base90 + (6160777/500000000000000000000 : ℝ)*base92 + (6160777/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58849/100000 : ℝ) ≤ (33471751844736868978722548371077/56875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56029239/100000000000000 : ℝ)*(upper0) + (9809411/12500000000000 : ℝ)*(lower1) + (39123713/20000000000000 : ℝ)*(upper4) + (1466771548770753/50000000000000 : ℝ)*(major0) + (1466771548770753/50000000000000 : ℝ)*(major1) + (1466771548770753/50000000000000 : ℝ)*(major2) + (785621957893663/20000000000000 : ℝ)*(sp0) + (982028128307949/25000000000000 : ℝ)*(sp1) + (3928106069207739/100000000000000 : ℝ)*(sp2) + (479836835452531/25000000000000 : ℝ)*(sp3) + (1481095673/25000000000000 : ℝ)*(sp5) + (3092101687/25000000000000 : ℝ)*(sp6) + (654344017/20000000000000 : ℝ)*(sp7) + (2162036543/25000000000000 : ℝ)*(sp8) + (59979706672819/3125000000000 : ℝ)*(f.failure) + (3928118437614487/100000000000000 : ℝ)*(f.sum) + (407680342133/568750000000000000000000000 : ℝ)*base65 + (877225547462309641/227500000000000000000000000000000 : ℝ)*base68 + (1294353285989809641/227500000000000000000000000000000 : ℝ)*base70 + (2194737263209809641/227500000000000000000000000000000 : ℝ)*base72 + (22598718628341/1137500000000000000000000000 : ℝ)*base73 + (482694743522309641/227500000000000000000000000000000 : ℝ)*base76 + (1432856329304809641/227500000000000000000000000000000 : ℝ)*base78 + (2193440455715190359/227500000000000000000000000000000 : ℝ)*base79 + (12398419429/284375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1180857/312500000000000000000 : ℝ)*base90 + (1180857/312500000000000000000 : ℝ)*base92 + (1180857/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (79669/100000 : ℝ) ≤ (2832061385816154777310262964711/3554687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (822973/100000000000000 : ℝ)*(upper1) + (63288673/20000000000000 : ℝ)*(upper2) + (2741651/10000000000000 : ℝ)*(lower5) + (649498850775731/20000000000000 : ℝ)*(major0) + (649498850775731/20000000000000 : ℝ)*(major1) + (25371048858427/781250000000 : ℝ)*(major2) + (205098746397/50000000000000 : ℝ)*(sp1) + (157510555007/100000000000000 : ℝ)*(sp3) + (78456141/781250000000 : ℝ)*(sp4) + (1085909238050959/25000000000000 : ℝ)*(sp8) + (271453720460541/6250000000000 : ℝ)*(sp9) + (86873394497229/2000000000000 : ℝ)*(sp10) + (424920842638359/20000000000000 : ℝ)*(sp11) + (22730271567/100000000000000 : ℝ)*(sp12) + (1062380861873401/50000000000000 : ℝ)*(f.failure) + (86873394497229/2000000000000 : ℝ)*(f.sum) + (262480149931691/9100000000000000000000000000 : ℝ)*base66 + (617954783457305893/91000000000000000000000000000000 : ℝ)*base67 + (63141772141031427/28437500000000000000000000000000 : ℝ)*base70 + (444155867780694107/91000000000000000000000000000000 : ℝ)*base72 + (53129696957009/9100000000000000000000000000 : ℝ)*base73 + (10307685352593927/28437500000000000000000000000000 : ℝ)*base76 + (4726181594972884107/91000000000000000000000000000000 : ℝ)*base78 + (388403407190115893/91000000000000000000000000000000 : ℝ)*base79 + (6156941515551/910000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (22580197/5000000000000000000000 : ℝ)*base89 + (22580197/5000000000000000000000 : ℝ)*base91 + (27419803/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-84163/100000 : ℝ) ≤ (-76585857942732638917826843331/91000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15940409/25000000000000 : ℝ)*(lower0) + (74628607/100000000000000 : ℝ)*(lower1) + (6717907/4000000000000 : ℝ)*(lower2) + (19905309/50000000000000 : ℝ)*(upper5) + (1313356273947/40000000000 : ℝ)*(major0) + (1313356273947/40000000000 : ℝ)*(major1) + (1313356273947/40000000000 : ℝ)*(major2) + (452354643/10000000000000 : ℝ)*(sp0) + (11203579227/6250000000000 : ℝ)*(sp5) + (5291623997/10000000000000 : ℝ)*(sp7) + (2223291165424047/50000000000000 : ℝ)*(sp12) + (4446407597126891/100000000000000 : ℝ)*(sp13) + (1111646713598631/25000000000000 : ℝ)*(sp14) + (2148195026918343/100000000000000 : ℝ)*(sp15) + (2148247943158313/100000000000000 : ℝ)*(f.failure) + (1111646713598631/25000000000000 : ℝ)*(f.sum) + (252929233859/45500000000000000000000000 : ℝ)*base65 + (1312742196188259/182000000000000000000000000000 : ℝ)*base68 + (2535271436666259/182000000000000000000000000000 : ℝ)*base70 + (175819042640259/182000000000000000000000000000 : ℝ)*base72 + (997610384833/45500000000000000000000000 : ℝ)*base74 + (914506574222259/182000000000000000000000000000 : ℝ)*base76 + (2571262188918259/182000000000000000000000000000 : ℝ)*base78 + (9904404164532259/182000000000000000000000000000 : ℝ)*base80 + (2398436137/2275000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (7229739/10000000000000000000000 : ℝ)*base90 + (7229739/10000000000000000000000 : ℝ)*base92 + (7229739/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1294_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1571/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(58849/100000 : ℝ) else (79669/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84163/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1294_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1294_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1571/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(58849/100000 : ℝ) else (79669/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84163/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1294_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4253/1024 : ℝ) ≤ p) (hpb : p ≤ (2127/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152840397/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14673/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1571/2500 : ℝ) ≤ X j i ∧ X j i ≤ -(58849/100000 : ℝ) else (79669/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84163/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1294_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

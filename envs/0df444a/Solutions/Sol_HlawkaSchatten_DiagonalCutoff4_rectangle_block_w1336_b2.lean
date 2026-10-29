-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1336_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:03:20.815623+00:00
-- url     : https://prove2.me/submissions/31879b8f-d8f6-4ef2-81fc-0aae550a6604

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
theorem support_rectangle_w1336_s6_0 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2049159629/10000000000 : ℝ)*x 0 + (108260639/200000000 : ℝ)*x 1 + (5244410741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049159629/10000000000 : ℝ)^537 ≤ (1247750142059/10000000000000 : ℝ)^409 := by
    have hnat : (2049159629 : ℕ)^537*10000000000000^409 ≤ 1247750142059^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049159629 10000000000 1247750142059 10000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108260639/200000000 : ℝ)^537 ≤ (11167567430991/25000000000000 : ℝ)^409 := by
    have hnat : (108260639 : ℕ)^537*25000000000000^409 ≤ 11167567430991^409*200000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108260639 200000000 11167567430991 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244410741/10000000000 : ℝ)^537 ≤ (21426114420061/50000000000000 : ℝ)^409 := by
    have hnat : (5244410741 : ℕ)^537*50000000000000^409 ≤ 21426114420061^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244410741 10000000000 21426114420061 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2049159629/10000000000 : ℝ), (108260639/200000000 : ℝ), (5244410741/10000000000 : ℝ)] ![(1247750142059/10000000000000 : ℝ), (11167567430991/25000000000000 : ℝ), (21426114420061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2049159629/10000000000 : ℝ)|^537 ≤ (1247750142059/10000000000000 : ℝ)^409
        have hw : |(-2049159629/10000000000 : ℝ)|=(2049159629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108260639/200000000 : ℝ)|^537 ≤ (11167567430991/25000000000000 : ℝ)^409
        have hw : |(108260639/200000000 : ℝ)|=(108260639/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244410741/10000000000 : ℝ)|^537 ≤ (21426114420061/50000000000000 : ℝ)^409
        have hw : |(5244410741/10000000000 : ℝ)|=(5244410741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s6_1 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5349105479/10000000000 : ℝ)*x 0 + (-2135078439/10000000000 : ℝ)*x 1 + (327775669/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349105479/10000000000 : ℝ)^537 ≤ (5497363725717/12500000000000 : ℝ)^409 := by
    have hnat : (5349105479 : ℕ)^537*12500000000000^409 ≤ 5497363725717^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349105479 10000000000 5497363725717 12500000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2135078439/10000000000 : ℝ)^537 ≤ (411526929301/3125000000000 : ℝ)^409 := by
    have hnat : (2135078439 : ℕ)^537*3125000000000^409 ≤ 411526929301^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135078439 10000000000 411526929301 3125000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327775669/625000000 : ℝ)^537 ≤ (21426114221589/50000000000000 : ℝ)^409 := by
    have hnat : (327775669 : ℕ)^537*50000000000000^409 ≤ 21426114221589^409*625000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327775669 625000000 21426114221589 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349105479/10000000000 : ℝ), (-2135078439/10000000000 : ℝ), (327775669/625000000 : ℝ)] ![(5497363725717/12500000000000 : ℝ), (411526929301/3125000000000 : ℝ), (21426114221589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349105479/10000000000 : ℝ)|^537 ≤ (5497363725717/12500000000000 : ℝ)^409
        have hw : |(5349105479/10000000000 : ℝ)|=(5349105479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2135078439/10000000000 : ℝ)|^537 ≤ (411526929301/3125000000000 : ℝ)^409
        have hw : |(-2135078439/10000000000 : ℝ)|=(2135078439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327775669/625000000 : ℝ)|^537 ≤ (21426114221589/50000000000000 : ℝ)^409
        have hw : |(327775669/625000000 : ℝ)|=(327775669/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s6_2 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2674552739/5000000000 : ℝ)*x 0 + (2622205361/5000000000 : ℝ)*x 1 + (-133442401/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674552739/5000000000 : ℝ)^537 ≤ (21989454897471/50000000000000 : ℝ)^409 := by
    have hnat : (2674552739 : ℕ)^537*50000000000000^409 ≤ 21989454897471^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674552739 5000000000 21989454897471 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622205361/5000000000 : ℝ)^537 ≤ (21426114318143/50000000000000 : ℝ)^409 := by
    have hnat : (2622205361 : ℕ)^537*50000000000000^409 ≤ 21426114318143^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622205361 5000000000 21426114318143 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133442401/625000000 : ℝ)^537 ≤ (105350892411/800000000000 : ℝ)^409 := by
    have hnat : (133442401 : ℕ)^537*800000000000^409 ≤ 105350892411^409*625000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133442401 625000000 105350892411 800000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674552739/5000000000 : ℝ), (2622205361/5000000000 : ℝ), (-133442401/625000000 : ℝ)] ![(21989454897471/50000000000000 : ℝ), (21426114318143/50000000000000 : ℝ), (105350892411/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674552739/5000000000 : ℝ)|^537 ≤ (21989454897471/50000000000000 : ℝ)^409
        have hw : |(2674552739/5000000000 : ℝ)|=(2674552739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622205361/5000000000 : ℝ)|^537 ≤ (21426114318143/50000000000000 : ℝ)^409
        have hw : |(2622205361/5000000000 : ℝ)|=(2622205361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133442401/625000000 : ℝ)|^537 ≤ (105350892411/800000000000 : ℝ)^409
        have hw : |(-133442401/625000000 : ℝ)|=(133442401/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s6_3 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4328188939/10000000000 : ℝ)*x 0 + (207767681/500000000 : ℝ)*x 1 + (1126936459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328188939/10000000000 : ℝ)^537 ≤ (33303139126147/100000000000000 : ℝ)^409 := by
    have hnat : (4328188939 : ℕ)^537*100000000000000^409 ≤ 33303139126147^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328188939 10000000000 33303139126147 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207767681/500000000 : ℝ)^537 ≤ (3156807798963/10000000000000 : ℝ)^409 := by
    have hnat : (207767681 : ℕ)^537*10000000000000^409 ≤ 3156807798963^409*500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207767681 500000000 3156807798963 10000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126936459/2500000000 : ℝ)^537 ≤ (17564391432893/50000000000000 : ℝ)^409 := by
    have hnat : (1126936459 : ℕ)^537*50000000000000^409 ≤ 17564391432893^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126936459 2500000000 17564391432893 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328188939/10000000000 : ℝ), (207767681/500000000 : ℝ), (1126936459/2500000000 : ℝ)] ![(33303139126147/100000000000000 : ℝ), (3156807798963/10000000000000 : ℝ), (17564391432893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328188939/10000000000 : ℝ)|^537 ≤ (33303139126147/100000000000000 : ℝ)^409
        have hw : |(4328188939/10000000000 : ℝ)|=(4328188939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207767681/500000000 : ℝ)|^537 ≤ (3156807798963/10000000000000 : ℝ)^409
        have hw : |(207767681/500000000 : ℝ)|=(207767681/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126936459/2500000000 : ℝ)|^537 ≤ (17564391432893/50000000000000 : ℝ)^409
        have hw : |(1126936459/2500000000 : ℝ)|=(1126936459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s6_4 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2049171877/10000000000 : ℝ)*x 0 + (2622507127/5000000000 : ℝ)*x 1 + (216497013/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049171877/10000000000 : ℝ)^537 ≤ (12477599339913/100000000000000 : ℝ)^409 := by
    have hnat : (2049171877 : ℕ)^537*100000000000000^409 ≤ 12477599339913^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049171877 10000000000 12477599339913 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622507127/5000000000 : ℝ)^537 ≤ (8571740715461/20000000000000 : ℝ)^409 := by
    have hnat : (2622507127 : ℕ)^537*20000000000000^409 ≤ 8571740715461^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622507127 5000000000 8571740715461 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216497013/400000000 : ℝ)^537 ≤ (11165924264163/25000000000000 : ℝ)^409 := by
    have hnat : (216497013 : ℕ)^537*25000000000000^409 ≤ 11165924264163^409*400000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216497013 400000000 11165924264163 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2049171877/10000000000 : ℝ), (2622507127/5000000000 : ℝ), (216497013/400000000 : ℝ)] ![(12477599339913/100000000000000 : ℝ), (8571740715461/20000000000000 : ℝ), (11165924264163/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2049171877/10000000000 : ℝ)|^537 ≤ (12477599339913/100000000000000 : ℝ)^409
        have hw : |(-2049171877/10000000000 : ℝ)|=(2049171877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622507127/5000000000 : ℝ)|^537 ≤ (8571740715461/20000000000000 : ℝ)^409
        have hw : |(2622507127/5000000000 : ℝ)|=(2622507127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216497013/400000000 : ℝ)|^537 ≤ (11165924264163/25000000000000 : ℝ)^409
        have hw : |(216497013/400000000 : ℝ)|=(216497013/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s6_5 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652851307/5000000000 : ℝ)*x 0 + (-393412763/2000000000 : ℝ)*x 1 + (216497013/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652851307/5000000000 : ℝ)^537 ≤ (21755490447373/50000000000000 : ℝ)^409 := by
    have hnat : (2652851307 : ℕ)^537*50000000000000^409 ≤ 21755490447373^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652851307 5000000000 21755490447373 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (393412763/2000000000 : ℝ)^537 ≤ (5912661014987/50000000000000 : ℝ)^409 := by
    have hnat : (393412763 : ℕ)^537*50000000000000^409 ≤ 5912661014987^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393412763 2000000000 5912661014987 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216497013/400000000 : ℝ)^537 ≤ (11165924264163/25000000000000 : ℝ)^409 := by
    have hnat : (216497013 : ℕ)^537*25000000000000^409 ≤ 11165924264163^409*400000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216497013 400000000 11165924264163 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652851307/5000000000 : ℝ), (-393412763/2000000000 : ℝ), (216497013/400000000 : ℝ)] ![(21755490447373/50000000000000 : ℝ), (5912661014987/50000000000000 : ℝ), (11165924264163/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652851307/5000000000 : ℝ)|^537 ≤ (21755490447373/50000000000000 : ℝ)^409
        have hw : |(2652851307/5000000000 : ℝ)|=(2652851307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-393412763/2000000000 : ℝ)|^537 ≤ (5912661014987/50000000000000 : ℝ)^409
        have hw : |(-393412763/2000000000 : ℝ)|=(393412763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216497013/400000000 : ℝ)|^537 ≤ (11165924264163/25000000000000 : ℝ)^409
        have hw : |(216497013/400000000 : ℝ)|=(216497013/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s6_6 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652851307/5000000000 : ℝ)*x 0 + (2706212663/5000000000 : ℝ)*x 1 + (-393412763/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652851307/5000000000 : ℝ)^537 ≤ (21755490447373/50000000000000 : ℝ)^409 := by
    have hnat : (2652851307 : ℕ)^537*50000000000000^409 ≤ 21755490447373^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652851307 5000000000 21755490447373 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706212663/5000000000 : ℝ)^537 ≤ (44663697067487/100000000000000 : ℝ)^409 := by
    have hnat : (2706212663 : ℕ)^537*100000000000000^409 ≤ 44663697067487^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706212663 5000000000 44663697067487 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (393412763/2000000000 : ℝ)^537 ≤ (5912661014987/50000000000000 : ℝ)^409 := by
    have hnat : (393412763 : ℕ)^537*50000000000000^409 ≤ 5912661014987^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393412763 2000000000 5912661014987 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652851307/5000000000 : ℝ), (2706212663/5000000000 : ℝ), (-393412763/2000000000 : ℝ)] ![(21755490447373/50000000000000 : ℝ), (44663697067487/100000000000000 : ℝ), (5912661014987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652851307/5000000000 : ℝ)|^537 ≤ (21755490447373/50000000000000 : ℝ)^409
        have hw : |(2652851307/5000000000 : ℝ)|=(2652851307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706212663/5000000000 : ℝ)|^537 ≤ (44663697067487/100000000000000 : ℝ)^409
        have hw : |(2706212663/5000000000 : ℝ)|=(2706212663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-393412763/2000000000 : ℝ)|^537 ≤ (5912661014987/50000000000000 : ℝ)^409
        have hw : |(-393412763/2000000000 : ℝ)|=(393412763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s6_7 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4328214517/10000000000 : ℝ)*x 0 + (225324229/500000000 : ℝ)*x 1 + (1039155349/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328214517/10000000000 : ℝ)^537 ≤ (33303397528773/100000000000000 : ℝ)^409 := by
    have hnat : (4328214517 : ℕ)^537*100000000000000^409 ≤ 33303397528773^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328214517 10000000000 33303397528773 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225324229/500000000 : ℝ)^537 ≤ (4389484804241/12500000000000 : ℝ)^409 := by
    have hnat : (225324229 : ℕ)^537*12500000000000^409 ≤ 4389484804241^409*500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225324229 500000000 4389484804241 12500000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039155349/2500000000 : ℝ)^537 ≤ (15790362012441/50000000000000 : ℝ)^409 := by
    have hnat : (1039155349 : ℕ)^537*50000000000000^409 ≤ 15790362012441^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039155349 2500000000 15790362012441 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328214517/10000000000 : ℝ), (225324229/500000000 : ℝ), (1039155349/2500000000 : ℝ)] ![(33303397528773/100000000000000 : ℝ), (4389484804241/12500000000000 : ℝ), (15790362012441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328214517/10000000000 : ℝ)|^537 ≤ (33303397528773/100000000000000 : ℝ)^409
        have hw : |(4328214517/10000000000 : ℝ)|=(4328214517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225324229/500000000 : ℝ)|^537 ≤ (4389484804241/12500000000000 : ℝ)^409
        have hw : |(225324229/500000000 : ℝ)|=(225324229/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1039155349/2500000000 : ℝ)|^537 ≤ (15790362012441/50000000000000 : ℝ)^409
        have hw : |(1039155349/2500000000 : ℝ)|=(1039155349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1336_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11127/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5567/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (919/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1839/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11127/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1839/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11127/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1839/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11127/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1839/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11127/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1839/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11127/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1839/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11127/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11127/100000 : ℝ) ^ (4295/1024 : ℝ) ≤ (10004360755257641/100000000000000000000 : ℝ) := by
    have hpowers : (11127/100000 : ℝ)^4295 ≤ (10004360755257641/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11127 : ℕ)^4295*100000000000000000000^1024 ≤ 10004360755257641^1024*100000^4295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11127 100000 10004360755257641 100000000000000000000 4295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11127/100000 : ℝ)) (X := (10004360755257641/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1839/12500 : ℝ) ^ (4295/1024 : ℝ) ≤ (6456030348500737/20000000000000000000 : ℝ) := by
    have hpowers : (1839/12500 : ℝ)^4295 ≤ (6456030348500737/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1839 : ℕ)^4295*20000000000000000000^1024 ≤ 6456030348500737^1024*12500^4295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1839 12500 6456030348500737 20000000000000000000 4295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1839/12500 : ℝ)) (X := (6456030348500737/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010004360755257641/50000000000000000000 : ℝ) ≤ (5000238502560269/5000000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (50010004360755257641/50000000000000000000 : ℝ)^1024 ≤ (5000238502560269/5000000000000000 : ℝ)^4295 := by
      have hnat : (50010004360755257641 : ℕ)^1024*5000000000000000^4295 ≤ 5000238502560269^4295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010004360755257641 50000000000000000000 5000238502560269 5000000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000238502560269/5000000000000000 : ℝ)) (X := (50010004360755257641/50000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021142256248880663/50000000000000000000 : ℝ) ≤ (1000100797137711/1000000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (50021142256248880663/50000000000000000000 : ℝ)^1024 ≤ (1000100797137711/1000000000000000 : ℝ)^4295 := by
      have hnat : (50021142256248880663 : ℕ)^1024*1000000000000000^4295 ≤ 1000100797137711^4295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021142256248880663 50000000000000000000 1000100797137711 1000000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000100797137711/1000000000000000 : ℝ)) (X := (50021142256248880663/50000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006456030348500737/10000000000000000000 : ℝ) ≤ (5000769468816841/5000000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (10006456030348500737/10000000000000000000 : ℝ)^1024 ≤ (5000769468816841/5000000000000000 : ℝ)^4295 := by
      have hnat : (10006456030348500737 : ℕ)^1024*5000000000000000^4295 ≤ 5000769468816841^4295*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006456030348500737 10000000000000000000 5000769468816841 5000000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000769468816841/5000000000000000 : ℝ)) (X := (10006456030348500737/10000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10004360755257641/100000000000000000000 : ℝ) ≤ ((5973315656713895907/5975000000000000000 : ℝ)+2*(132741564143/89625000000000 : ℝ)*(11127/100000 : ℝ))^(4295/1024 : ℝ) := by
    rw [show (5973315656713895907/5975000000000000000 : ℝ)+2*(132741564143/89625000000000 : ℝ)*(11127/100000 : ℝ)=(5000238502560269/5000000000000000 : ℝ) by norm_num, show 1+2*(10004360755257641/100000000000000000000 : ℝ)=(50010004360755257641/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6456030348500737/20000000000000000000 : ℝ)+(10004360755257641/100000000000000000000 : ℝ) ≤ ((5973315656713895907/5975000000000000000 : ℝ)+(132741564143/89625000000000 : ℝ)*((1839/12500 : ℝ)+(11127/100000 : ℝ)))^(4295/1024 : ℝ) := by
    rw [show (5973315656713895907/5975000000000000000 : ℝ)+(132741564143/89625000000000 : ℝ)*((1839/12500 : ℝ)+(11127/100000 : ℝ))=(1000100797137711/1000000000000000 : ℝ) by norm_num, show 1+(6456030348500737/20000000000000000000 : ℝ)+(10004360755257641/100000000000000000000 : ℝ)=(50021142256248880663/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6456030348500737/20000000000000000000 : ℝ) ≤ ((5973315656713895907/5975000000000000000 : ℝ)+2*(132741564143/89625000000000 : ℝ)*(1839/12500 : ℝ))^(4295/1024 : ℝ) := by
    rw [show (5973315656713895907/5975000000000000000 : ℝ)+2*(132741564143/89625000000000 : ℝ)*(1839/12500 : ℝ)=(5000769468816841/5000000000000000 : ℝ) by norm_num, show 1+2*(6456030348500737/20000000000000000000 : ℝ)=(10006456030348500737/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5973315656713895907/5975000000000000000 : ℝ)*(X 1 0+X 2 0)+(132741564143/89625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (11127/100000 : ℝ)) (hi := (1839/12500 : ℝ)) (c := (5973315656713895907/5975000000000000000 : ℝ)) (alpha := (132741564143/89625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5973315656713895907/5975000000000000000 : ℝ)*(X 0 1+X 2 1)+(132741564143/89625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (11127/100000 : ℝ)) (hi := (1839/12500 : ℝ)) (c := (5973315656713895907/5975000000000000000 : ℝ)) (alpha := (132741564143/89625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5973315656713895907/5975000000000000000 : ℝ)*(X 0 2+X 1 2)+(132741564143/89625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (11127/100000 : ℝ)) (hi := (1839/12500 : ℝ)) (c := (5973315656713895907/5975000000000000000 : ℝ)) (alpha := (132741564143/89625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2049159629/10000000000 : ℝ)*X 0 0+(108260639/200000000 : ℝ)*X 0 1+(5244410741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349105479/10000000000 : ℝ)*X 1 0+(-2135078439/10000000000 : ℝ)*X 1 1+(327775669/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674552739/5000000000 : ℝ)*X 2 0+(2622205361/5000000000 : ℝ)*X 2 1+(-133442401/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4328188939/10000000000 : ℝ)*X 0 0+(207767681/500000000 : ℝ)*X 0 1+(1126936459/2500000000 : ℝ)*X 0 2+(4328188939/10000000000 : ℝ)*X 1 0+(207767681/500000000 : ℝ)*X 1 1+(1126936459/2500000000 : ℝ)*X 1 2+(4328188939/10000000000 : ℝ)*X 2 0+(207767681/500000000 : ℝ)*X 2 1+(1126936459/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2049171877/10000000000 : ℝ)*X 0 0+(2622507127/5000000000 : ℝ)*X 0 1+(216497013/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652851307/5000000000 : ℝ)*X 1 0+(-393412763/2000000000 : ℝ)*X 1 1+(216497013/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652851307/5000000000 : ℝ)*X 2 0+(2706212663/5000000000 : ℝ)*X 2 1+(-393412763/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4328214517/10000000000 : ℝ)*X 0 0+(225324229/500000000 : ℝ)*X 0 1+(1039155349/2500000000 : ℝ)*X 0 2+(4328214517/10000000000 : ℝ)*X 1 0+(225324229/500000000 : ℝ)*X 1 1+(1039155349/2500000000 : ℝ)*X 1 2+(4328214517/10000000000 : ℝ)*X 2 0+(225324229/500000000 : ℝ)*X 2 1+(1039155349/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1425844961208028994592611101/149375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (907249167/50000000000000 : ℝ)*(base19) + (840454013/50000000000000 : ℝ)*(base23) + (70865813/100000000000000 : ℝ)*(lower2) + (232684391/100000000000000 : ℝ)*(upper3) + (81253873/50000000000000 : ℝ)*(upper5) + (4384154066113561/100000000000000 : ℝ)*(major0) + (4384154066113561/100000000000000 : ℝ)*(major1) + (2192077033056781/50000000000000 : ℝ)*(major2) + (2965244526568983/50000000000000 : ℝ)*(sp0) + (5930523442255777/100000000000000 : ℝ)*(sp1) + (1186104715169217/20000000000000 : ℝ)*(sp2) + (709440998264813/25000000000000 : ℝ)*(sp3) + (7240723229/20000000000000 : ℝ)*(sp4) + (3712846713/20000000000000 : ℝ)*(sp7) + (2837782557292817/100000000000000 : ℝ)*(f.failure) + (5930525256754111/100000000000000 : ℝ)*(f.sum) + (665629247/729370117187500000000000 : ℝ)*base66 + (20242513337216515519/1792500000000000000000000000000000 : ℝ)*base68 + (6324031127963899/896250000000000000000000000000000 : ℝ)*base70 + (14487686018328484481/1792500000000000000000000000000000 : ℝ)*base71 + (19252574592349/5975000000000000000000000000 : ℝ)*base74 + (3934114630139213899/896250000000000000000000000000000 : ℝ)*base76 + (23623946986752384481/1792500000000000000000000000000000 : ℝ)*base77 + (27098807220745115519/1792500000000000000000000000000000 : ℝ)*base80 + (9124499888651/2240625000000000000000000000 : ℝ)*base82 + (927173/1250000000000000000000 : ℝ)*base90 + (927173/1250000000000000000000 : ℝ)*base92 + (13427173/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40499019299748316296528903/4667968750000000000000000000000 : ℝ) := by norm_num
    linear_combination (378642089/25000000000000 : ℝ)*(base19) + (205796977/12500000000000 : ℝ)*(base23) + (35367107/20000000000000 : ℝ)*(upper3) + (59699757/100000000000000 : ℝ)*(lower4) + (44537763/25000000000000 : ℝ)*(upper5) + (551973713898897/12500000000000 : ℝ)*(major0) + (551973713898897/12500000000000 : ℝ)*(major1) + (551973713898897/12500000000000 : ℝ)*(major2) + (7707424573/25000000000000 : ℝ)*(sp1) + (33187460943/100000000000000 : ℝ)*(sp2) + (2986659701386507/50000000000000 : ℝ)*(sp4) + (2986643529253183/50000000000000 : ℝ)*(sp5) + (1194656913787251/20000000000000 : ℝ)*(sp6) + (178641233150707/6250000000000 : ℝ)*(sp7) + (178641233150707/6250000000000 : ℝ)*(f.failure) + (2986659701386507/50000000000000 : ℝ)*(f.sum) + (16171977102937/2987500000000000000000000000 : ℝ)*base65 + (973458522232235421/74687500000000000000000000000000 : ℝ)*base68 + (107173190999110421/74687500000000000000000000000000 : ℝ)*base70 + (325709001886514579/74687500000000000000000000000000 : ℝ)*base71 + (10952752671863/2987500000000000000000000000 : ℝ)*base74 + (814258945796610421/74687500000000000000000000000000 : ℝ)*base76 + (106674392472235421/74687500000000000000000000000000 : ℝ)*base78 + (921960252663485421/74687500000000000000000000000000 : ℝ)*base80 + (38503441813199/5975000000000000000000000000 : ℝ)*base81 + (347583/78125000000000000000 : ℝ)*base90 + (347583/78125000000000000000 : ℝ)*base92 + (347583/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1336_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11127/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5567/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (919/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1336_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1336_s7_0 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2049168371/10000000000 : ℝ)*x 0 + (5412968063/10000000000 : ℝ)*x 1 + (5244468749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049168371/10000000000 : ℝ)^537 ≤ (1559696413801/12500000000000 : ℝ)^409 := by
    have hnat : (2049168371 : ℕ)^537*12500000000000^409 ≤ 1559696413801^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049168371 10000000000 1559696413801 12500000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412968063/10000000000 : ℝ)^537 ≤ (44669577509523/100000000000000 : ℝ)^409 := by
    have hnat : (5412968063 : ℕ)^537*100000000000000^409 ≤ 44669577509523^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412968063 10000000000 44669577509523 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244468749/10000000000 : ℝ)^537 ≤ (42852851163819/100000000000000 : ℝ)^409 := by
    have hnat : (5244468749 : ℕ)^537*100000000000000^409 ≤ 42852851163819^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244468749 10000000000 42852851163819 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2049168371/10000000000 : ℝ), (5412968063/10000000000 : ℝ), (5244468749/10000000000 : ℝ)] ![(1559696413801/12500000000000 : ℝ), (44669577509523/100000000000000 : ℝ), (42852851163819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2049168371/10000000000 : ℝ)|^537 ≤ (1559696413801/12500000000000 : ℝ)^409
        have hw : |(-2049168371/10000000000 : ℝ)|=(2049168371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412968063/10000000000 : ℝ)|^537 ≤ (44669577509523/100000000000000 : ℝ)^409
        have hw : |(5412968063/10000000000 : ℝ)|=(5412968063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244468749/10000000000 : ℝ)|^537 ≤ (42852851163819/100000000000000 : ℝ)^409
        have hw : |(5244468749/10000000000 : ℝ)|=(5244468749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s7_1 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (106981771/200000000 : ℝ)*x 0 + (-2135023887/10000000000 : ℝ)*x 1 + (1311117229/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106981771/200000000 : ℝ)^537 ≤ (21989363530397/50000000000000 : ℝ)^409 := by
    have hnat : (106981771 : ℕ)^537*50000000000000^409 ≤ 21989363530397^409*200000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106981771 200000000 21989363530397 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2135023887/10000000000 : ℝ)^537 ≤ (13168419969563/100000000000000 : ℝ)^409 := by
    have hnat : (2135023887 : ℕ)^537*100000000000000^409 ≤ 13168419969563^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135023887 10000000000 13168419969563 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311117229/2500000000 : ℝ)^537 ≤ (21426426477719/50000000000000 : ℝ)^409 := by
    have hnat : (1311117229 : ℕ)^537*50000000000000^409 ≤ 21426426477719^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311117229 2500000000 21426426477719 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106981771/200000000 : ℝ), (-2135023887/10000000000 : ℝ), (1311117229/2500000000 : ℝ)] ![(21989363530397/50000000000000 : ℝ), (13168419969563/100000000000000 : ℝ), (21426426477719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106981771/200000000 : ℝ)|^537 ≤ (21989363530397/50000000000000 : ℝ)^409
        have hw : |(106981771/200000000 : ℝ)|=(106981771/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2135023887/10000000000 : ℝ)|^537 ≤ (13168419969563/100000000000000 : ℝ)^409
        have hw : |(-2135023887/10000000000 : ℝ)|=(2135023887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311117229/2500000000 : ℝ)|^537 ≤ (21426426477719/50000000000000 : ℝ)^409
        have hw : |(1311117229/2500000000 : ℝ)|=(1311117229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s7_2 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4279271/8000000 : ℝ)*x 0 + (5244468691/10000000000 : ℝ)*x 1 + (-2135023919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4279271/8000000 : ℝ)^537 ≤ (43978729219751/100000000000000 : ℝ)^409 := by
    have hnat : (4279271 : ℕ)^537*100000000000000^409 ≤ 43978729219751^409*8000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4279271 8000000 43978729219751 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244468691/10000000000 : ℝ)^537 ≤ (2142642527079/5000000000000 : ℝ)^409 := by
    have hnat : (5244468691 : ℕ)^537*5000000000000^409 ≤ 2142642527079^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244468691 10000000000 2142642527079 5000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2135023919/10000000000 : ℝ)^537 ≤ (13168420228701/100000000000000 : ℝ)^409 := by
    have hnat : (2135023919 : ℕ)^537*100000000000000^409 ≤ 13168420228701^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135023919 10000000000 13168420228701 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4279271/8000000 : ℝ), (5244468691/10000000000 : ℝ), (-2135023919/10000000000 : ℝ)] ![(43978729219751/100000000000000 : ℝ), (2142642527079/5000000000000 : ℝ), (13168420228701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4279271/8000000 : ℝ)|^537 ≤ (43978729219751/100000000000000 : ℝ)^409
        have hw : |(4279271/8000000 : ℝ)|=(4279271/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244468691/10000000000 : ℝ)|^537 ≤ (2142642527079/5000000000000 : ℝ)^409
        have hw : |(5244468691/10000000000 : ℝ)|=(5244468691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2135023919/10000000000 : ℝ)|^537 ≤ (13168420228701/100000000000000 : ℝ)^409
        have hw : |(-2135023919/10000000000 : ℝ)|=(2135023919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s7_3 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4328193197/10000000000 : ℝ)*x 0 + (2077740377/5000000000 : ℝ)*x 1 + (2253808847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328193197/10000000000 : ℝ)^537 ≤ (16651591071353/50000000000000 : ℝ)^409 := by
    have hnat : (4328193197 : ℕ)^537*50000000000000^409 ≤ 16651591071353^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328193197 10000000000 16651591071353 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077740377/5000000000 : ℝ)^537 ≤ (31569346093771/100000000000000 : ℝ)^409 := by
    have hnat : (2077740377 : ℕ)^537*100000000000000^409 ≤ 31569346093771^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077740377 5000000000 31569346093771 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253808847/5000000000 : ℝ)^537 ≤ (35127471740401/100000000000000 : ℝ)^409 := by
    have hnat : (2253808847 : ℕ)^537*100000000000000^409 ≤ 35127471740401^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253808847 5000000000 35127471740401 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328193197/10000000000 : ℝ), (2077740377/5000000000 : ℝ), (2253808847/5000000000 : ℝ)] ![(16651591071353/50000000000000 : ℝ), (31569346093771/100000000000000 : ℝ), (35127471740401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328193197/10000000000 : ℝ)|^537 ≤ (16651591071353/50000000000000 : ℝ)^409
        have hw : |(4328193197/10000000000 : ℝ)|=(4328193197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2077740377/5000000000 : ℝ)|^537 ≤ (31569346093771/100000000000000 : ℝ)^409
        have hw : |(2077740377/5000000000 : ℝ)|=(2077740377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253808847/5000000000 : ℝ)|^537 ≤ (35127471740401/100000000000000 : ℝ)^409
        have hw : |(2253808847/5000000000 : ℝ)|=(2253808847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s7_4 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2049180521/10000000000 : ℝ)*x 0 + (5245071559/10000000000 : ℝ)*x 1 + (5412362203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049180521/10000000000 : ℝ)^537 ≤ (12477668446377/100000000000000 : ℝ)^409 := by
    have hnat : (2049180521 : ℕ)^537*100000000000000^409 ≤ 12477668446377^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049180521 10000000000 12477668446377 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245071559/10000000000 : ℝ)^537 ≤ (42859318381177/100000000000000 : ℝ)^409 := by
    have hnat : (5245071559 : ℕ)^537*100000000000000^409 ≤ 42859318381177^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245071559 10000000000 42859318381177 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412362203/10000000000 : ℝ)^537 ≤ (8932602630989/20000000000000 : ℝ)^409 := by
    have hnat : (5412362203 : ℕ)^537*20000000000000^409 ≤ 8932602630989^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412362203 10000000000 8932602630989 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2049180521/10000000000 : ℝ), (5245071559/10000000000 : ℝ), (5412362203/10000000000 : ℝ)] ![(12477668446377/100000000000000 : ℝ), (42859318381177/100000000000000 : ℝ), (8932602630989/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2049180521/10000000000 : ℝ)|^537 ≤ (12477668446377/100000000000000 : ℝ)^409
        have hw : |(-2049180521/10000000000 : ℝ)|=(2049180521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245071559/10000000000 : ℝ)|^537 ≤ (42859318381177/100000000000000 : ℝ)^409
        have hw : |(5245071559/10000000000 : ℝ)|=(5245071559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412362203/10000000000 : ℝ)|^537 ≤ (8932602630989/20000000000000 : ℝ)^409
        have hw : |(5412362203/10000000000 : ℝ)|=(5412362203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s7_5 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652858713/5000000000 : ℝ)*x 0 + (-196713049/1000000000 : ℝ)*x 1 + (338272627/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652858713/5000000000 : ℝ)^537 ≤ (2719446273757/6250000000000 : ℝ)^409 := by
    have hnat : (2652858713 : ℕ)^537*6250000000000^409 ≤ 2719446273757^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652858713 5000000000 2719446273757 6250000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196713049/1000000000 : ℝ)^537 ≤ (5912924151331/50000000000000 : ℝ)^409 := by
    have hnat : (196713049 : ℕ)^537*50000000000000^409 ≤ 5912924151331^409*1000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196713049 1000000000 5912924151331 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338272627/625000000 : ℝ)^537 ≤ (5582876412779/12500000000000 : ℝ)^409 := by
    have hnat : (338272627 : ℕ)^537*12500000000000^409 ≤ 5582876412779^409*625000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338272627 625000000 5582876412779 12500000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652858713/5000000000 : ℝ), (-196713049/1000000000 : ℝ), (338272627/625000000 : ℝ)] ![(2719446273757/6250000000000 : ℝ), (5912924151331/50000000000000 : ℝ), (5582876412779/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652858713/5000000000 : ℝ)|^537 ≤ (2719446273757/6250000000000 : ℝ)^409
        have hw : |(2652858713/5000000000 : ℝ)|=(2652858713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-196713049/1000000000 : ℝ)|^537 ≤ (5912924151331/50000000000000 : ℝ)^409
        have hw : |(-196713049/1000000000 : ℝ)|=(196713049/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338272627/625000000 : ℝ)|^537 ≤ (5582876412779/12500000000000 : ℝ)^409
        have hw : |(338272627/625000000 : ℝ)|=(338272627/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s7_6 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305717457/10000000000 : ℝ)*x 0 + (270618107/500000000 : ℝ)*x 1 + (-1967130299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305717457/10000000000 : ℝ)^537 ≤ (43511140713899/100000000000000 : ℝ)^409 := by
    have hnat : (5305717457 : ℕ)^537*100000000000000^409 ≤ 43511140713899^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305717457 10000000000 43511140713899 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270618107/500000000 : ℝ)^537 ≤ (44663012472367/100000000000000 : ℝ)^409 := by
    have hnat : (270618107 : ℕ)^537*100000000000000^409 ≤ 44663012472367^409*500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270618107 500000000 44663012472367 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1967130299/10000000000 : ℝ)^537 ≤ (11825846795071/100000000000000 : ℝ)^409 := by
    have hnat : (1967130299 : ℕ)^537*100000000000000^409 ≤ 11825846795071^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967130299 10000000000 11825846795071 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305717457/10000000000 : ℝ), (270618107/500000000 : ℝ), (-1967130299/10000000000 : ℝ)] ![(43511140713899/100000000000000 : ℝ), (44663012472367/100000000000000 : ℝ), (11825846795071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305717457/10000000000 : ℝ)|^537 ≤ (43511140713899/100000000000000 : ℝ)^409
        have hw : |(5305717457/10000000000 : ℝ)|=(5305717457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270618107/500000000 : ℝ)|^537 ≤ (44663012472367/100000000000000 : ℝ)^409
        have hw : |(270618107/500000000 : ℝ)|=(270618107/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1967130299/10000000000 : ℝ)|^537 ≤ (11825846795071/100000000000000 : ℝ)^409
        have hw : |(-1967130299/10000000000 : ℝ)|=(1967130299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s7_7 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4328218879/10000000000 : ℝ)*x 0 + (4506358583/10000000000 : ℝ)*x 1 + (4156746201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328218879/10000000000 : ℝ)^537 ≤ (8325860399019/25000000000000 : ℝ)^409 := by
    have hnat : (4328218879 : ℕ)^537*25000000000000^409 ≤ 8325860399019^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328218879 10000000000 8325860399019 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506358583/10000000000 : ℝ)^537 ≤ (35114589368593/100000000000000 : ℝ)^409 := by
    have hnat : (4506358583 : ℕ)^537*100000000000000^409 ≤ 35114589368593^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506358583 10000000000 35114589368593 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4156746201/10000000000 : ℝ)^537 ≤ (15790984508521/50000000000000 : ℝ)^409 := by
    have hnat : (4156746201 : ℕ)^537*50000000000000^409 ≤ 15790984508521^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4156746201 10000000000 15790984508521 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328218879/10000000000 : ℝ), (4506358583/10000000000 : ℝ), (4156746201/10000000000 : ℝ)] ![(8325860399019/25000000000000 : ℝ), (35114589368593/100000000000000 : ℝ), (15790984508521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328218879/10000000000 : ℝ)|^537 ≤ (8325860399019/25000000000000 : ℝ)^409
        have hw : |(4328218879/10000000000 : ℝ)|=(4328218879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506358583/10000000000 : ℝ)|^537 ≤ (35114589368593/100000000000000 : ℝ)^409
        have hw : |(4506358583/10000000000 : ℝ)|=(4506358583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4156746201/10000000000 : ℝ)|^537 ≤ (15790984508521/50000000000000 : ℝ)^409
        have hw : |(4156746201/10000000000 : ℝ)|=(4156746201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1336_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (919/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5567/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (348/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7351/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (919/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5567/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (919/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5567/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (919/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5567/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (919/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5567/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (919/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5567/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (919/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5567/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5567/50000 : ℝ) ^ (4295/1024 : ℝ) ≤ (10030785381846407/100000000000000000000 : ℝ) := by
    have hpowers : (5567/50000 : ℝ)^4295 ≤ (10030785381846407/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5567 : ℕ)^4295*100000000000000000000^1024 ≤ 10030785381846407^1024*50000^4295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5567 50000 10030785381846407 100000000000000000000 4295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5567/50000 : ℝ)) (X := (10030785381846407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (919/6250 : ℝ) ^ (4295/1024 : ℝ) ≤ (32206592058964687/100000000000000000000 : ℝ) := by
    have hpowers : (919/6250 : ℝ)^4295 ≤ (32206592058964687/100000000000000000000 : ℝ)^1024 := by
      have hnat : (919 : ℕ)^4295*100000000000000000000^1024 ≤ 32206592058964687^1024*6250^4295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        919 6250 32206592058964687 100000000000000000000 4295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (919/6250 : ℝ)) (X := (32206592058964687/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010030785381846407/50000000000000000000 : ℝ) ≤ (19532184111217/19531250000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (50010030785381846407/50000000000000000000 : ℝ)^1024 ≤ (19532184111217/19531250000000 : ℝ)^4295 := by
      have hnat : (50010030785381846407 : ℕ)^1024*19531250000000^4295 ≤ 19532184111217^4295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010030785381846407 50000000000000000000 19532184111217 19531250000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (19532184111217/19531250000000 : ℝ)) (X := (50010030785381846407/50000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021118688720405547/50000000000000000000 : ℝ) ≤ (2500251711989973/2500000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (50021118688720405547/50000000000000000000 : ℝ)^1024 ≤ (2500251711989973/2500000000000000 : ℝ)^4295 := by
      have hnat : (50021118688720405547 : ℕ)^1024*2500000000000000^4295 ≤ 2500251711989973^4295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021118688720405547 50000000000000000000 2500251711989973 2500000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500251711989973/2500000000000000 : ℝ)) (X := (50021118688720405547/50000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032206592058964687/50000000000000000000 : ℝ) ≤ (250038385774417/250000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (50032206592058964687/50000000000000000000 : ℝ)^1024 ≤ (250038385774417/250000000000000 : ℝ)^4295 := by
      have hnat : (50032206592058964687 : ℕ)^1024*250000000000000^4295 ≤ 250038385774417^4295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032206592058964687 50000000000000000000 250038385774417 250000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250038385774417/250000000000000 : ℝ)) (X := (50032206592058964687/50000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10030785381846407/100000000000000000000 : ℝ) ≤ ((2230621057451815381/2231250000000000000 : ℝ)+2*(132145754197/89250000000000 : ℝ)*(5567/50000 : ℝ))^(4295/1024 : ℝ) := by
    rw [show (2230621057451815381/2231250000000000000 : ℝ)+2*(132145754197/89250000000000 : ℝ)*(5567/50000 : ℝ)=(19532184111217/19531250000000 : ℝ) by norm_num, show 1+2*(10030785381846407/100000000000000000000 : ℝ)=(50010030785381846407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32206592058964687/100000000000000000000 : ℝ)+(10030785381846407/100000000000000000000 : ℝ) ≤ ((2230621057451815381/2231250000000000000 : ℝ)+(132145754197/89250000000000 : ℝ)*((919/6250 : ℝ)+(5567/50000 : ℝ)))^(4295/1024 : ℝ) := by
    rw [show (2230621057451815381/2231250000000000000 : ℝ)+(132145754197/89250000000000 : ℝ)*((919/6250 : ℝ)+(5567/50000 : ℝ))=(2500251711989973/2500000000000000 : ℝ) by norm_num, show 1+(32206592058964687/100000000000000000000 : ℝ)+(10030785381846407/100000000000000000000 : ℝ)=(50021118688720405547/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32206592058964687/100000000000000000000 : ℝ) ≤ ((2230621057451815381/2231250000000000000 : ℝ)+2*(132145754197/89250000000000 : ℝ)*(919/6250 : ℝ))^(4295/1024 : ℝ) := by
    rw [show (2230621057451815381/2231250000000000000 : ℝ)+2*(132145754197/89250000000000 : ℝ)*(919/6250 : ℝ)=(250038385774417/250000000000000 : ℝ) by norm_num, show 1+2*(32206592058964687/100000000000000000000 : ℝ)=(50032206592058964687/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2230621057451815381/2231250000000000000 : ℝ)*(X 1 0+X 2 0)+(132145754197/89250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (5567/50000 : ℝ)) (hi := (919/6250 : ℝ)) (c := (2230621057451815381/2231250000000000000 : ℝ)) (alpha := (132145754197/89250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2230621057451815381/2231250000000000000 : ℝ)*(X 0 1+X 2 1)+(132145754197/89250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (5567/50000 : ℝ)) (hi := (919/6250 : ℝ)) (c := (2230621057451815381/2231250000000000000 : ℝ)) (alpha := (132145754197/89250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2230621057451815381/2231250000000000000 : ℝ)*(X 0 2+X 1 2)+(132145754197/89250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (5567/50000 : ℝ)) (hi := (919/6250 : ℝ)) (c := (2230621057451815381/2231250000000000000 : ℝ)) (alpha := (132145754197/89250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2049168371/10000000000 : ℝ)*X 0 0+(5412968063/10000000000 : ℝ)*X 0 1+(5244468749/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((106981771/200000000 : ℝ)*X 1 0+(-2135023887/10000000000 : ℝ)*X 1 1+(1311117229/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((4279271/8000000 : ℝ)*X 2 0+(5244468691/10000000000 : ℝ)*X 2 1+(-2135023919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4328193197/10000000000 : ℝ)*X 0 0+(2077740377/5000000000 : ℝ)*X 0 1+(2253808847/5000000000 : ℝ)*X 0 2+(4328193197/10000000000 : ℝ)*X 1 0+(2077740377/5000000000 : ℝ)*X 1 1+(2253808847/5000000000 : ℝ)*X 1 2+(4328193197/10000000000 : ℝ)*X 2 0+(2077740377/5000000000 : ℝ)*X 2 1+(2253808847/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2049180521/10000000000 : ℝ)*X 0 0+(5245071559/10000000000 : ℝ)*X 0 1+(5412362203/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652858713/5000000000 : ℝ)*X 1 0+(-196713049/1000000000 : ℝ)*X 1 1+(338272627/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305717457/10000000000 : ℝ)*X 2 0+(270618107/500000000 : ℝ)*X 2 1+(-1967130299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4328218879/10000000000 : ℝ)*X 0 0+(4506358583/10000000000 : ℝ)*X 0 1+(4156746201/10000000000 : ℝ)*X 0 2+(4328218879/10000000000 : ℝ)*X 1 0+(4506358583/10000000000 : ℝ)*X 1 1+(4156746201/10000000000 : ℝ)*X 1 2+(4328218879/10000000000 : ℝ)*X 2 0+(4506358583/10000000000 : ℝ)*X 2 1+(4156746201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4105499014244106083489/1487500000000000000000000000 : ℝ) := by norm_num
    linear_combination (23159317/12500000000000 : ℝ)*(base19) + (14939003/4000000000000 : ℝ)*(base23) + (1802499/10000000000000 : ℝ)*(lower2) + (28181771/50000000000000 : ℝ)*(upper3) + (499/1562500000 : ℝ)*(upper5) + (4387281951566379/100000000000000 : ℝ)*(major0) + (4387281951566379/100000000000000 : ℝ)*(major1) + (219364097578319/5000000000000 : ℝ)*(major2) + (2967374418504363/50000000000000 : ℝ)*(sp0) + (1483689111412943/25000000000000 : ℝ)*(sp1) + (185461133045351/3125000000000 : ℝ)*(sp2) + (709951272498991/25000000000000 : ℝ)*(sp3) + (7793917581/100000000000000 : ℝ)*(sp4) + (2090210501/100000000000000 : ℝ)*(sp7) + (1419903590103233/50000000000000 : ℝ)*(f.failure) + (5934756630926307/100000000000000 : ℝ)*(f.sum) + (24423604797523/8925000000000000000000000000 : ℝ)*base65 + (1846601790126175399/223125000000000000000000000000000 : ℝ)*base67 + (110033830900340789/11156250000000000000000000000000 : ℝ)*base69 + (1155871389790699601/223125000000000000000000000000000 : ℝ)*base72 + (6986400100331/1115625000000000000000000000 : ℝ)*base73 + (54692935452627961/11156250000000000000000000000000 : ℝ)*base76 + (228153614506874867/74375000000000000000000000000000 : ℝ)*base78 + (12004081295625133/74375000000000000000000000000000 : ℝ)*base79 + (20231091339167/2975000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (8529723/625000000000000000000 : ℝ)*base89 + (8529723/625000000000000000000 : ℝ)*base91 + (2279723/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7957730095675709968089319/5312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39701051/10000000000000 : ℝ)*(base19) + (704232883/100000000000000 : ℝ)*(base23) + (10329839/25000000000000 : ℝ)*(lower1) + (38597467/100000000000000 : ℝ)*(upper3) + (92454271/100000000000000 : ℝ)*(lower4) + (4418965490742053/100000000000000 : ℝ)*(major0) + (4418965490742053/100000000000000 : ℝ)*(major1) + (2209482745371027/50000000000000 : ℝ)*(major2) + (11993793459/100000000000000 : ℝ)*(sp2) + (348970087/12500000000000 : ℝ)*(sp3) + (29888077886283/500000000000 : ℝ)*(sp4) + (597761518024609/10000000000000 : ℝ)*(sp5) + (2988801439615129/50000000000000 : ℝ)*(sp6) + (57206251250719/2000000000000 : ℝ)*(sp7) + (1430157677148323/50000000000000 : ℝ)*(f.failure) + (29888077886283/500000000000 : ℝ)*(f.sum) + (40465117231229/8925000000000000000000000000 : ℝ)*base65 + (453858264203617193/223125000000000000000000000000000 : ℝ)*base67 + (176206931656503787/111562500000000000000000000000000 : ℝ)*base69 + (79296883531117193/223125000000000000000000000000000 : ℝ)*base71 + (26709702206129/8925000000000000000000000000 : ℝ)*base73 + (660369764919003787/111562500000000000000000000000000 : ℝ)*base75 + (654146689268807807/223125000000000000000000000000000 : ℝ)*base78 + (2038605554490567193/223125000000000000000000000000000 : ℝ)*base79 + (46357779794707/8925000000000000000000000000 : ℝ)*base81 + (37487/625000000000000000000 : ℝ)*base90 + (37487/625000000000000000000 : ℝ)*base92 + (6287487/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1336_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (919/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5567/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (348/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1336_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1336_box_0 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1881439999/10000000000 : ℝ)*x 0 + (539018917/1000000000 : ℝ)*x 1 + (5390189023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1881439999/10000000000 : ℝ)^537 ≤ (5577069023291/50000000000000 : ℝ)^409 := by
    have hnat : (1881439999 : ℕ)^537*50000000000000^409 ≤ 5577069023291^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1881439999 10000000000 5577069023291 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539018917/1000000000 : ℝ)^537 ≤ (8884586353737/20000000000000 : ℝ)^409 := by
    have hnat : (539018917 : ℕ)^537*20000000000000^409 ≤ 8884586353737^409*1000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539018917 1000000000 8884586353737 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390189023/10000000000 : ℝ)^537 ≤ (22211465089023/50000000000000 : ℝ)^409 := by
    have hnat : (5390189023 : ℕ)^537*50000000000000^409 ≤ 22211465089023^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390189023 10000000000 22211465089023 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1881439999/10000000000 : ℝ), (539018917/1000000000 : ℝ), (5390189023/10000000000 : ℝ)] ![(5577069023291/50000000000000 : ℝ), (8884586353737/20000000000000 : ℝ), (22211465089023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1881439999/10000000000 : ℝ)|^537 ≤ (5577069023291/50000000000000 : ℝ)^409
        have hw : |(-1881439999/10000000000 : ℝ)|=(1881439999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539018917/1000000000 : ℝ)|^537 ≤ (8884586353737/20000000000000 : ℝ)^409
        have hw : |(539018917/1000000000 : ℝ)|=(539018917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390189023/10000000000 : ℝ)|^537 ≤ (22211465089023/50000000000000 : ℝ)^409
        have hw : |(5390189023/10000000000 : ℝ)|=(5390189023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_box_1 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5285081749/10000000000 : ℝ)*x 0 + (-2025411163/10000000000 : ℝ)*x 1 + (1078037811/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285081749/10000000000 : ℝ)^537 ≤ (21644542469093/50000000000000 : ℝ)^409 := by
    have hnat : (5285081749 : ℕ)^537*50000000000000^409 ≤ 21644542469093^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285081749 10000000000 21644542469093 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2025411163/10000000000 : ℝ)^537 ≤ (6143992255409/50000000000000 : ℝ)^409 := by
    have hnat : (2025411163 : ℕ)^537*50000000000000^409 ≤ 6143992255409^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025411163 10000000000 6143992255409 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078037811/2000000000 : ℝ)^537 ≤ (11105732631077/25000000000000 : ℝ)^409 := by
    have hnat : (1078037811 : ℕ)^537*25000000000000^409 ≤ 11105732631077^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078037811 2000000000 11105732631077 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285081749/10000000000 : ℝ), (-2025411163/10000000000 : ℝ), (1078037811/2000000000 : ℝ)] ![(21644542469093/50000000000000 : ℝ), (6143992255409/50000000000000 : ℝ), (11105732631077/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285081749/10000000000 : ℝ)|^537 ≤ (21644542469093/50000000000000 : ℝ)^409
        have hw : |(5285081749/10000000000 : ℝ)|=(5285081749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2025411163/10000000000 : ℝ)|^537 ≤ (6143992255409/50000000000000 : ℝ)^409
        have hw : |(-2025411163/10000000000 : ℝ)|=(2025411163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078037811/2000000000 : ℝ)|^537 ≤ (11105732631077/25000000000000 : ℝ)^409
        have hw : |(1078037811/2000000000 : ℝ)|=(1078037811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_box_2 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1321270383/2500000000 : ℝ)*x 0 + (673773657/1250000000 : ℝ)*x 1 + (-126588199/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321270383/2500000000 : ℝ)^537 ≤ (43289082604527/100000000000000 : ℝ)^409 := by
    have hnat : (1321270383 : ℕ)^537*100000000000000^409 ≤ 43289082604527^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321270383 2500000000 43289082604527 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673773657/1250000000 : ℝ)^537 ≤ (44422932699263/100000000000000 : ℝ)^409 := by
    have hnat : (673773657 : ℕ)^537*100000000000000^409 ≤ 44422932699263^409*1250000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673773657 1250000000 44422932699263 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126588199/625000000 : ℝ)^537 ≤ (767999042381/6250000000000 : ℝ)^409 := by
    have hnat : (126588199 : ℕ)^537*6250000000000^409 ≤ 767999042381^409*625000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126588199 625000000 767999042381 6250000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321270383/2500000000 : ℝ), (673773657/1250000000 : ℝ), (-126588199/625000000 : ℝ)] ![(43289082604527/100000000000000 : ℝ), (44422932699263/100000000000000 : ℝ), (767999042381/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321270383/2500000000 : ℝ)|^537 ≤ (43289082604527/100000000000000 : ℝ)^409
        have hw : |(1321270383/2500000000 : ℝ)|=(1321270383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673773657/1250000000 : ℝ)|^537 ≤ (44422932699263/100000000000000 : ℝ)^409
        have hw : |(673773657/1250000000 : ℝ)|=(673773657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-126588199/625000000 : ℝ)|^537 ≤ (767999042381/6250000000000 : ℝ)^409
        have hw : |(-126588199/625000000 : ℝ)|=(126588199/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_box_3 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (895304181/2000000000 : ℝ)*x 0 + (2128966117/5000000000 : ℝ)*x 1 + (212896623/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (895304181/2000000000 : ℝ)^537 ≤ (17404820272199/50000000000000 : ℝ)^409 := by
    have hnat : (895304181 : ℕ)^537*50000000000000^409 ≤ 17404820272199^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895304181 2000000000 17404820272199 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2128966117/5000000000 : ℝ)^537 ≤ (6519035716571/20000000000000 : ℝ)^409 := by
    have hnat : (2128966117 : ℕ)^537*20000000000000^409 ≤ 6519035716571^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128966117 5000000000 6519035716571 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212896623/500000000 : ℝ)^537 ≤ (16297590427181/50000000000000 : ℝ)^409 := by
    have hnat : (212896623 : ℕ)^537*50000000000000^409 ≤ 16297590427181^409*500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212896623 500000000 16297590427181 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(895304181/2000000000 : ℝ), (2128966117/5000000000 : ℝ), (212896623/500000000 : ℝ)] ![(17404820272199/50000000000000 : ℝ), (6519035716571/20000000000000 : ℝ), (16297590427181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(895304181/2000000000 : ℝ)|^537 ≤ (17404820272199/50000000000000 : ℝ)^409
        have hw : |(895304181/2000000000 : ℝ)|=(895304181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2128966117/5000000000 : ℝ)|^537 ≤ (6519035716571/20000000000000 : ℝ)^409
        have hw : |(2128966117/5000000000 : ℝ)|=(2128966117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(212896623/500000000 : ℝ)|^537 ≤ (16297590427181/50000000000000 : ℝ)^409
        have hw : |(212896623/500000000 : ℝ)|=(212896623/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_box_4 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2219650479/10000000000 : ℝ)*x 0 + (2632396711/5000000000 : ℝ)*x 1 + (5264792631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2219650479/10000000000 : ℝ)^537 ≤ (13857945277543/100000000000000 : ℝ)^409 := by
    have hnat : (2219650479 : ℕ)^537*100000000000000^409 ≤ 13857945277543^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219650479 10000000000 13857945277543 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632396711/5000000000 : ℝ)^537 ≤ (43071031607377/100000000000000 : ℝ)^409 := by
    have hnat : (2632396711 : ℕ)^537*100000000000000^409 ≤ 43071031607377^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632396711 5000000000 43071031607377 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264792631/10000000000 : ℝ)^537 ≤ (43071023111047/100000000000000 : ℝ)^409 := by
    have hnat : (5264792631 : ℕ)^537*100000000000000^409 ≤ 43071023111047^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264792631 10000000000 43071023111047 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2219650479/10000000000 : ℝ), (2632396711/5000000000 : ℝ), (5264792631/10000000000 : ℝ)] ![(13857945277543/100000000000000 : ℝ), (43071031607377/100000000000000 : ℝ), (43071023111047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2219650479/10000000000 : ℝ)|^537 ≤ (13857945277543/100000000000000 : ℝ)^409
        have hw : |(-2219650479/10000000000 : ℝ)|=(2219650479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632396711/5000000000 : ℝ)|^537 ≤ (43071031607377/100000000000000 : ℝ)^409
        have hw : |(2632396711/5000000000 : ℝ)|=(2632396711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264792631/10000000000 : ℝ)|^537 ≤ (43071023111047/100000000000000 : ℝ)^409
        have hw : |(5264792631/10000000000 : ℝ)|=(5264792631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_box_5 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5373180191/10000000000 : ℝ)*x 0 + (-1037842611/5000000000 : ℝ)*x 1 + (5264793427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373180191/10000000000 : ℝ)^537 ≤ (1382467942177/3125000000000 : ℝ)^409 := by
    have hnat : (5373180191 : ℕ)^537*3125000000000^409 ≤ 1382467942177^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373180191 10000000000 1382467942177 3125000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037842611/5000000000 : ℝ)^537 ≤ (1586249272073/12500000000000 : ℝ)^409 := by
    have hnat : (1037842611 : ℕ)^537*12500000000000^409 ≤ 1586249272073^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037842611 5000000000 1586249272073 12500000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264793427/10000000000 : ℝ)^537 ≤ (43071031661083/100000000000000 : ℝ)^409 := by
    have hnat : (5264793427 : ℕ)^537*100000000000000^409 ≤ 43071031661083^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264793427 10000000000 43071031661083 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373180191/10000000000 : ℝ), (-1037842611/5000000000 : ℝ), (5264793427/10000000000 : ℝ)] ![(1382467942177/3125000000000 : ℝ), (1586249272073/12500000000000 : ℝ), (43071031661083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373180191/10000000000 : ℝ)|^537 ≤ (1382467942177/3125000000000 : ℝ)^409
        have hw : |(5373180191/10000000000 : ℝ)|=(5373180191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1037842611/5000000000 : ℝ)|^537 ≤ (1586249272073/12500000000000 : ℝ)^409
        have hw : |(-1037842611/5000000000 : ℝ)|=(1037842611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264793427/10000000000 : ℝ)|^537 ≤ (43071031661083/100000000000000 : ℝ)^409
        have hw : |(5264793427/10000000000 : ℝ)|=(5264793427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_box_6 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1343294693/2500000000 : ℝ)*x 0 + (5264794167/10000000000 : ℝ)*x 1 + (-1037843071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343294693/2500000000 : ℝ)^537 ≤ (5529869851289/12500000000000 : ℝ)^409 := by
    have hnat : (1343294693 : ℕ)^537*12500000000000^409 ≤ 5529869851289^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343294693 2500000000 5529869851289 12500000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264794167/10000000000 : ℝ)^537 ≤ (4307103960961/10000000000000 : ℝ)^409 := by
    have hnat : (5264794167 : ℕ)^537*10000000000000^409 ≤ 4307103960961^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264794167 10000000000 4307103960961 10000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037843071/5000000000 : ℝ)^537 ≤ (2538000312277/20000000000000 : ℝ)^409 := by
    have hnat : (1037843071 : ℕ)^537*20000000000000^409 ≤ 2538000312277^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037843071 5000000000 2538000312277 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343294693/2500000000 : ℝ), (5264794167/10000000000 : ℝ), (-1037843071/5000000000 : ℝ)] ![(5529869851289/12500000000000 : ℝ), (4307103960961/10000000000000 : ℝ), (2538000312277/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343294693/2500000000 : ℝ)|^537 ≤ (5529869851289/12500000000000 : ℝ)^409
        have hw : |(1343294693/2500000000 : ℝ)|=(1343294693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264794167/10000000000 : ℝ)|^537 ≤ (4307103960961/10000000000000 : ℝ)^409
        have hw : |(5264794167/10000000000 : ℝ)|=(5264794167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1037843071/5000000000 : ℝ)|^537 ≤ (2538000312277/20000000000000 : ℝ)^409
        have hw : |(-1037843071/5000000000 : ℝ)|=(1037843071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_box_7 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (835789861/2000000000 : ℝ)*x 0 + (4406664751/10000000000 : ℝ)*x 1 + (2203331977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835789861/2000000000 : ℝ)^537 ≤ (31803642000607/100000000000000 : ℝ)^409 := by
    have hnat : (835789861 : ℕ)^537*100000000000000^409 ≤ 31803642000607^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835789861 2000000000 31803642000607 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4406664751/10000000000 : ℝ)^537 ≤ (6819636608447/20000000000000 : ℝ)^409 := by
    have hnat : (4406664751 : ℕ)^537*20000000000000^409 ≤ 6819636608447^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4406664751 10000000000 6819636608447 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2203331977/5000000000 : ℝ)^537 ≤ (8524543736279/25000000000000 : ℝ)^409 := by
    have hnat : (2203331977 : ℕ)^537*25000000000000^409 ≤ 8524543736279^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203331977 5000000000 8524543736279 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(835789861/2000000000 : ℝ), (4406664751/10000000000 : ℝ), (2203331977/5000000000 : ℝ)] ![(31803642000607/100000000000000 : ℝ), (6819636608447/20000000000000 : ℝ), (8524543736279/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(835789861/2000000000 : ℝ)|^537 ≤ (31803642000607/100000000000000 : ℝ)^409
        have hw : |(835789861/2000000000 : ℝ)|=(835789861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4406664751/10000000000 : ℝ)|^537 ≤ (6819636608447/20000000000000 : ℝ)^409
        have hw : |(4406664751/10000000000 : ℝ)|=(4406664751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2203331977/5000000000 : ℝ)|^537 ≤ (8524543736279/25000000000000 : ℝ)^409
        have hw : |(2203331977/5000000000 : ℝ)|=(2203331977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_box_8 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2148642517/10000000000 : ℝ)*x 0 + (5178495271/10000000000 : ℝ)*x 1 + (2702105423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148642517/10000000000 : ℝ)^537 ≤ (829925912729/6250000000000 : ℝ)^409 := by
    have hnat : (2148642517 : ℕ)^537*6250000000000^409 ≤ 829925912729^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148642517 10000000000 829925912729 6250000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178495271/10000000000 : ℝ)^537 ≤ (4214646795453/10000000000000 : ℝ)^409 := by
    have hnat : (5178495271 : ℕ)^537*10000000000000^409 ≤ 4214646795453^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178495271 10000000000 4214646795453 10000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702105423/5000000000 : ℝ)^537 ≤ (44574717433013/100000000000000 : ℝ)^409 := by
    have hnat : (2702105423 : ℕ)^537*100000000000000^409 ≤ 44574717433013^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702105423 5000000000 44574717433013 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2148642517/10000000000 : ℝ), (5178495271/10000000000 : ℝ), (2702105423/5000000000 : ℝ)] ![(829925912729/6250000000000 : ℝ), (4214646795453/10000000000000 : ℝ), (44574717433013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2148642517/10000000000 : ℝ)|^537 ≤ (829925912729/6250000000000 : ℝ)^409
        have hw : |(-2148642517/10000000000 : ℝ)|=(2148642517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178495271/10000000000 : ℝ)|^537 ≤ (4214646795453/10000000000000 : ℝ)^409
        have hw : |(5178495271/10000000000 : ℝ)|=(5178495271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702105423/5000000000 : ℝ)|^537 ≤ (44574717433013/100000000000000 : ℝ)^409
        have hw : |(2702105423/5000000000 : ℝ)|=(2702105423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_box_9 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2637612649/5000000000 : ℝ)*x 0 + (-504914151/2500000000 : ℝ)*x 1 + (5404210699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637612649/5000000000 : ℝ)^537 ≤ (21591558872673/50000000000000 : ℝ)^409 := by
    have hnat : (2637612649 : ℕ)^537*50000000000000^409 ≤ 21591558872673^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637612649 5000000000 21591558872673 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504914151/2500000000 : ℝ)^537 ≤ (765135399653/6250000000000 : ℝ)^409 := by
    have hnat : (504914151 : ℕ)^537*6250000000000^409 ≤ 765135399653^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504914151 2500000000 765135399653 6250000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404210699/10000000000 : ℝ)^537 ≤ (1114367896027/2500000000000 : ℝ)^409 := by
    have hnat : (5404210699 : ℕ)^537*2500000000000^409 ≤ 1114367896027^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404210699 10000000000 1114367896027 2500000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637612649/5000000000 : ℝ), (-504914151/2500000000 : ℝ), (5404210699/10000000000 : ℝ)] ![(21591558872673/50000000000000 : ℝ), (765135399653/6250000000000 : ℝ), (1114367896027/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637612649/5000000000 : ℝ)|^537 ≤ (21591558872673/50000000000000 : ℝ)^409
        have hw : |(2637612649/5000000000 : ℝ)|=(2637612649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-504914151/2500000000 : ℝ)|^537 ≤ (765135399653/6250000000000 : ℝ)^409
        have hw : |(-504914151/2500000000 : ℝ)|=(504914151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404210699/10000000000 : ℝ)|^537 ≤ (1114367896027/2500000000000 : ℝ)^409
        have hw : |(5404210699/10000000000 : ℝ)|=(5404210699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_box_10 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (659403121/1250000000 : ℝ)*x 0 + (5404211063/10000000000 : ℝ)*x 1 + (-403931311/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659403121/1250000000 : ℝ)^537 ≤ (5397889274817/12500000000000 : ℝ)^409 := by
    have hnat : (659403121 : ℕ)^537*12500000000000^409 ≤ 5397889274817^409*1250000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659403121 1250000000 5397889274817 12500000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404211063/10000000000 : ℝ)^537 ≤ (1392959993219/3125000000000 : ℝ)^409 := by
    have hnat : (5404211063 : ℕ)^537*3125000000000^409 ≤ 1392959993219^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404211063 10000000000 1392959993219 3125000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403931311/2000000000 : ℝ)^537 ≤ (12242166004481/100000000000000 : ℝ)^409 := by
    have hnat : (403931311 : ℕ)^537*100000000000000^409 ≤ 12242166004481^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403931311 2000000000 12242166004481 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659403121/1250000000 : ℝ), (5404211063/10000000000 : ℝ), (-403931311/2000000000 : ℝ)] ![(5397889274817/12500000000000 : ℝ), (1392959993219/3125000000000 : ℝ), (12242166004481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659403121/1250000000 : ℝ)|^537 ≤ (5397889274817/12500000000000 : ℝ)^409
        have hw : |(659403121/1250000000 : ℝ)|=(659403121/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404211063/10000000000 : ℝ)|^537 ≤ (1392959993219/3125000000000 : ℝ)^409
        have hw : |(5404211063/10000000000 : ℝ)|=(5404211063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-403931311/2000000000 : ℝ)|^537 ≤ (12242166004481/100000000000000 : ℝ)^409
        have hw : |(-403931311/2000000000 : ℝ)|=(403931311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_box_11 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (901847303/2000000000 : ℝ)*x 0 + (4241286933/10000000000 : ℝ)*x 1 + (4241287221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (901847303/2000000000 : ℝ)^537 ≤ (3514403607629/10000000000000 : ℝ)^409 := by
    have hnat : (901847303 : ℕ)^537*10000000000000^409 ≤ 3514403607629^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901847303 2000000000 3514403607629 10000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4241286933/10000000000 : ℝ)^537 ≤ (8106995127651/25000000000000 : ℝ)^409 := by
    have hnat : (4241286933 : ℕ)^537*25000000000000^409 ≤ 8106995127651^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241286933 10000000000 8106995127651 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241287221/10000000000 : ℝ)^537 ≤ (32427983401721/100000000000000 : ℝ)^409 := by
    have hnat : (4241287221 : ℕ)^537*100000000000000^409 ≤ 32427983401721^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241287221 10000000000 32427983401721 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(901847303/2000000000 : ℝ), (4241286933/10000000000 : ℝ), (4241287221/10000000000 : ℝ)] ![(3514403607629/10000000000000 : ℝ), (8106995127651/25000000000000 : ℝ), (32427983401721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(901847303/2000000000 : ℝ)|^537 ≤ (3514403607629/10000000000000 : ℝ)^409
        have hw : |(901847303/2000000000 : ℝ)|=(901847303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4241286933/10000000000 : ℝ)|^537 ≤ (8106995127651/25000000000000 : ℝ)^409
        have hw : |(4241286933/10000000000 : ℝ)|=(4241286933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241287221/10000000000 : ℝ)|^537 ≤ (32427983401721/100000000000000 : ℝ)^409
        have hw : |(4241287221/10000000000 : ℝ)|=(4241287221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_box_12 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1952796589/10000000000 : ℝ)*x 0 + (684283523/1250000000 : ℝ)*x 1 + (525372911/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1952796589/10000000000 : ℝ)^537 ≤ (1464104744427/12500000000000 : ℝ)^409 := by
    have hnat : (1952796589 : ℕ)^537*12500000000000^409 ≤ 1464104744427^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952796589 10000000000 1464104744427 12500000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (684283523/1250000000 : ℝ)^537 ≤ (9066987177181/20000000000000 : ℝ)^409 := by
    have hnat : (684283523 : ℕ)^537*20000000000000^409 ≤ 9066987177181^409*1250000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684283523 1250000000 9066987177181 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525372911/1000000000 : ℝ)^537 ≤ (21476113071047/50000000000000 : ℝ)^409 := by
    have hnat : (525372911 : ℕ)^537*50000000000000^409 ≤ 21476113071047^409*1000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525372911 1000000000 21476113071047 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1952796589/10000000000 : ℝ), (684283523/1250000000 : ℝ), (525372911/1000000000 : ℝ)] ![(1464104744427/12500000000000 : ℝ), (9066987177181/20000000000000 : ℝ), (21476113071047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1952796589/10000000000 : ℝ)|^537 ≤ (1464104744427/12500000000000 : ℝ)^409
        have hw : |(-1952796589/10000000000 : ℝ)|=(1952796589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(684283523/1250000000 : ℝ)|^537 ≤ (9066987177181/20000000000000 : ℝ)^409
        have hw : |(684283523/1250000000 : ℝ)|=(684283523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525372911/1000000000 : ℝ)|^537 ≤ (21476113071047/50000000000000 : ℝ)^409
        have hw : |(525372911/1000000000 : ℝ)|=(525372911/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_box_13 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5380950403/10000000000 : ℝ)*x 0 + (-520004459/2500000000 : ℝ)*x 1 + (2626864633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380950403/10000000000 : ℝ)^537 ≤ (8864597786907/20000000000000 : ℝ)^409 := by
    have hnat : (5380950403 : ℕ)^537*20000000000000^409 ≤ 8864597786907^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380950403 10000000000 8864597786907 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520004459/2500000000 : ℝ)^537 ≤ (6362391617121/50000000000000 : ℝ)^409 := by
    have hnat : (520004459 : ℕ)^537*50000000000000^409 ≤ 6362391617121^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520004459 2500000000 6362391617121 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626864633/5000000000 : ℝ)^537 ≤ (21476113908313/50000000000000 : ℝ)^409 := by
    have hnat : (2626864633 : ℕ)^537*50000000000000^409 ≤ 21476113908313^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626864633 5000000000 21476113908313 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380950403/10000000000 : ℝ), (-520004459/2500000000 : ℝ), (2626864633/5000000000 : ℝ)] ![(8864597786907/20000000000000 : ℝ), (6362391617121/50000000000000 : ℝ), (21476113908313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380950403/10000000000 : ℝ)|^537 ≤ (8864597786907/20000000000000 : ℝ)^409
        have hw : |(5380950403/10000000000 : ℝ)|=(5380950403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-520004459/2500000000 : ℝ)|^537 ≤ (6362391617121/50000000000000 : ℝ)^409
        have hw : |(-520004459/2500000000 : ℝ)|=(520004459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626864633/5000000000 : ℝ)|^537 ≤ (21476113908313/50000000000000 : ℝ)^409
        have hw : |(2626864633/5000000000 : ℝ)|=(2626864633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_box_14 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5380950309/10000000000 : ℝ)*x 0 + (5253729101/10000000000 : ℝ)*x 1 + (-260002273/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380950309/10000000000 : ℝ)^537 ≤ (22161493958969/50000000000000 : ℝ)^409 := by
    have hnat : (5380950309 : ℕ)^537*50000000000000^409 ≤ 22161493958969^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380950309 10000000000 22161493958969 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253729101/10000000000 : ℝ)^537 ≤ (21476113022743/50000000000000 : ℝ)^409 := by
    have hnat : (5253729101 : ℕ)^537*50000000000000^409 ≤ 21476113022743^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253729101 10000000000 21476113022743 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260002273/1250000000 : ℝ)^537 ≤ (6362393014723/50000000000000 : ℝ)^409 := by
    have hnat : (260002273 : ℕ)^537*50000000000000^409 ≤ 6362393014723^409*1250000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260002273 1250000000 6362393014723 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380950309/10000000000 : ℝ), (5253729101/10000000000 : ℝ), (-260002273/1250000000 : ℝ)] ![(22161493958969/50000000000000 : ℝ), (21476113022743/50000000000000 : ℝ), (6362393014723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380950309/10000000000 : ℝ)|^537 ≤ (22161493958969/50000000000000 : ℝ)^409
        have hw : |(5380950309/10000000000 : ℝ)|=(5380950309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253729101/10000000000 : ℝ)|^537 ≤ (21476113022743/50000000000000 : ℝ)^409
        have hw : |(5253729101/10000000000 : ℝ)|=(5253729101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-260002273/1250000000 : ℝ)|^537 ≤ (6362393014723/50000000000000 : ℝ)^409
        have hw : |(-260002273/1250000000 : ℝ)|=(260002273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_box_15 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4152245663/10000000000 : ℝ)*x 0 + (4419777053/10000000000 : ℝ)*x 1 + (2209888519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4152245663/10000000000 : ℝ)^537 ≤ (6307416260329/20000000000000 : ℝ)^409 := by
    have hnat : (4152245663 : ℕ)^537*20000000000000^409 ≤ 6307416260329^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152245663 10000000000 6307416260329 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4419777053/10000000000 : ℝ)^537 ≤ (17115729709241/50000000000000 : ℝ)^409 := by
    have hnat : (4419777053 : ℕ)^537*50000000000000^409 ≤ 17115729709241^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4419777053 10000000000 17115729709241 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2209888519/5000000000 : ℝ)^537 ≤ (34231459265947/100000000000000 : ℝ)^409 := by
    have hnat : (2209888519 : ℕ)^537*100000000000000^409 ≤ 34231459265947^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209888519 5000000000 34231459265947 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4152245663/10000000000 : ℝ), (4419777053/10000000000 : ℝ), (2209888519/5000000000 : ℝ)] ![(6307416260329/20000000000000 : ℝ), (17115729709241/50000000000000 : ℝ), (34231459265947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4152245663/10000000000 : ℝ)|^537 ≤ (6307416260329/20000000000000 : ℝ)^409
        have hw : |(4152245663/10000000000 : ℝ)|=(4152245663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4419777053/10000000000 : ℝ)|^537 ≤ (17115729709241/50000000000000 : ℝ)^409
        have hw : |(4419777053/10000000000 : ℝ)|=(4419777053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2209888519/5000000000 : ℝ)|^537 ≤ (34231459265947/100000000000000 : ℝ)^409
        have hw : |(2209888519/5000000000 : ℝ)|=(2209888519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1336_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (348/3125 : ℝ)*pair X i i ≤ pair X i h) :
    -(62853/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5893/10000 : ℝ) ∧ (79919/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84329/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7351/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (348/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7351/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (348/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7351/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (348/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7351/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (348/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7351/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (348/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7351/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (348/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (348/3125 : ℝ) ^ (4295/1024 : ℝ) ≤ (250958625725239/2500000000000000000 : ℝ) := by
    have hpowers : (348/3125 : ℝ)^4295 ≤ (250958625725239/2500000000000000000 : ℝ)^1024 := by
      have hnat : (348 : ℕ)^4295*2500000000000000000^1024 ≤ 250958625725239^1024*3125^4295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        348 3125 250958625725239 2500000000000000000 4295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (348/3125 : ℝ)) (X := (250958625725239/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7351/50000 : ℝ) ^ (4295/1024 : ℝ) ≤ (32188222102063781/100000000000000000000 : ℝ) := by
    have hpowers : (7351/50000 : ℝ)^4295 ≤ (32188222102063781/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7351 : ℕ)^4295*100000000000000000000^1024 ≤ 32188222102063781^1024*50000^4295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7351 50000 32188222102063781 100000000000000000000 4295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7351/50000 : ℝ)) (X := (32188222102063781/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250250958625725239/1250000000000000000 : ℝ) ≤ (500023931267867/500000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (1250250958625725239/1250000000000000000 : ℝ)^1024 ≤ (500023931267867/500000000000000 : ℝ)^4295 := by
      have hnat : (1250250958625725239 : ℕ)^1024*500000000000000^4295 ≤ 500023931267867^4295*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250250958625725239 1250000000000000000 500023931267867 500000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500023931267867/500000000000000 : ℝ)) (X := (1250250958625725239/1250000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042226567131073341/100000000000000000000 : ℝ) ≤ (10001006590306851/10000000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (100042226567131073341/100000000000000000000 : ℝ)^1024 ≤ (10001006590306851/10000000000000000 : ℝ)^4295 := by
      have hnat : (100042226567131073341 : ℕ)^1024*10000000000000000^4295 ≤ 10001006590306851^4295*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042226567131073341 100000000000000000000 10001006590306851 10000000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001006590306851/10000000000000000 : ℝ)) (X := (100042226567131073341/100000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032188222102063781/50000000000000000000 : ℝ) ≤ (5000767277628181/5000000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (50032188222102063781/50000000000000000000 : ℝ)^1024 ≤ (5000767277628181/5000000000000000 : ℝ)^4295 := by
      have hnat : (50032188222102063781 : ℕ)^1024*5000000000000000^4295 ≤ 5000767277628181^4295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032188222102063781 50000000000000000000 5000767277628181 5000000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000767277628181/5000000000000000 : ℝ)) (X := (50032188222102063781/50000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(250958625725239/2500000000000000000 : ℝ) ≤ ((4456243492833595681/4457500000000000000 : ℝ)+2*(527964949511/356600000000000 : ℝ)*(348/3125 : ℝ))^(4295/1024 : ℝ) := by
    rw [show (4456243492833595681/4457500000000000000 : ℝ)+2*(527964949511/356600000000000 : ℝ)*(348/3125 : ℝ)=(500023931267867/500000000000000 : ℝ) by norm_num, show 1+2*(250958625725239/2500000000000000000 : ℝ)=(1250250958625725239/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32188222102063781/100000000000000000000 : ℝ)+(250958625725239/2500000000000000000 : ℝ) ≤ ((4456243492833595681/4457500000000000000 : ℝ)+(527964949511/356600000000000 : ℝ)*((7351/50000 : ℝ)+(348/3125 : ℝ)))^(4295/1024 : ℝ) := by
    rw [show (4456243492833595681/4457500000000000000 : ℝ)+(527964949511/356600000000000 : ℝ)*((7351/50000 : ℝ)+(348/3125 : ℝ))=(10001006590306851/10000000000000000 : ℝ) by norm_num, show 1+(32188222102063781/100000000000000000000 : ℝ)+(250958625725239/2500000000000000000 : ℝ)=(100042226567131073341/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32188222102063781/100000000000000000000 : ℝ) ≤ ((4456243492833595681/4457500000000000000 : ℝ)+2*(527964949511/356600000000000 : ℝ)*(7351/50000 : ℝ))^(4295/1024 : ℝ) := by
    rw [show (4456243492833595681/4457500000000000000 : ℝ)+2*(527964949511/356600000000000 : ℝ)*(7351/50000 : ℝ)=(5000767277628181/5000000000000000 : ℝ) by norm_num, show 1+2*(32188222102063781/100000000000000000000 : ℝ)=(50032188222102063781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4456243492833595681/4457500000000000000 : ℝ)*(X 1 0+X 2 0)+(527964949511/356600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (348/3125 : ℝ)) (hi := (7351/50000 : ℝ)) (c := (4456243492833595681/4457500000000000000 : ℝ)) (alpha := (527964949511/356600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4456243492833595681/4457500000000000000 : ℝ)*(X 0 1+X 2 1)+(527964949511/356600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (348/3125 : ℝ)) (hi := (7351/50000 : ℝ)) (c := (4456243492833595681/4457500000000000000 : ℝ)) (alpha := (527964949511/356600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4456243492833595681/4457500000000000000 : ℝ)*(X 0 2+X 1 2)+(527964949511/356600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (348/3125 : ℝ)) (hi := (7351/50000 : ℝ)) (c := (4456243492833595681/4457500000000000000 : ℝ)) (alpha := (527964949511/356600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1881439999/10000000000 : ℝ)*X 0 0+(539018917/1000000000 : ℝ)*X 0 1+(5390189023/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285081749/10000000000 : ℝ)*X 1 0+(-2025411163/10000000000 : ℝ)*X 1 1+(1078037811/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1321270383/2500000000 : ℝ)*X 2 0+(673773657/1250000000 : ℝ)*X 2 1+(-126588199/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((895304181/2000000000 : ℝ)*X 0 0+(2128966117/5000000000 : ℝ)*X 0 1+(212896623/500000000 : ℝ)*X 0 2+(895304181/2000000000 : ℝ)*X 1 0+(2128966117/5000000000 : ℝ)*X 1 1+(212896623/500000000 : ℝ)*X 1 2+(895304181/2000000000 : ℝ)*X 2 0+(2128966117/5000000000 : ℝ)*X 2 1+(212896623/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2219650479/10000000000 : ℝ)*X 0 0+(2632396711/5000000000 : ℝ)*X 0 1+(5264792631/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5373180191/10000000000 : ℝ)*X 1 0+(-1037842611/5000000000 : ℝ)*X 1 1+(5264793427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1343294693/2500000000 : ℝ)*X 2 0+(5264794167/10000000000 : ℝ)*X 2 1+(-1037843071/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((835789861/2000000000 : ℝ)*X 0 0+(4406664751/10000000000 : ℝ)*X 0 1+(2203331977/5000000000 : ℝ)*X 0 2+(835789861/2000000000 : ℝ)*X 1 0+(4406664751/10000000000 : ℝ)*X 1 1+(2203331977/5000000000 : ℝ)*X 1 2+(835789861/2000000000 : ℝ)*X 2 0+(4406664751/10000000000 : ℝ)*X 2 1+(2203331977/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2148642517/10000000000 : ℝ)*X 0 0+(5178495271/10000000000 : ℝ)*X 0 1+(2702105423/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2637612649/5000000000 : ℝ)*X 1 0+(-504914151/2500000000 : ℝ)*X 1 1+(5404210699/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((659403121/1250000000 : ℝ)*X 2 0+(5404211063/10000000000 : ℝ)*X 2 1+(-403931311/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((901847303/2000000000 : ℝ)*X 0 0+(4241286933/10000000000 : ℝ)*X 0 1+(4241287221/10000000000 : ℝ)*X 0 2+(901847303/2000000000 : ℝ)*X 1 0+(4241286933/10000000000 : ℝ)*X 1 1+(4241287221/10000000000 : ℝ)*X 1 2+(901847303/2000000000 : ℝ)*X 2 0+(4241286933/10000000000 : ℝ)*X 2 1+(4241287221/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1952796589/10000000000 : ℝ)*X 0 0+(684283523/1250000000 : ℝ)*X 0 1+(525372911/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5380950403/10000000000 : ℝ)*X 1 0+(-520004459/2500000000 : ℝ)*X 1 1+(2626864633/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5380950309/10000000000 : ℝ)*X 2 0+(5253729101/10000000000 : ℝ)*X 2 1+(-260002273/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4152245663/10000000000 : ℝ)*X 0 0+(4419777053/10000000000 : ℝ)*X 0 1+(2209888519/5000000000 : ℝ)*X 0 2+(4152245663/10000000000 : ℝ)*X 1 0+(4419777053/10000000000 : ℝ)*X 1 1+(2209888519/5000000000 : ℝ)*X 1 2+(4152245663/10000000000 : ℝ)*X 2 0+(4419777053/10000000000 : ℝ)*X 2 1+(2209888519/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62853/100000 : ℝ) ≤ (-7003897192888775358733907994741/11143750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80747199/100000000000000 : ℝ)*(lower0) + (30787737/25000000000000 : ℝ)*(upper1) + (129310653/100000000000000 : ℝ)*(upper3) + (115506971/25000000000000 : ℝ)*(lower4) + (59387597/25000000000000 : ℝ)*(lower5) + (145698002689663/5000000000000 : ℝ)*(major0) + (145698002689663/5000000000000 : ℝ)*(major1) + (145698002689663/5000000000000 : ℝ)*(major2) + (99067933339701/2500000000000 : ℝ)*(sp4) + (990609451777817/25000000000000 : ℝ)*(sp5) + (198115440880473/5000000000000 : ℝ)*(sp6) + (471538231127503/25000000000000 : ℝ)*(sp7) + (279526476771/100000000000000 : ℝ)*(sp13) + (20425798929/5000000000000 : ℝ)*(sp14) + (471538231127503/25000000000000 : ℝ)*(f.failure) + (99067933339701/2500000000000 : ℝ)*(f.sum) + (3182428454043/891500000000000000000000000 : ℝ)*base65 + (72672440677108003/22287500000000000000000000000000 : ℝ)*base67 + (17306226313741997/22287500000000000000000000000000 : ℝ)*base70 + (95705175191770503/22287500000000000000000000000000 : ℝ)*base71 + (447534406547/891500000000000000000000000 : ℝ)*base74 + (6478563923816997/22287500000000000000000000000000 : ℝ)*base76 + (71756044454941997/22287500000000000000000000000000 : ℝ)*base78 + (784968467774891997/22287500000000000000000000000000 : ℝ)*base80 + (392161066439/891500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1637093/312500000000000000000 : ℝ)*base89 + (1637093/312500000000000000000 : ℝ)*base91 + (1637093/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (5893/10000 : ℝ) ≤ (131344881939912929299340900454129/222875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20202329/100000000000000 : ℝ)*(lower1) + (52694423/100000000000000 : ℝ)*(upper2) + (4720059/100000000000000 : ℝ)*(lower5) + (745617086720187/25000000000000 : ℝ)*(major0) + (745617086720187/25000000000000 : ℝ)*(major1) + (2982468346880749/100000000000000 : ℝ)*(major2) + (501849434116757/12500000000000 : ℝ)*(sp0) + (2007395113741369/50000000000000 : ℝ)*(sp1) + (1003698067501023/25000000000000 : ℝ)*(sp2) + (1930496862026677/100000000000000 : ℝ)*(sp3) + (3309057493/100000000000000 : ℝ)*(sp6) + (112357183/50000000000000 : ℝ)*(sp7) + (106127529/100000000000000 : ℝ)*(sp8) + (167236839/3125000000000 : ℝ)*(sp9) + (482624271685261/25000000000000 : ℝ)*(f.failure) + (2007397789530793/50000000000000 : ℝ)*(f.sum) + (232289861408487/35660000000000000000000000000 : ℝ)*base65 + (149541186186792111/55718750000000000000000000000000 : ℝ)*base67 + (4831170394391795069/445750000000000000000000000000000 : ℝ)*base69 + (412523689028645389/55718750000000000000000000000000 : ℝ)*base72 + (334253893001287/35660000000000000000000000000 : ℝ)*base73 + (2184449302601795069/445750000000000000000000000000000 : ℝ)*base75 + (189487690354112347/111437500000000000000000000000000 : ℝ)*base77 + (145466277085612347/111437500000000000000000000000000 : ℝ)*base79 + (12206601049341/2228750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (2544591/312500000000000000000 : ℝ)*base89 + (2544591/312500000000000000000 : ℝ)*base91 + (580409/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (79919/100000 : ℝ) ≤ (178125641483369207488404978652617/222875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (815401/4000000000000 : ℝ)*(upper0) + (6733949/10000000000000 : ℝ)*(upper2) + (8351133/50000000000000 : ℝ)*(lower3) + (164742380880581/5000000000000 : ℝ)*(major0) + (164742380880581/5000000000000 : ℝ)*(major1) + (3294847617611621/100000000000000 : ℝ)*(major2) + (32912571/1562500000000 : ℝ)*(sp0) + (80010028449/100000000000000 : ℝ)*(sp2) + (21886207109/50000000000000 : ℝ)*(sp3) + (4430355055475963/100000000000000 : ℝ)*(sp8) + (2215180091770279/50000000000000 : ℝ)*(sp9) + (1107570043378027/25000000000000 : ℝ)*(sp10) + (1066325344888791/50000000000000 : ℝ)*(sp11) + (3021660051/100000000000000 : ℝ)*(sp12) + (2132694462191799/100000000000000 : ℝ)*(f.failure) + (2215180091770279/50000000000000 : ℝ)*(f.sum) + (196715738916489/35660000000000000000000000000 : ℝ)*base66 + (50851421163214991/5571875000000000000000000000000 : ℝ)*base68 + (88503162192258901/445750000000000000000000000000000 : ℝ)*base69 + (6285357273118433/2785937500000000000000000000000 : ℝ)*base72 + (69413116755609/35660000000000000000000000000 : ℝ)*base74 + (2416107040735758901/445750000000000000000000000000000 : ℝ)*base75 + (55199160881191839/22287500000000000000000000000000 : ℝ)*base78 + (289805929437716839/22287500000000000000000000000000 : ℝ)*base80 + (58401494587/13929687500000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (4334269/1250000000000000000000 : ℝ)*base89 + (4334269/1250000000000000000000 : ℝ)*base91 + (8165731/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-84329/100000 : ℝ) ≤ (-23492716225361149322748093353397/27859375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54253887/100000000000000 : ℝ)*(lower0) + (24152573/50000000000000 : ℝ)*(upper3) + (29505373/20000000000000 : ℝ)*(lower4) + (832812710485921/25000000000000 : ℝ)*(major0) + (832812710485921/25000000000000 : ℝ)*(major1) + (832812710485921/25000000000000 : ℝ)*(major2) + (3251522857/100000000000000 : ℝ)*(sp4) + (134984807011/100000000000000 : ℝ)*(sp6) + (6592749243/10000000000000 : ℝ)*(sp7) + (625771203/50000000000000 : ℝ)*(sp8) + (4534348269051983/100000000000000 : ℝ)*(sp12) + (2267176386058623/50000000000000 : ℝ)*(sp13) + (2267108893655117/50000000000000 : ℝ)*(sp14) + (215619167447067/10000000000000 : ℝ)*(sp15) + (2156257601963099/100000000000000 : ℝ)*(f.failure) + (2267176386058623/50000000000000 : ℝ)*(f.sum) + (143367430689771/4457500000000000000000000000 : ℝ)*base65 + (487021839768705299/111437500000000000000000000000000 : ℝ)*base68 + (247273314628892799/111437500000000000000000000000000 : ℝ)*base70 + (6678551213781419701/111437500000000000000000000000000 : ℝ)*base71 + (277821314951/4457500000000000000000000000 : ℝ)*base73 + (1039303540524455299/111437500000000000000000000000000 : ℝ)*base76 + (221233391392330299/111437500000000000000000000000000 : ℝ)*base78 + (229847148304767799/111437500000000000000000000000000 : ℝ)*base80 + (2955120947117/2228750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2805431/1250000000000000000000 : ℝ)*base90 + (2805431/1250000000000000000000 : ℝ)*base92 + (2805431/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1336_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (348/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62853/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5893/10000 : ℝ) else (79919/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84329/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1336_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1336_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11127/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62853/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5893/10000 : ℝ) else (79919/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84329/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1336_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1336_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1336_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1839/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11127/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62853/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5893/10000 : ℝ) else (79919/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84329/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1336_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p002_b032
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:13:51.119086+00:00
-- url     : https://prove2.me/submissions/56ba5904-cee7-464d-aa9d-5fcf72726927

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c302077_s0_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-140009803/250000000 : ℝ)*x 0 + (940412743/2500000000 : ℝ)*x 1 + (3628050657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140009803/250000000 : ℝ)^131 ≤ (5804228601621/12500000000000 : ℝ)^99 := by
    have hnat : (140009803 : ℕ)^131*12500000000000^99 ≤ 5804228601621^99*250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140009803 250000000 5804228601621 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (940412743/2500000000 : ℝ)^131 ≤ (13711883225993/50000000000000 : ℝ)^99 := by
    have hnat : (940412743 : ℕ)^131*50000000000000^99 ≤ 13711883225993^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940412743 2500000000 13711883225993 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3628050657/10000000000 : ℝ)^131 ≤ (26142404715199/100000000000000 : ℝ)^99 := by
    have hnat : (3628050657 : ℕ)^131*100000000000000^99 ≤ 26142404715199^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3628050657 10000000000 26142404715199 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-140009803/250000000 : ℝ), (940412743/2500000000 : ℝ), (3628050657/10000000000 : ℝ)] ![(5804228601621/12500000000000 : ℝ), (13711883225993/50000000000000 : ℝ), (26142404715199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-140009803/250000000 : ℝ)|^131 ≤ (5804228601621/12500000000000 : ℝ)^99
        have hw : |(-140009803/250000000 : ℝ)|=(140009803/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(940412743/2500000000 : ℝ)|^131 ≤ (13711883225993/50000000000000 : ℝ)^99
        have hw : |(940412743/2500000000 : ℝ)|=(940412743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3628050657/10000000000 : ℝ)|^131 ≤ (26142404715199/100000000000000 : ℝ)^99
        have hw : |(3628050657/10000000000 : ℝ)|=(3628050657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s0_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2272029493/5000000000 : ℝ)*x 0 + (2732762163/5000000000 : ℝ)*x 1 + (-735934013/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2272029493/5000000000 : ℝ)^131 ≤ (35214276966847/100000000000000 : ℝ)^99 := by
    have hnat : (2272029493 : ℕ)^131*100000000000000^99 ≤ 35214276966847^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272029493 5000000000 35214276966847 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732762163/5000000000 : ℝ)^131 ≤ (22479982216121/50000000000000 : ℝ)^99 := by
    have hnat : (2732762163 : ℕ)^131*50000000000000^99 ≤ 22479982216121^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732762163 5000000000 22479982216121 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (735934013/2500000000 : ℝ)^131 ≤ (396515171679/2000000000000 : ℝ)^99 := by
    have hnat : (735934013 : ℕ)^131*2000000000000^99 ≤ 396515171679^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      735934013 2500000000 396515171679 2000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2272029493/5000000000 : ℝ), (2732762163/5000000000 : ℝ), (-735934013/2500000000 : ℝ)] ![(35214276966847/100000000000000 : ℝ), (22479982216121/50000000000000 : ℝ), (396515171679/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2272029493/5000000000 : ℝ)|^131 ≤ (35214276966847/100000000000000 : ℝ)^99
        have hw : |(2272029493/5000000000 : ℝ)|=(2272029493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732762163/5000000000 : ℝ)|^131 ≤ (22479982216121/50000000000000 : ℝ)^99
        have hw : |(2732762163/5000000000 : ℝ)|=(2732762163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-735934013/2500000000 : ℝ)|^131 ≤ (396515171679/2000000000000 : ℝ)^99
        have hw : |(-735934013/2500000000 : ℝ)|=(735934013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s0_4 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (1 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^131 ≤ (0 : ℝ)^99 := by
    have hnat : (0 : ℕ)^131*1^99 ≤ 0^99*1^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1 : ℝ)^131 ≤ (1 : ℝ)^99 := by
    have hnat : (1 : ℕ)^131*1^99 ≤ 1^99*1^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^131 ≤ (0 : ℝ)^99 := by
    have hnat : (0 : ℕ)^131*1^99 ≤ 0^99*1^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^131 ≤ (0 : ℝ)^99
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1 : ℝ)|^131 ≤ (1 : ℝ)^99
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^131 ≤ (0 : ℝ)^99
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s0_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (425397569/2000000000 : ℝ)*x 0 + (6830561663/10000000000 : ℝ)*x 1 + (1844014481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425397569/2000000000 : ℝ)^131 ≤ (3224162619631/25000000000000 : ℝ)^99 := by
    have hnat : (425397569 : ℕ)^131*25000000000000^99 ≤ 3224162619631^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425397569 2000000000 3224162619631 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6830561663/10000000000 : ℝ)^131 ≤ (3774221605999/6250000000000 : ℝ)^99 := by
    have hnat : (6830561663 : ℕ)^131*6250000000000^99 ≤ 3774221605999^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6830561663 10000000000 3774221605999 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1844014481/5000000000 : ℝ)^131 ≤ (2671580380567/10000000000000 : ℝ)^99 := by
    have hnat : (1844014481 : ℕ)^131*10000000000000^99 ≤ 2671580380567^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844014481 5000000000 2671580380567 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(425397569/2000000000 : ℝ), (6830561663/10000000000 : ℝ), (1844014481/5000000000 : ℝ)] ![(3224162619631/25000000000000 : ℝ), (3774221605999/6250000000000 : ℝ), (2671580380567/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(425397569/2000000000 : ℝ)|^131 ≤ (3224162619631/25000000000000 : ℝ)^99
        have hw : |(425397569/2000000000 : ℝ)|=(425397569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6830561663/10000000000 : ℝ)|^131 ≤ (3774221605999/6250000000000 : ℝ)^99
        have hw : |(6830561663/10000000000 : ℝ)|=(6830561663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1844014481/5000000000 : ℝ)|^131 ≤ (2671580380567/10000000000000 : ℝ)^99
        have hw : |(1844014481/5000000000 : ℝ)|=(1844014481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s0_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-5789802919/10000000000 : ℝ)*x 0 + (104023977/312500000 : ℝ)*x 1 + (1918307319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5789802919/10000000000 : ℝ)^131 ≤ (48523156367209/100000000000000 : ℝ)^99 := by
    have hnat : (5789802919 : ℕ)^131*100000000000000^99 ≤ 48523156367209^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5789802919 10000000000 48523156367209 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104023977/312500000 : ℝ)^131 ≤ (5831899138409/25000000000000 : ℝ)^99 := by
    have hnat : (104023977 : ℕ)^131*25000000000000^99 ≤ 5831899138409^99*312500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104023977 312500000 5831899138409 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1918307319/5000000000 : ℝ)^131 ≤ (28149247068317/100000000000000 : ℝ)^99 := by
    have hnat : (1918307319 : ℕ)^131*100000000000000^99 ≤ 28149247068317^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1918307319 5000000000 28149247068317 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5789802919/10000000000 : ℝ), (104023977/312500000 : ℝ), (1918307319/5000000000 : ℝ)] ![(48523156367209/100000000000000 : ℝ), (5831899138409/25000000000000 : ℝ), (28149247068317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5789802919/10000000000 : ℝ)|^131 ≤ (48523156367209/100000000000000 : ℝ)^99
        have hw : |(-5789802919/10000000000 : ℝ)|=(5789802919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104023977/312500000 : ℝ)|^131 ≤ (5831899138409/25000000000000 : ℝ)^99
        have hw : |(104023977/312500000 : ℝ)|=(104023977/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1918307319/5000000000 : ℝ)|^131 ≤ (28149247068317/100000000000000 : ℝ)^99
        have hw : |(1918307319/5000000000 : ℝ)|=(1918307319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s0_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (151041359/400000000 : ℝ)*x 0 + (-933087707/5000000000 : ℝ)*x 1 + (3466577121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (151041359/400000000 : ℝ)^131 ≤ (13781301265047/50000000000000 : ℝ)^99 := by
    have hnat : (151041359 : ℕ)^131*50000000000000^99 ≤ 13781301265047^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151041359 400000000 13781301265047 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (933087707/5000000000 : ℝ)^131 ≤ (2169355514823/20000000000000 : ℝ)^99 := by
    have hnat : (933087707 : ℕ)^131*20000000000000^99 ≤ 2169355514823^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933087707 5000000000 2169355514823 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3466577121/5000000000 : ℝ)^131 ≤ (12318123975303/20000000000000 : ℝ)^99 := by
    have hnat : (3466577121 : ℕ)^131*20000000000000^99 ≤ 12318123975303^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3466577121 5000000000 12318123975303 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(151041359/400000000 : ℝ), (-933087707/5000000000 : ℝ), (3466577121/5000000000 : ℝ)] ![(13781301265047/50000000000000 : ℝ), (2169355514823/20000000000000 : ℝ), (12318123975303/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(151041359/400000000 : ℝ)|^131 ≤ (13781301265047/50000000000000 : ℝ)^99
        have hw : |(151041359/400000000 : ℝ)|=(151041359/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-933087707/5000000000 : ℝ)|^131 ≤ (2169355514823/20000000000000 : ℝ)^99
        have hw : |(-933087707/5000000000 : ℝ)|=(933087707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3466577121/5000000000 : ℝ)|^131 ≤ (12318123975303/20000000000000 : ℝ)^99
        have hw : |(3466577121/5000000000 : ℝ)|=(3466577121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s0_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2073549007/5000000000 : ℝ)*x 0 + (5984736373/10000000000 : ℝ)*x 1 + (-2748075741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073549007/5000000000 : ℝ)^131 ≤ (31202321091207/100000000000000 : ℝ)^99 := by
    have hnat : (2073549007 : ℕ)^131*100000000000000^99 ≤ 31202321091207^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073549007 5000000000 31202321091207 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5984736373/10000000000 : ℝ)^131 ≤ (10139318500477/20000000000000 : ℝ)^99 := by
    have hnat : (5984736373 : ℕ)^131*20000000000000^99 ≤ 10139318500477^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5984736373 10000000000 10139318500477 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2748075741/10000000000 : ℝ)^131 ≤ (18101086395491/100000000000000 : ℝ)^99 := by
    have hnat : (2748075741 : ℕ)^131*100000000000000^99 ≤ 18101086395491^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748075741 10000000000 18101086395491 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2073549007/5000000000 : ℝ), (5984736373/10000000000 : ℝ), (-2748075741/10000000000 : ℝ)] ![(31202321091207/100000000000000 : ℝ), (10139318500477/20000000000000 : ℝ), (18101086395491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2073549007/5000000000 : ℝ)|^131 ≤ (31202321091207/100000000000000 : ℝ)^99
        have hw : |(2073549007/5000000000 : ℝ)|=(2073549007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5984736373/10000000000 : ℝ)|^131 ≤ (10139318500477/20000000000000 : ℝ)^99
        have hw : |(5984736373/10000000000 : ℝ)|=(5984736373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2748075741/10000000000 : ℝ)|^131 ≤ (18101086395491/100000000000000 : ℝ)^99
        have hw : |(-2748075741/10000000000 : ℝ)|=(2748075741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s0_12 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (32925407/200000000 : ℝ)*x 0 + (3830111889/5000000000 : ℝ)*x 1 + (3022707511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32925407/200000000 : ℝ)^131 ≤ (2297148195471/25000000000000 : ℝ)^99 := by
    have hnat : (32925407 : ℕ)^131*25000000000000^99 ≤ 2297148195471^99*200000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32925407 200000000 2297148195471 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3830111889/5000000000 : ℝ)^131 ≤ (7027883505867/10000000000000 : ℝ)^99 := by
    have hnat : (3830111889 : ℕ)^131*10000000000000^99 ≤ 7027883505867^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3830111889 5000000000 7027883505867 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3022707511/10000000000 : ℝ)^131 ≤ (10266286074463/50000000000000 : ℝ)^99 := by
    have hnat : (3022707511 : ℕ)^131*50000000000000^99 ≤ 10266286074463^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3022707511 10000000000 10266286074463 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32925407/200000000 : ℝ), (3830111889/5000000000 : ℝ), (3022707511/10000000000 : ℝ)] ![(2297148195471/25000000000000 : ℝ), (7027883505867/10000000000000 : ℝ), (10266286074463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32925407/200000000 : ℝ)|^131 ≤ (2297148195471/25000000000000 : ℝ)^99
        have hw : |(32925407/200000000 : ℝ)|=(32925407/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3830111889/5000000000 : ℝ)|^131 ≤ (7027883505867/10000000000000 : ℝ)^99
        have hw : |(3830111889/5000000000 : ℝ)|=(3830111889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3022707511/10000000000 : ℝ)|^131 ≤ (10266286074463/50000000000000 : ℝ)^99
        have hw : |(3022707511/10000000000 : ℝ)|=(3022707511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s0_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2914105811/5000000000 : ℝ)*x 0 + (119081911/312500000 : ℝ)*x 1 + (132398077/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2914105811/5000000000 : ℝ)^131 ≤ (3059347180263/6250000000000 : ℝ)^99 := by
    have hnat : (2914105811 : ℕ)^131*6250000000000^99 ≤ 3059347180263^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2914105811 5000000000 3059347180263 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (119081911/312500000 : ℝ)^131 ≤ (6974291141257/25000000000000 : ℝ)^99 := by
    have hnat : (119081911 : ℕ)^131*25000000000000^99 ≤ 6974291141257^99*312500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119081911 312500000 6974291141257 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (132398077/400000000 : ℝ)^131 ≤ (23153280537817/100000000000000 : ℝ)^99 := by
    have hnat : (132398077 : ℕ)^131*100000000000000^99 ≤ 23153280537817^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132398077 400000000 23153280537817 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2914105811/5000000000 : ℝ), (119081911/312500000 : ℝ), (132398077/400000000 : ℝ)] ![(3059347180263/6250000000000 : ℝ), (6974291141257/25000000000000 : ℝ), (23153280537817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2914105811/5000000000 : ℝ)|^131 ≤ (3059347180263/6250000000000 : ℝ)^99
        have hw : |(-2914105811/5000000000 : ℝ)|=(2914105811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(119081911/312500000 : ℝ)|^131 ≤ (6974291141257/25000000000000 : ℝ)^99
        have hw : |(119081911/312500000 : ℝ)|=(119081911/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(132398077/400000000 : ℝ)|^131 ≤ (23153280537817/100000000000000 : ℝ)^99
        have hw : |(132398077/400000000 : ℝ)|=(132398077/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s0_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3705511577/10000000000 : ℝ)*x 0 + (-2264230579/10000000000 : ℝ)*x 1 + (6720846213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3705511577/10000000000 : ℝ)^131 ≤ (3360438728423/12500000000000 : ℝ)^99 := by
    have hnat : (3705511577 : ℕ)^131*12500000000000^99 ≤ 3360438728423^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3705511577 10000000000 3360438728423 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264230579/10000000000 : ℝ)^131 ≤ (14009097401211/100000000000000 : ℝ)^99 := by
    have hnat : (2264230579 : ℕ)^131*100000000000000^99 ≤ 14009097401211^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264230579 10000000000 14009097401211 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6720846213/10000000000 : ℝ)^131 ≤ (59107392759511/100000000000000 : ℝ)^99 := by
    have hnat : (6720846213 : ℕ)^131*100000000000000^99 ≤ 59107392759511^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6720846213 10000000000 59107392759511 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3705511577/10000000000 : ℝ), (-2264230579/10000000000 : ℝ), (6720846213/10000000000 : ℝ)] ![(3360438728423/12500000000000 : ℝ), (14009097401211/100000000000000 : ℝ), (59107392759511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3705511577/10000000000 : ℝ)|^131 ≤ (3360438728423/12500000000000 : ℝ)^99
        have hw : |(3705511577/10000000000 : ℝ)|=(3705511577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2264230579/10000000000 : ℝ)|^131 ≤ (14009097401211/100000000000000 : ℝ)^99
        have hw : |(-2264230579/10000000000 : ℝ)|=(2264230579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6720846213/10000000000 : ℝ)|^131 ≤ (59107392759511/100000000000000 : ℝ)^99
        have hw : |(6720846213/10000000000 : ℝ)|=(6720846213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s0_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (213335289/500000000 : ℝ)*x 0 + (2724190991/5000000000 : ℝ)*x 1 + (-818684571/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213335289/500000000 : ℝ)^131 ≤ (1295945357673/4000000000000 : ℝ)^99 := by
    have hnat : (213335289 : ℕ)^131*4000000000000^99 ≤ 1295945357673^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213335289 500000000 1295945357673 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724190991/5000000000 : ℝ)^131 ≤ (44773463898851/100000000000000 : ℝ)^99 := by
    have hnat : (2724190991 : ℕ)^131*100000000000000^99 ≤ 44773463898851^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724190991 5000000000 44773463898851 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (818684571/2500000000 : ℝ)^131 ≤ (22827902141403/100000000000000 : ℝ)^99 := by
    have hnat : (818684571 : ℕ)^131*100000000000000^99 ≤ 22827902141403^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818684571 2500000000 22827902141403 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213335289/500000000 : ℝ), (2724190991/5000000000 : ℝ), (-818684571/2500000000 : ℝ)] ![(1295945357673/4000000000000 : ℝ), (44773463898851/100000000000000 : ℝ), (22827902141403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213335289/500000000 : ℝ)|^131 ≤ (1295945357673/4000000000000 : ℝ)^99
        have hw : |(213335289/500000000 : ℝ)|=(213335289/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2724190991/5000000000 : ℝ)|^131 ≤ (44773463898851/100000000000000 : ℝ)^99
        have hw : |(2724190991/5000000000 : ℝ)|=(2724190991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-818684571/2500000000 : ℝ)|^131 ≤ (22827902141403/100000000000000 : ℝ)^99
        have hw : |(-818684571/2500000000 : ℝ)|=(818684571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s0_19 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1231114969/5000000000 : ℝ)*x 0 + (1698221817/2500000000 : ℝ)*x 1 + (3443798317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1231114969/5000000000 : ℝ)^131 ≤ (3130518934839/20000000000000 : ℝ)^99 := by
    have hnat : (1231114969 : ℕ)^131*20000000000000^99 ≤ 3130518934839^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1231114969 5000000000 3130518934839 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1698221817/2500000000 : ℝ)^131 ≤ (59947208306943/100000000000000 : ℝ)^99 := by
    have hnat : (1698221817 : ℕ)^131*100000000000000^99 ≤ 59947208306943^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1698221817 2500000000 59947208306943 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3443798317/10000000000 : ℝ)^131 ≤ (12200098499829/50000000000000 : ℝ)^99 := by
    have hnat : (3443798317 : ℕ)^131*50000000000000^99 ≤ 12200098499829^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3443798317 10000000000 12200098499829 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1231114969/5000000000 : ℝ), (1698221817/2500000000 : ℝ), (3443798317/10000000000 : ℝ)] ![(3130518934839/20000000000000 : ℝ), (59947208306943/100000000000000 : ℝ), (12200098499829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1231114969/5000000000 : ℝ)|^131 ≤ (3130518934839/20000000000000 : ℝ)^99
        have hw : |(1231114969/5000000000 : ℝ)|=(1231114969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1698221817/2500000000 : ℝ)|^131 ≤ (59947208306943/100000000000000 : ℝ)^99
        have hw : |(1698221817/2500000000 : ℝ)|=(1698221817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3443798317/10000000000 : ℝ)|^131 ≤ (12200098499829/50000000000000 : ℝ)^99
        have hw : |(3443798317/10000000000 : ℝ)|=(3443798317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s0_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-5649744537/10000000000 : ℝ)*x 0 + (3931555013/10000000000 : ℝ)*x 1 + (848898923/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5649744537/10000000000 : ℝ)^131 ≤ (23488025604733/50000000000000 : ℝ)^99 := by
    have hnat : (5649744537 : ℕ)^131*50000000000000^99 ≤ 23488025604733^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5649744537 10000000000 23488025604733 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3931555013/10000000000 : ℝ)^131 ≤ (29074647106123/100000000000000 : ℝ)^99 := by
    have hnat : (3931555013 : ℕ)^131*100000000000000^99 ≤ 29074647106123^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3931555013 10000000000 29074647106123 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848898923/2500000000 : ℝ)^131 ≤ (11974650832159/50000000000000 : ℝ)^99 := by
    have hnat : (848898923 : ℕ)^131*50000000000000^99 ≤ 11974650832159^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848898923 2500000000 11974650832159 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5649744537/10000000000 : ℝ), (3931555013/10000000000 : ℝ), (848898923/2500000000 : ℝ)] ![(23488025604733/50000000000000 : ℝ), (29074647106123/100000000000000 : ℝ), (11974650832159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5649744537/10000000000 : ℝ)|^131 ≤ (23488025604733/50000000000000 : ℝ)^99
        have hw : |(-5649744537/10000000000 : ℝ)|=(5649744537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3931555013/10000000000 : ℝ)|^131 ≤ (29074647106123/100000000000000 : ℝ)^99
        have hw : |(3931555013/10000000000 : ℝ)|=(3931555013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848898923/2500000000 : ℝ)|^131 ≤ (11974650832159/50000000000000 : ℝ)^99
        have hw : |(848898923/2500000000 : ℝ)|=(848898923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s0_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3619672641/10000000000 : ℝ)*x 0 + (-136885657/625000000 : ℝ)*x 1 + (6842859423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3619672641/10000000000 : ℝ)^131 ≤ (13031276221333/50000000000000 : ℝ)^99 := by
    have hnat : (3619672641 : ℕ)^131*50000000000000^99 ≤ 13031276221333^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3619672641 10000000000 13031276221333 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136885657/625000000 : ℝ)^131 ≤ (13405995697311/100000000000000 : ℝ)^99 := by
    have hnat : (136885657 : ℕ)^131*100000000000000^99 ≤ 13405995697311^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136885657 625000000 13405995697311 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6842859423/10000000000 : ℝ)^131 ≤ (30265725926553/50000000000000 : ℝ)^99 := by
    have hnat : (6842859423 : ℕ)^131*50000000000000^99 ≤ 30265725926553^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6842859423 10000000000 30265725926553 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3619672641/10000000000 : ℝ), (-136885657/625000000 : ℝ), (6842859423/10000000000 : ℝ)] ![(13031276221333/50000000000000 : ℝ), (13405995697311/100000000000000 : ℝ), (30265725926553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3619672641/10000000000 : ℝ)|^131 ≤ (13031276221333/50000000000000 : ℝ)^99
        have hw : |(3619672641/10000000000 : ℝ)|=(3619672641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-136885657/625000000 : ℝ)|^131 ≤ (13405995697311/100000000000000 : ℝ)^99
        have hw : |(-136885657/625000000 : ℝ)|=(136885657/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6842859423/10000000000 : ℝ)|^131 ≤ (30265725926553/50000000000000 : ℝ)^99
        have hw : |(6842859423/10000000000 : ℝ)|=(6842859423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s0_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2506013149/5000000000 : ℝ)*x 0 + (2476602223/5000000000 : ℝ)*x 1 + (-301231583/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2506013149/5000000000 : ℝ)^131 ≤ (2505693657581/6250000000000 : ℝ)^99 := by
    have hnat : (2506013149 : ℕ)^131*6250000000000^99 ≤ 2505693657581^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2506013149 5000000000 2505693657581 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2476602223/5000000000 : ℝ)^131 ≤ (986742053979/2500000000000 : ℝ)^99 := by
    have hnat : (2476602223 : ℕ)^131*2500000000000^99 ≤ 986742053979^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2476602223 5000000000 986742053979 2500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (301231583/1000000000 : ℝ)^131 ≤ (2554902412277/12500000000000 : ℝ)^99 := by
    have hnat : (301231583 : ℕ)^131*12500000000000^99 ≤ 2554902412277^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301231583 1000000000 2554902412277 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2506013149/5000000000 : ℝ), (2476602223/5000000000 : ℝ), (-301231583/1000000000 : ℝ)] ![(2505693657581/6250000000000 : ℝ), (986742053979/2500000000000 : ℝ), (2554902412277/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2506013149/5000000000 : ℝ)|^131 ≤ (2505693657581/6250000000000 : ℝ)^99
        have hw : |(2506013149/5000000000 : ℝ)|=(2506013149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2476602223/5000000000 : ℝ)|^131 ≤ (986742053979/2500000000000 : ℝ)^99
        have hw : |(2476602223/5000000000 : ℝ)|=(2476602223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-301231583/1000000000 : ℝ)|^131 ≤ (2554902412277/12500000000000 : ℝ)^99
        have hw : |(-301231583/1000000000 : ℝ)|=(301231583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s0_25 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1508187807/10000000000 : ℝ)*x 0 + (7867984747/10000000000 : ℝ)*x 1 + (712793543/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1508187807/10000000000 : ℝ)^131 ≤ (4091435115383/50000000000000 : ℝ)^99 := by
    have hnat : (1508187807 : ℕ)^131*50000000000000^99 ≤ 4091435115383^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1508187807 10000000000 4091435115383 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7867984747/10000000000 : ℝ)^131 ≤ (36406022556871/50000000000000 : ℝ)^99 := by
    have hnat : (7867984747 : ℕ)^131*50000000000000^99 ≤ 36406022556871^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7867984747 10000000000 36406022556871 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (712793543/2500000000 : ℝ)^131 ≤ (760203385877/4000000000000 : ℝ)^99 := by
    have hnat : (712793543 : ℕ)^131*4000000000000^99 ≤ 760203385877^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712793543 2500000000 760203385877 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1508187807/10000000000 : ℝ), (7867984747/10000000000 : ℝ), (712793543/2500000000 : ℝ)] ![(4091435115383/50000000000000 : ℝ), (36406022556871/50000000000000 : ℝ), (760203385877/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1508187807/10000000000 : ℝ)|^131 ≤ (4091435115383/50000000000000 : ℝ)^99
        have hw : |(1508187807/10000000000 : ℝ)|=(1508187807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7867984747/10000000000 : ℝ)|^131 ≤ (36406022556871/50000000000000 : ℝ)^99
        have hw : |(7867984747/10000000000 : ℝ)|=(7867984747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(712793543/2500000000 : ℝ)|^131 ≤ (760203385877/4000000000000 : ℝ)^99
        have hw : |(712793543/2500000000 : ℝ)|=(712793543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s1_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-4901815803/10000000000 : ℝ)*x 0 + (815981331/2000000000 : ℝ)*x 1 + (2040003613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4901815803/10000000000 : ℝ)^131 ≤ (38928740908209/100000000000000 : ℝ)^99 := by
    have hnat : (4901815803 : ℕ)^131*100000000000000^99 ≤ 38928740908209^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4901815803 10000000000 38928740908209 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (815981331/2000000000 : ℝ)^131 ≤ (305351315387/1000000000000 : ℝ)^99 := by
    have hnat : (815981331 : ℕ)^131*1000000000000^99 ≤ 305351315387^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      815981331 2000000000 305351315387 1000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2040003613/5000000000 : ℝ)^131 ≤ (30536127540603/100000000000000 : ℝ)^99 := by
    have hnat : (2040003613 : ℕ)^131*100000000000000^99 ≤ 30536127540603^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040003613 5000000000 30536127540603 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4901815803/10000000000 : ℝ), (815981331/2000000000 : ℝ), (2040003613/5000000000 : ℝ)] ![(38928740908209/100000000000000 : ℝ), (305351315387/1000000000000 : ℝ), (30536127540603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4901815803/10000000000 : ℝ)|^131 ≤ (38928740908209/100000000000000 : ℝ)^99
        have hw : |(-4901815803/10000000000 : ℝ)|=(4901815803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(815981331/2000000000 : ℝ)|^131 ≤ (305351315387/1000000000000 : ℝ)^99
        have hw : |(815981331/2000000000 : ℝ)|=(815981331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2040003613/5000000000 : ℝ)|^131 ≤ (30536127540603/100000000000000 : ℝ)^99
        have hw : |(2040003613/5000000000 : ℝ)|=(2040003613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s1_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (84496149/200000000 : ℝ)*x 0 + (-3516415289/10000000000 : ℝ)*x 1 + (82480651/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84496149/200000000 : ℝ)^131 ≤ (15989159180371/50000000000000 : ℝ)^99 := by
    have hnat : (84496149 : ℕ)^131*50000000000000^99 ≤ 15989159180371^99*200000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84496149 200000000 15989159180371 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3516415289/10000000000 : ℝ)^131 ≤ (25083322370937/100000000000000 : ℝ)^99 := by
    have hnat : (3516415289 : ℕ)^131*100000000000000^99 ≤ 25083322370937^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3516415289 10000000000 25083322370937 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82480651/156250000 : ℝ)^131 ≤ (1073458981253/2500000000000 : ℝ)^99 := by
    have hnat : (82480651 : ℕ)^131*2500000000000^99 ≤ 1073458981253^99*156250000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82480651 156250000 1073458981253 2500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84496149/200000000 : ℝ), (-3516415289/10000000000 : ℝ), (82480651/156250000 : ℝ)] ![(15989159180371/50000000000000 : ℝ), (25083322370937/100000000000000 : ℝ), (1073458981253/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84496149/200000000 : ℝ)|^131 ≤ (15989159180371/50000000000000 : ℝ)^99
        have hw : |(84496149/200000000 : ℝ)|=(84496149/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3516415289/10000000000 : ℝ)|^131 ≤ (25083322370937/100000000000000 : ℝ)^99
        have hw : |(-3516415289/10000000000 : ℝ)|=(3516415289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82480651/156250000 : ℝ)|^131 ≤ (1073458981253/2500000000000 : ℝ)^99
        have hw : |(82480651/156250000 : ℝ)|=(82480651/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s1_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4224729381/10000000000 : ℝ)*x 0 + (65985191/125000000 : ℝ)*x 1 + (-3516436989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4224729381/10000000000 : ℝ)^131 ≤ (15988768220551/50000000000000 : ℝ)^99 := by
    have hnat : (4224729381 : ℕ)^131*50000000000000^99 ≤ 15988768220551^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224729381 10000000000 15988768220551 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65985191/125000000 : ℝ)^131 ≤ (21469468170769/50000000000000 : ℝ)^99 := by
    have hnat : (65985191 : ℕ)^131*50000000000000^99 ≤ 21469468170769^99*125000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65985191 125000000 21469468170769 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3516436989/10000000000 : ℝ)^131 ≤ (2508352719509/10000000000000 : ℝ)^99 := by
    have hnat : (3516436989 : ℕ)^131*10000000000000^99 ≤ 2508352719509^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3516436989 10000000000 2508352719509 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4224729381/10000000000 : ℝ), (65985191/125000000 : ℝ), (-3516436989/10000000000 : ℝ)] ![(15988768220551/50000000000000 : ℝ), (21469468170769/50000000000000 : ℝ), (2508352719509/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4224729381/10000000000 : ℝ)|^131 ≤ (15988768220551/50000000000000 : ℝ)^99
        have hw : |(4224729381/10000000000 : ℝ)|=(4224729381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65985191/125000000 : ℝ)|^131 ≤ (21469468170769/50000000000000 : ℝ)^99
        have hw : |(65985191/125000000 : ℝ)|=(65985191/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3516436989/10000000000 : ℝ)|^131 ≤ (2508352719509/10000000000000 : ℝ)^99
        have hw : |(-3516436989/10000000000 : ℝ)|=(3516436989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302077_s1_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (186574721/500000000 : ℝ)*x 0 + (4662516337/10000000000 : ℝ)*x 1 + (582797853/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (186574721/500000000 : ℝ)^131 ≤ (3391653609479/12500000000000 : ℝ)^99 := by
    have hnat : (186574721 : ℕ)^131*12500000000000^99 ≤ 3391653609479^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186574721 500000000 3391653609479 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4662516337/10000000000 : ℝ)^131 ≤ (4554259477329/12500000000000 : ℝ)^99 := by
    have hnat : (4662516337 : ℕ)^131*12500000000000^99 ≤ 4554259477329^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4662516337 10000000000 4554259477329 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (582797853/1250000000 : ℝ)^131 ≤ (9108173822803/25000000000000 : ℝ)^99 := by
    have hnat : (582797853 : ℕ)^131*25000000000000^99 ≤ 9108173822803^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582797853 1250000000 9108173822803 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(186574721/500000000 : ℝ), (4662516337/10000000000 : ℝ), (582797853/1250000000 : ℝ)] ![(3391653609479/12500000000000 : ℝ), (4554259477329/12500000000000 : ℝ), (9108173822803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(186574721/500000000 : ℝ)|^131 ≤ (3391653609479/12500000000000 : ℝ)^99
        have hw : |(186574721/500000000 : ℝ)|=(186574721/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4662516337/10000000000 : ℝ)|^131 ≤ (4554259477329/12500000000000 : ℝ)^99
        have hw : |(4662516337/10000000000 : ℝ)|=(4662516337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(582797853/1250000000 : ℝ)|^131 ≤ (9108173822803/25000000000000 : ℝ)^99
        have hw : |(582797853/1250000000 : ℝ)|=(582797853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302077 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have s0_pow0 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-140009803/250000000 : ℝ)*X 0 0+(940412743/2500000000 : ℝ)*X 0 1+(3628050657/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2272029493/5000000000 : ℝ)*X 2 0+(2732762163/5000000000 : ℝ)*X 2 1+(-735934013/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_4 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s0_4 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((425397569/2000000000 : ℝ)*X 0 0+(6830561663/10000000000 : ℝ)*X 0 1+(1844014481/5000000000 : ℝ)*X 0 2+(425397569/2000000000 : ℝ)*X 1 0+(6830561663/10000000000 : ℝ)*X 1 1+(1844014481/5000000000 : ℝ)*X 1 2+(425397569/2000000000 : ℝ)*X 2 0+(6830561663/10000000000 : ℝ)*X 2 1+(1844014481/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-5789802919/10000000000 : ℝ)*X 0 0+(104023977/312500000 : ℝ)*X 0 1+(1918307319/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((151041359/400000000 : ℝ)*X 1 0+(-933087707/5000000000 : ℝ)*X 1 1+(3466577121/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2073549007/5000000000 : ℝ)*X 2 0+(5984736373/10000000000 : ℝ)*X 2 1+(-2748075741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((32925407/200000000 : ℝ)*X 0 0+(3830111889/5000000000 : ℝ)*X 0 1+(3022707511/10000000000 : ℝ)*X 0 2+(32925407/200000000 : ℝ)*X 1 0+(3830111889/5000000000 : ℝ)*X 1 1+(3022707511/10000000000 : ℝ)*X 1 2+(32925407/200000000 : ℝ)*X 2 0+(3830111889/5000000000 : ℝ)*X 2 1+(3022707511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-2914105811/5000000000 : ℝ)*X 0 0+(119081911/312500000 : ℝ)*X 0 1+(132398077/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((3705511577/10000000000 : ℝ)*X 1 0+(-2264230579/10000000000 : ℝ)*X 1 1+(6720846213/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((213335289/500000000 : ℝ)*X 2 0+(2724190991/5000000000 : ℝ)*X 2 1+(-818684571/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((1231114969/5000000000 : ℝ)*X 0 0+(1698221817/2500000000 : ℝ)*X 0 1+(3443798317/10000000000 : ℝ)*X 0 2+(1231114969/5000000000 : ℝ)*X 1 0+(1698221817/2500000000 : ℝ)*X 1 1+(3443798317/10000000000 : ℝ)*X 1 2+(1231114969/5000000000 : ℝ)*X 2 0+(1698221817/2500000000 : ℝ)*X 2 1+(3443798317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-5649744537/10000000000 : ℝ)*X 0 0+(3931555013/10000000000 : ℝ)*X 0 1+(848898923/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((3619672641/10000000000 : ℝ)*X 1 0+(-136885657/625000000 : ℝ)*X 1 1+(6842859423/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2506013149/5000000000 : ℝ)*X 2 0+(2476602223/5000000000 : ℝ)*X 2 1+(-301231583/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((1508187807/10000000000 : ℝ)*X 0 0+(7867984747/10000000000 : ℝ)*X 0 1+(712793543/2500000000 : ℝ)*X 0 2+(1508187807/10000000000 : ℝ)*X 1 0+(7867984747/10000000000 : ℝ)*X 1 1+(712793543/2500000000 : ℝ)*X 1 2+(1508187807/10000000000 : ℝ)*X 2 0+(7867984747/10000000000 : ℝ)*X 2 1+(712793543/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((6729/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6729/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3075497899070931450969/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (915921175871/1000000000000 : ℝ)*(base49) + (683139008493/500000000000 : ℝ)*(base60) + (126800607959/15625000000 : ℝ)*(major_s0_0) + (12529596598919/1000000000000 : ℝ)*(major_s0_1) + (126800607959/15625000000 : ℝ)*(major_s0_2) + (228495087/1000000000000 : ℝ)*(sp_s0_0) + (4414357689543/1000000000000 : ℝ)*(sp_s0_4) + (18316213/250000000000 : ℝ)*(sp_s0_6) + (5394991583351/500000000000 : ℝ)*(sp_s0_7) + (2157986805613/200000000000 : ℝ)*(sp_s0_8) + (5395033188141/500000000000 : ℝ)*(sp_s0_9) + (1360047197861/250000000000 : ℝ)*(sp_s0_12) + (145285507/1000000000000 : ℝ)*(sp_s0_15) + (69408431/250000000000 : ℝ)*(sp_s0_21) + (680032757037/125000000000 : ℝ)*(f.failure) + (10790211661789/1000000000000 : ℝ)*(f.sum) + (1941633445189151/10000000000000000000000000000 : ℝ)*base62 + (25840099168183/156250000000000000000000000 : ℝ)*base65 + (2106490783156837/10000000000000000000000000000 : ℝ)*base66 + (16323999432217/39062500000000000000000000 : ℝ)*base69 + (2035497161119/15625000000000000000000000 : ℝ)*base71 + (17444592863067/156250000000000000000000000 : ℝ)*base72 + (5929192084836703/10000000000000000000000000000 : ℝ)*base74 + (46368297213243/156250000000000000000000000 : ℝ)*base76 + (4347122002229/16000000000000000000000000 : ℝ)*base78 + (929/1250000000000000 : ℝ)*base87 + (929/1250000000000000 : ℝ)*base89 + (929/1250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((4359/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(4359/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (26117328584087585262723/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1099037/500000000000 : ℝ)*(base40) + (200205923943/200000000000 : ℝ)*(base49) + (1092369907209/1000000000000 : ℝ)*(base60) + (6993247770963/1000000000000 : ℝ)*(major_s0_0) + (6993247770963/1000000000000 : ℝ)*(major_s0_1) + (6993247770963/1000000000000 : ℝ)*(major_s0_2) + (8639671/500000000000 : ℝ)*(sp_s0_2) + (65835043/500000000000 : ℝ)*(sp_s0_7) + (2033381/250000000000 : ℝ)*(sp_s0_8) + (9298254355493/1000000000000 : ℝ)*(sp_s0_13) + (4649188946027/500000000000 : ℝ)*(sp_s0_14) + (371932382243/40000000000 : ℝ)*(sp_s0_15) + (4688106034031/1000000000000 : ℝ)*(sp_s0_19) + (59190161/1000000000000 : ℝ)*(sp_s0_22) + (4688106034031/1000000000000 : ℝ)*(f.failure) + (4649193012789/500000000000 : ℝ)*(f.sum) + (424658846456271/500000000000000000000000000 : ℝ)*base63 + (7144659856308469/10000000000000000000000000000 : ℝ)*base64 + (7460232301183049/10000000000000000000000000000 : ℝ)*base66 + (422520717183049/10000000000000000000000000000 : ℝ)*base68 + (110650228343729/500000000000000000000000000 : ℝ)*base71 + (8286216045308469/10000000000000000000000000000 : ℝ)*base72 + (2501764859691531/10000000000000000000000000000 : ℝ)*base74 + (2332473674816951/10000000000000000000000000000 : ℝ)*base76 + (2970083801245759/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (10427/10000000000000000 : ℝ)*base87 + (10427/10000000000000000 : ℝ)*base89 + (10427/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(467/3125 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(467/3125 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (557566147604922246813/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11549688883/200000000000 : ℝ)*(base49) + (236139237647/500000000000 : ℝ)*(base60) + (6357719759139/1000000000000 : ℝ)*(major_s0_0) + (5704839711463/500000000000 : ℝ)*(major_s0_1) + (6357719759139/1000000000000 : ℝ)*(major_s0_2) + (331223/125000000000 : ℝ)*(sp_s0_0) + (3683997/100000000000 : ℝ)*(sp_s0_2) + (2525979831893/500000000000 : ℝ)*(sp_s0_4) + (20811999/200000000000 : ℝ)*(sp_s0_13) + (4724833/50000000000 : ℝ)*(sp_s0_14) + (422663403277/50000000000 : ℝ)*(sp_s0_20) + (4226640139329/500000000000 : ℝ)*(sp_s0_21) + (2113334483837/250000000000 : ℝ)*(sp_s0_22) + (426206325611/100000000000 : ℝ)*(sp_s0_25) + (426206325611/100000000000 : ℝ)*(f.failure) + (8453374775319/1000000000000 : ℝ)*(f.sum) + (1156707453467959/10000000000000000000000000000 : ℝ)*base62 + (6265168613210843/10000000000000000000000000000 : ℝ)*base65 + (2499318556464549/5000000000000000000000000000 : ℝ)*base66 + (802416348812103/10000000000000000000000000000 : ℝ)*base69 + (46573587980063/500000000000000000000000000 : ℝ)*base70 + (566045257210843/10000000000000000000000000000 : ℝ)*base73 + (2694387122140031/5000000000000000000000000000 : ℝ)*base74 + (9527882685187897/10000000000000000000000000000 : ℝ)*base77 + (526019719743651/2000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (287/1000000000000000 : ℝ)*base87 + (713/1000000000000000 : ℝ)*base88 + (287/1000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (6729/25000 : ℝ) ^ (65/16 : ℝ) ≤ (241761833320512451/50000000000000000000 : ℝ) := by
    have hpowers : (6729/25000 : ℝ)^65 ≤ (241761833320512451/50000000000000000000 : ℝ)^16 := by
      have hnat : (6729 : ℕ)^65*50000000000000000000^16 ≤ 241761833320512451^16*25000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6729 25000 241761833320512451 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6729/25000 : ℝ)) (X := (241761833320512451/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50241761833320512451/50000000000000000000 : ℝ) ≤ (200237609807543/200000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50241761833320512451/50000000000000000000 : ℝ)^16 ≤ (200237609807543/200000000000000 : ℝ)^65 := by
      have hnat : (50241761833320512451 : ℕ)^16*200000000000000^65 ≤ 200237609807543^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50241761833320512451 50000000000000000000 200237609807543 200000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200237609807543/200000000000000 : ℝ)) (X := (50241761833320512451/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25241761833320512451/25000000000000000000 : ℝ) ≤ (1252964745287353/1250000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (25241761833320512451/25000000000000000000 : ℝ)^16 ≤ (1252964745287353/1250000000000000 : ℝ)^65 := by
      have hnat : (25241761833320512451 : ℕ)^16*1250000000000000^65 ≤ 1252964745287353^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25241761833320512451 25000000000000000000 1252964745287353 1250000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1252964745287353/1250000000000000 : ℝ)) (X := (25241761833320512451/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(79203269181/17944000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(5918735960837/1345800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (6729/25000 : ℝ)) (alpha := (79203269181/17944000000000 : ℝ)) (beta := (5918735960837/1345800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (6729/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(79203269181/17944000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(5918735960837/1345800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (4359/100000 : ℝ) ^ (65/16 : ℝ) ≤ (296830931788529/100000000000000000000 : ℝ) := by
    have hpowers : (4359/100000 : ℝ)^65 ≤ (296830931788529/100000000000000000000 : ℝ)^16 := by
      have hnat : (4359 : ℕ)^65*100000000000000000000^16 ≤ 296830931788529^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4359 100000 296830931788529 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4359/100000 : ℝ)) (X := (296830931788529/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100000296830931788529/100000000000000000000 : ℝ) ≤ (10000007306599377/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (100000296830931788529/100000000000000000000 : ℝ)^16 ≤ (10000007306599377/10000000000000000 : ℝ)^65 := by
      have hnat : (100000296830931788529 : ℕ)^16*10000000000000000^65 ≤ 10000007306599377^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100000296830931788529 100000000000000000000 10000007306599377 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000007306599377/10000000000000000 : ℝ)) (X := (100000296830931788529/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50000296830931788529/50000000000000000000 : ℝ) ≤ (2000002922636481/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50000296830931788529/50000000000000000000 : ℝ)^16 ≤ (2000002922636481/2000000000000000 : ℝ)^65 := by
      have hnat : (50000296830931788529 : ℕ)^16*2000000000000000^65 ≤ 2000002922636481^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000296830931788529 50000000000000000000 2000002922636481 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000002922636481/2000000000000000 : ℝ)) (X := (50000296830931788529/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(7306599377/435900000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(608881919/36325000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (4359/100000 : ℝ)) (alpha := (7306599377/435900000000000 : ℝ)) (beta := (608881919/36325000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (4359/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(7306599377/435900000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(608881919/36325000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (467/3125 : ℝ) ^ (65/16 : ℝ) ≤ (22143263014266857/50000000000000000000 : ℝ) := by
    have hpowers : (467/3125 : ℝ)^65 ≤ (22143263014266857/50000000000000000000 : ℝ)^16 := by
      have hnat : (467 : ℕ)^65*50000000000000000000^16 ≤ 22143263014266857^16*3125^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        467 3125 22143263014266857 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (467/3125 : ℝ)) (X := (22143263014266857/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50022143263014266857/50000000000000000000 : ℝ) ≤ (10001089947947403/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50022143263014266857/50000000000000000000 : ℝ)^16 ≤ (10001089947947403/10000000000000000 : ℝ)^65 := by
      have hnat : (50022143263014266857 : ℕ)^16*10000000000000000^65 ≤ 10001089947947403^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022143263014266857 50000000000000000000 10001089947947403 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001089947947403/10000000000000000 : ℝ)) (X := (50022143263014266857/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25022143263014266857/25000000000000000000 : ℝ) ≤ (200043590644699/200000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (25022143263014266857/25000000000000000000 : ℝ)^16 ≤ (200043590644699/200000000000000 : ℝ)^65 := by
      have hnat : (25022143263014266857 : ℕ)^16*200000000000000^65 ≤ 200043590644699^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25022143263014266857 25000000000000000000 200043590644699 200000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200043590644699/200000000000000 : ℝ)) (X := (25022143263014266857/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1089947947403/1494400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1089584287547/1494400000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (467/3125 : ℝ)) (alpha := (1089947947403/1494400000000000 : ℝ)) (beta := (1089584287547/1494400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (467/3125 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1089947947403/1494400000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1089584287547/1494400000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-4901815803/10000000000 : ℝ)*X 0 0+(815981331/2000000000 : ℝ)*X 0 1+(2040003613/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((84496149/200000000 : ℝ)*X 1 0+(-3516415289/10000000000 : ℝ)*X 1 1+(82480651/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4224729381/10000000000 : ℝ)*X 2 0+(65985191/125000000 : ℝ)*X 2 1+(-3516436989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((186574721/500000000 : ℝ)*X 0 0+(4662516337/10000000000 : ℝ)*X 0 1+(582797853/1250000000 : ℝ)*X 0 2+(186574721/500000000 : ℝ)*X 1 0+(4662516337/10000000000 : ℝ)*X 1 1+(582797853/1250000000 : ℝ)*X 1 2+(186574721/500000000 : ℝ)*X 2 0+(4662516337/10000000000 : ℝ)*X 2 1+(582797853/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302077_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-29751/5000 : ℝ) < ((-14917/10000 : ℝ)*P 0+(-14917/10000 : ℝ)*P 1+(-14917/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-29751/5000 : ℝ) < (-446333996845478524947099682825997/76099494650000000000000000000000 : ℝ) := by norm_num
    linear_combination (21/781250000 : ℝ)*(base19) + (837/25000000000 : ℝ)*(base23) + (6253/1000000000000 : ℝ)*(base40) + (17993/500000000000 : ℝ)*(base43) + (130087063089/250000000000 : ℝ)*(base49) + (22777662083/100000000000 : ℝ)*(base50) + (31298930311/500000000000 : ℝ)*(base59) + (291493375967/1000000000000 : ℝ)*(base60) + (14917/10000 : ℝ)*(major_s1_0) + (745849982007/500000000000 : ℝ)*(major_s1_1) + (14917/10000 : ℝ)*(major_s1_2) + (1955045784387/1000000000000 : ℝ)*(sp_s1_0) + (1955045793493/1000000000000 : ℝ)*(sp_s1_1) + (488761437727/250000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (977522910187/500000000000 : ℝ)*(f.sum) + (17025189530232789/33927550000000000000000000000 : ℝ)*base62 + (339451099201/934000000000000000000000 : ℝ)*base65 + (7111736140357/72650000000000000000000000 : ℝ)*base67 + (22339143169/93400000000000000000000 : ℝ)*base68 + (6320252490155063/10474810000000000000000000000 : ℝ)*base70 + (447523685339/525703125000000000000000 : ℝ)*base73 + (10648214503/4540625000000000000000000 : ℝ)*base75 + (21135815813/35046875000000000000000 : ℝ)*base76 + (233203340121973943/488861850000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p002_b032 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (c : Fin 88) (hlo : 77 ≤ c.val) (hhi : c.val < 78)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=77 := by omega
  rcases hc with rfl
  · exact collision_c302077 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (c : Fin 88) (hlo : 77 ≤ c.val) (hhi : c.val < 78)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p002_b032 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

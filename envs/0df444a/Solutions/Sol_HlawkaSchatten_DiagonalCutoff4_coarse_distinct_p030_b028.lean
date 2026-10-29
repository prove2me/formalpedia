-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030_b028
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:32:45.464315+00:00
-- url     : https://prove2.me/submissions/2199b4a2-c123-4253-a4a8-5a9018f3b284

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
theorem collision_support_c330057_s0_0 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-2888640981/10000000000 : ℝ)*x 0 + (57772841/200000000 : ℝ)*x 1 + (6070044633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2888640981/10000000000 : ℝ)^6 ≤ (22533688265309/100000000000000 : ℝ)^5 := by
    have hnat : (2888640981 : ℕ)^6*100000000000000^5 ≤ 22533688265309^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2888640981 10000000000 22533688265309 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57772841/200000000 : ℝ)^6 ≤ (11266849136083/50000000000000 : ℝ)^5 := by
    have hnat : (57772841 : ℕ)^6*50000000000000^5 ≤ 11266849136083^5*200000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57772841 200000000 11266849136083 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6070044633/10000000000 : ℝ)^6 ≤ (27466306726559/50000000000000 : ℝ)^5 := by
    have hnat : (6070044633 : ℕ)^6*50000000000000^5 ≤ 27466306726559^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6070044633 10000000000 27466306726559 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2888640981/10000000000 : ℝ), (57772841/200000000 : ℝ), (6070044633/10000000000 : ℝ)] ![(22533688265309/100000000000000 : ℝ), (11266849136083/50000000000000 : ℝ), (27466306726559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2888640981/10000000000 : ℝ)|^6 ≤ (22533688265309/100000000000000 : ℝ)^5
        have hw : |(-2888640981/10000000000 : ℝ)|=(2888640981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(57772841/200000000 : ℝ)|^6 ≤ (11266849136083/50000000000000 : ℝ)^5
        have hw : |(57772841/200000000 : ℝ)|=(57772841/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6070044633/10000000000 : ℝ)|^6 ≤ (27466306726559/50000000000000 : ℝ)^5
        have hw : |(6070044633/10000000000 : ℝ)|=(6070044633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330057_s0_1 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2888640977/10000000000 : ℝ)*x 0 + (-2888642047/10000000000 : ℝ)*x 1 + (3035022319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2888640977/10000000000 : ℝ)^6 ≤ (4506737645573/20000000000000 : ℝ)^5 := by
    have hnat : (2888640977 : ℕ)^6*20000000000000^5 ≤ 4506737645573^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2888640977 10000000000 4506737645573 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2888642047/10000000000 : ℝ)^6 ≤ (22533698244083/100000000000000 : ℝ)^5 := by
    have hnat : (2888642047 : ℕ)^6*100000000000000^5 ≤ 22533698244083^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2888642047 10000000000 22533698244083 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3035022319/5000000000 : ℝ)^6 ≤ (54932613507417/100000000000000 : ℝ)^5 := by
    have hnat : (3035022319 : ℕ)^6*100000000000000^5 ≤ 54932613507417^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3035022319 5000000000 54932613507417 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2888640977/10000000000 : ℝ), (-2888642047/10000000000 : ℝ), (3035022319/5000000000 : ℝ)] ![(4506737645573/20000000000000 : ℝ), (22533698244083/100000000000000 : ℝ), (54932613507417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2888640977/10000000000 : ℝ)|^6 ≤ (4506737645573/20000000000000 : ℝ)^5
        have hw : |(2888640977/10000000000 : ℝ)|=(2888640977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2888642047/10000000000 : ℝ)|^6 ≤ (22533698244083/100000000000000 : ℝ)^5
        have hw : |(-2888642047/10000000000 : ℝ)|=(2888642047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3035022319/5000000000 : ℝ)|^6 ≤ (54932613507417/100000000000000 : ℝ)^5
        have hw : |(3035022319/5000000000 : ℝ)|=(3035022319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330057_s0_2 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (5612310363/10000000000 : ℝ)*x 0 + (2806154593/5000000000 : ℝ)*x 1 + (-14647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5612310363/10000000000 : ℝ)^6 ≤ (5000000129843/10000000000000 : ℝ)^5 := by
    have hnat : (5612310363 : ℕ)^6*10000000000000^5 ≤ 5000000129843^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5612310363 10000000000 5000000129843 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2806154593/5000000000 : ℝ)^6 ≤ (49999988715377/100000000000000 : ℝ)^5 := by
    have hnat : (2806154593 : ℕ)^6*100000000000000^5 ≤ 49999988715377^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2806154593 5000000000 49999988715377 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14647/10000000000 : ℝ)^6 ≤ (2493667/25000000000000 : ℝ)^5 := by
    have hnat : (14647 : ℕ)^6*25000000000000^5 ≤ 2493667^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14647 10000000000 2493667 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5612310363/10000000000 : ℝ), (2806154593/5000000000 : ℝ), (-14647/10000000000 : ℝ)] ![(5000000129843/10000000000000 : ℝ), (49999988715377/100000000000000 : ℝ), (2493667/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5612310363/10000000000 : ℝ)|^6 ≤ (5000000129843/10000000000000 : ℝ)^5
        have hw : |(5612310363/10000000000 : ℝ)|=(5612310363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2806154593/5000000000 : ℝ)|^6 ≤ (49999988715377/100000000000000 : ℝ)^5
        have hw : |(2806154593/5000000000 : ℝ)|=(2806154593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14647/10000000000 : ℝ)|^6 ≤ (2493667/25000000000000 : ℝ)^5
        have hw : |(-14647/10000000000 : ℝ)|=(14647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330057_s0_7 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-1261659577/5000000000 : ℝ)*x 0 + (425039657/5000000000 : ℝ)*x 1 + (3962534197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1261659577/5000000000 : ℝ)^6 ≤ (4789681443151/25000000000000 : ℝ)^5 := by
    have hnat : (1261659577 : ℕ)^6*25000000000000^5 ≤ 4789681443151^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1261659577 5000000000 4789681443151 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425039657/5000000000 : ℝ)^6 ≤ (649024887731/12500000000000 : ℝ)^5 := by
    have hnat : (425039657 : ℕ)^6*12500000000000^5 ≤ 649024887731^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425039657 5000000000 649024887731 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3962534197/5000000000 : ℝ)^6 ≤ (75649075110379/100000000000000 : ℝ)^5 := by
    have hnat : (3962534197 : ℕ)^6*100000000000000^5 ≤ 75649075110379^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3962534197 5000000000 75649075110379 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1261659577/5000000000 : ℝ), (425039657/5000000000 : ℝ), (3962534197/5000000000 : ℝ)] ![(4789681443151/25000000000000 : ℝ), (649024887731/12500000000000 : ℝ), (75649075110379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1261659577/5000000000 : ℝ)|^6 ≤ (4789681443151/25000000000000 : ℝ)^5
        have hw : |(-1261659577/5000000000 : ℝ)|=(1261659577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(425039657/5000000000 : ℝ)|^6 ≤ (649024887731/12500000000000 : ℝ)^5
        have hw : |(425039657/5000000000 : ℝ)|=(425039657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3962534197/5000000000 : ℝ)|^6 ≤ (75649075110379/100000000000000 : ℝ)^5
        have hw : |(3962534197/5000000000 : ℝ)|=(3962534197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330057_s0_8 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (988916167/5000000000 : ℝ)*x 0 + (-736829023/5000000000 : ℝ)*x 1 + (63400547/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (988916167/5000000000 : ℝ)^6 ≤ (178787594033/1250000000000 : ℝ)^5 := by
    have hnat : (988916167 : ℕ)^6*1250000000000^5 ≤ 178787594033^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988916167 5000000000 178787594033 1250000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (736829023/5000000000 : ℝ)^6 ≤ (2511979392367/25000000000000 : ℝ)^5 := by
    have hnat : (736829023 : ℕ)^6*25000000000000^5 ≤ 2511979392367^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736829023 5000000000 2511979392367 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63400547/80000000 : ℝ)^6 ≤ (3782453744637/5000000000000 : ℝ)^5 := by
    have hnat : (63400547 : ℕ)^6*5000000000000^5 ≤ 3782453744637^5*80000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63400547 80000000 3782453744637 5000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(988916167/5000000000 : ℝ), (-736829023/5000000000 : ℝ), (63400547/80000000 : ℝ)] ![(178787594033/1250000000000 : ℝ), (2511979392367/25000000000000 : ℝ), (3782453744637/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(988916167/5000000000 : ℝ)|^6 ≤ (178787594033/1250000000000 : ℝ)^5
        have hw : |(988916167/5000000000 : ℝ)|=(988916167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-736829023/5000000000 : ℝ)|^6 ≤ (2511979392367/25000000000000 : ℝ)^5
        have hw : |(-736829023/5000000000 : ℝ)|=(736829023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(63400547/80000000 : ℝ)|^6 ≤ (3782453744637/5000000000000 : ℝ)^5
        have hw : |(63400547/80000000 : ℝ)|=(63400547/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330057_s0_9 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (30039061/80000000 : ℝ)*x 0 + (1470336849/2000000000 : ℝ)*x 1 + (-7157/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (30039061/80000000 : ℝ)^6 ≤ (15434254006933/50000000000000 : ℝ)^5 := by
    have hnat : (30039061 : ℕ)^6*50000000000000^5 ≤ 15434254006933^5*80000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30039061 80000000 15434254006933 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1470336849/2000000000 : ℝ)^6 ≤ (34564813611593/50000000000000 : ℝ)^5 := by
    have hnat : (1470336849 : ℕ)^6*50000000000000^5 ≤ 34564813611593^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1470336849 2000000000 34564813611593 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7157/62500000 : ℝ)^6 ≤ (466188127/25000000000000 : ℝ)^5 := by
    have hnat : (7157 : ℕ)^6*25000000000000^5 ≤ 466188127^5*62500000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7157 62500000 466188127 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(30039061/80000000 : ℝ), (1470336849/2000000000 : ℝ), (-7157/62500000 : ℝ)] ![(15434254006933/50000000000000 : ℝ), (34564813611593/50000000000000 : ℝ), (466188127/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(30039061/80000000 : ℝ)|^6 ≤ (15434254006933/50000000000000 : ℝ)^5
        have hw : |(30039061/80000000 : ℝ)|=(30039061/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1470336849/2000000000 : ℝ)|^6 ≤ (34564813611593/50000000000000 : ℝ)^5
        have hw : |(1470336849/2000000000 : ℝ)|=(1470336849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7157/62500000 : ℝ)|^6 ≤ (466188127/25000000000000 : ℝ)^5
        have hw : |(-7157/62500000 : ℝ)|=(7157/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330057_s0_13 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2708399957/10000000000 : ℝ)*x 0 + (1470336849/2000000000 : ℝ)*x 1 + (1469414143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2708399957/10000000000 : ℝ)^6 ≤ (5214292222999/25000000000000 : ℝ)^5 := by
    have hnat : (2708399957 : ℕ)^6*25000000000000^5 ≤ 5214292222999^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708399957 10000000000 5214292222999 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1470336849/2000000000 : ℝ)^6 ≤ (34564813611593/50000000000000 : ℝ)^5 := by
    have hnat : (1470336849 : ℕ)^6*50000000000000^5 ≤ 34564813611593^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1470336849 2000000000 34564813611593 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1469414143/10000000000 : ℝ)^6 ≤ (10013203873557/100000000000000 : ℝ)^5 := by
    have hnat : (1469414143 : ℕ)^6*100000000000000^5 ≤ 10013203873557^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1469414143 10000000000 10013203873557 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2708399957/10000000000 : ℝ), (1470336849/2000000000 : ℝ), (1469414143/10000000000 : ℝ)] ![(5214292222999/25000000000000 : ℝ), (34564813611593/50000000000000 : ℝ), (10013203873557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2708399957/10000000000 : ℝ)|^6 ≤ (5214292222999/25000000000000 : ℝ)^5
        have hw : |(2708399957/10000000000 : ℝ)|=(2708399957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1470336849/2000000000 : ℝ)|^6 ≤ (34564813611593/50000000000000 : ℝ)^5
        have hw : |(1470336849/2000000000 : ℝ)|=(1470336849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1469414143/10000000000 : ℝ)|^6 ≤ (10013203873557/100000000000000 : ℝ)^5
        have hw : |(1469414143/10000000000 : ℝ)|=(1469414143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330057_s0_14 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-1346386863/10000000000 : ℝ)*x 0 + (2071952973/10000000000 : ℝ)*x 1 + (1588705813/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346386863/10000000000 : ℝ)^6 ≤ (4507895531547/50000000000000 : ℝ)^5 := by
    have hnat : (1346386863 : ℕ)^6*50000000000000^5 ≤ 4507895531547^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346386863 10000000000 4507895531547 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071952973/10000000000 : ℝ)^6 ≤ (3780906011633/25000000000000 : ℝ)^5 := by
    have hnat : (2071952973 : ℕ)^6*25000000000000^5 ≤ 3780906011633^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071952973 10000000000 3780906011633 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1588705813/2000000000 : ℝ)^6 ≤ (4741286554703/6250000000000 : ℝ)^5 := by
    have hnat : (1588705813 : ℕ)^6*6250000000000^5 ≤ 4741286554703^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588705813 2000000000 4741286554703 6250000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1346386863/10000000000 : ℝ), (2071952973/10000000000 : ℝ), (1588705813/2000000000 : ℝ)] ![(4507895531547/50000000000000 : ℝ), (3780906011633/25000000000000 : ℝ), (4741286554703/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1346386863/10000000000 : ℝ)|^6 ≤ (4507895531547/50000000000000 : ℝ)^5
        have hw : |(-1346386863/10000000000 : ℝ)|=(1346386863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2071952973/10000000000 : ℝ)|^6 ≤ (3780906011633/25000000000000 : ℝ)^5
        have hw : |(2071952973/10000000000 : ℝ)|=(2071952973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1588705813/2000000000 : ℝ)|^6 ≤ (4741286554703/6250000000000 : ℝ)^5
        have hw : |(1588705813/2000000000 : ℝ)|=(1588705813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330057_s0_15 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (187973159/2000000000 : ℝ)*x 0 + (-97070611/400000000 : ℝ)*x 1 + (1985881371/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (187973159/2000000000 : ℝ)^6 ≤ (1171410220583/20000000000000 : ℝ)^5 := by
    have hnat : (187973159 : ℕ)^6*20000000000000^5 ≤ 1171410220583^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187973159 2000000000 1171410220583 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97070611/400000000 : ℝ)^6 ≤ (18282405038251/100000000000000 : ℝ)^5 := by
    have hnat : (97070611 : ℕ)^6*100000000000000^5 ≤ 18282405038251^5*400000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97070611 400000000 18282405038251 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1985881371/2500000000 : ℝ)^6 ≤ (37930271918527/50000000000000 : ℝ)^5 := by
    have hnat : (1985881371 : ℕ)^6*50000000000000^5 ≤ 37930271918527^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985881371 2500000000 37930271918527 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(187973159/2000000000 : ℝ), (-97070611/400000000 : ℝ), (1985881371/2500000000 : ℝ)] ![(1171410220583/20000000000000 : ℝ), (18282405038251/100000000000000 : ℝ), (37930271918527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(187973159/2000000000 : ℝ)|^6 ≤ (1171410220583/20000000000000 : ℝ)^5
        have hw : |(187973159/2000000000 : ℝ)|=(187973159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-97070611/400000000 : ℝ)|^6 ≤ (18282405038251/100000000000000 : ℝ)^5
        have hw : |(-97070611/400000000 : ℝ)|=(97070611/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1985881371/2500000000 : ℝ)|^6 ≤ (37930271918527/50000000000000 : ℝ)^5
        have hw : |(1985881371/2500000000 : ℝ)|=(1985881371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330057_s0_16 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (7648008209/10000000000 : ℝ)*x 0 + (3411365877/10000000000 : ℝ)*x 1 + (-1148817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7648008209/10000000000 : ℝ)^6 ≤ (72486647560271/100000000000000 : ℝ)^5 := by
    have hnat : (7648008209 : ℕ)^6*100000000000000^5 ≤ 72486647560271^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7648008209 10000000000 72486647560271 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3411365877/10000000000 : ℝ)^6 ≤ (3438935055473/12500000000000 : ℝ)^5 := by
    have hnat : (3411365877 : ℕ)^6*12500000000000^5 ≤ 3438935055473^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3411365877 10000000000 3438935055473 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1148817/10000000000 : ℝ)^6 ≤ (233997403/12500000000000 : ℝ)^5 := by
    have hnat : (1148817 : ℕ)^6*12500000000000^5 ≤ 233997403^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148817 10000000000 233997403 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7648008209/10000000000 : ℝ), (3411365877/10000000000 : ℝ), (-1148817/10000000000 : ℝ)] ![(72486647560271/100000000000000 : ℝ), (3438935055473/12500000000000 : ℝ), (233997403/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7648008209/10000000000 : ℝ)|^6 ≤ (72486647560271/100000000000000 : ℝ)^5
        have hw : |(7648008209/10000000000 : ℝ)|=(7648008209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3411365877/10000000000 : ℝ)|^6 ≤ (3438935055473/12500000000000 : ℝ)^5
        have hw : |(3411365877/10000000000 : ℝ)|=(3411365877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1148817/10000000000 : ℝ)|^6 ≤ (233997403/12500000000000 : ℝ)^5
        have hw : |(-1148817/10000000000 : ℝ)|=(1148817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330057_s0_20 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (7031288627/10000000000 : ℝ)*x 0 + (3089959729/10000000000 : ℝ)*x 1 + (184065151/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7031288627/10000000000 : ℝ)^6 ≤ (32765131484659/50000000000000 : ℝ)^5 := by
    have hnat : (7031288627 : ℕ)^6*50000000000000^5 ≤ 32765131484659^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7031288627 10000000000 32765131484659 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3089959729/10000000000 : ℝ)^6 ≤ (1221556017921/5000000000000 : ℝ)^5 := by
    have hnat : (3089959729 : ℕ)^6*5000000000000^5 ≤ 1221556017921^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3089959729 10000000000 1221556017921 5000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184065151/1250000000 : ℝ)^6 ≤ (2509654163697/25000000000000 : ℝ)^5 := by
    have hnat : (184065151 : ℕ)^6*25000000000000^5 ≤ 2509654163697^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184065151 1250000000 2509654163697 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7031288627/10000000000 : ℝ), (3089959729/10000000000 : ℝ), (184065151/1250000000 : ℝ)] ![(32765131484659/50000000000000 : ℝ), (1221556017921/5000000000000 : ℝ), (2509654163697/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7031288627/10000000000 : ℝ)|^6 ≤ (32765131484659/50000000000000 : ℝ)^5
        have hw : |(7031288627/10000000000 : ℝ)|=(7031288627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3089959729/10000000000 : ℝ)|^6 ≤ (1221556017921/5000000000000 : ℝ)^5
        have hw : |(3089959729/10000000000 : ℝ)|=(3089959729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(184065151/1250000000 : ℝ)|^6 ≤ (2509654163697/25000000000000 : ℝ)^5
        have hw : |(184065151/1250000000 : ℝ)|=(184065151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330057_s0_21 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-287827349/625000000 : ℝ)*x 0 + (351047453/2000000000 : ℝ)*x 1 + (5440545961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (287827349/625000000 : ℝ)^6 ≤ (39436870869843/100000000000000 : ℝ)^5 := by
    have hnat : (287827349 : ℕ)^6*100000000000000^5 ≤ 39436870869843^5*625000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287827349 625000000 39436870869843 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (351047453/2000000000 : ℝ)^6 ≤ (12393757571641/100000000000000 : ℝ)^5 := by
    have hnat : (351047453 : ℕ)^6*100000000000000^5 ≤ 12393757571641^5*2000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351047453 2000000000 12393757571641 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440545961/10000000000 : ℝ)^6 ≤ (48169371545771/100000000000000 : ℝ)^5 := by
    have hnat : (5440545961 : ℕ)^6*100000000000000^5 ≤ 48169371545771^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440545961 10000000000 48169371545771 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-287827349/625000000 : ℝ), (351047453/2000000000 : ℝ), (5440545961/10000000000 : ℝ)] ![(39436870869843/100000000000000 : ℝ), (12393757571641/100000000000000 : ℝ), (48169371545771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-287827349/625000000 : ℝ)|^6 ≤ (39436870869843/100000000000000 : ℝ)^5
        have hw : |(-287827349/625000000 : ℝ)|=(287827349/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(351047453/2000000000 : ℝ)|^6 ≤ (12393757571641/100000000000000 : ℝ)^5
        have hw : |(351047453/2000000000 : ℝ)|=(351047453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440545961/10000000000 : ℝ)|^6 ≤ (48169371545771/100000000000000 : ℝ)^5
        have hw : |(5440545961/10000000000 : ℝ)|=(5440545961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330057_s0_22 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (85134181/1000000000 : ℝ)*x 0 + (-560524659/1250000000 : ℝ)*x 1 + (6223401981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85134181/1000000000 : ℝ)^6 ≤ (1040290782831/20000000000000 : ℝ)^5 := by
    have hnat : (85134181 : ℕ)^6*20000000000000^5 ≤ 1040290782831^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85134181 1000000000 1040290782831 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560524659/1250000000 : ℝ)^6 ≤ (7639266270157/20000000000000 : ℝ)^5 := by
    have hnat : (560524659 : ℕ)^6*20000000000000^5 ≤ 7639266270157^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560524659 1250000000 7639266270157 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6223401981/10000000000 : ℝ)^6 ≤ (11320442944473/20000000000000 : ℝ)^5 := by
    have hnat : (6223401981 : ℕ)^6*20000000000000^5 ≤ 11320442944473^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6223401981 10000000000 11320442944473 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(85134181/1000000000 : ℝ), (-560524659/1250000000 : ℝ), (6223401981/10000000000 : ℝ)] ![(1040290782831/20000000000000 : ℝ), (7639266270157/20000000000000 : ℝ), (11320442944473/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(85134181/1000000000 : ℝ)|^6 ≤ (1040290782831/20000000000000 : ℝ)^5
        have hw : |(85134181/1000000000 : ℝ)|=(85134181/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-560524659/1250000000 : ℝ)|^6 ≤ (7639266270157/20000000000000 : ℝ)^5
        have hw : |(-560524659/1250000000 : ℝ)|=(560524659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6223401981/10000000000 : ℝ)|^6 ≤ (11320442944473/20000000000000 : ℝ)^5
        have hw : |(6223401981/10000000000 : ℝ)|=(6223401981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330057_s0_23 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (5965103513/10000000000 : ℝ)*x 0 + (2627510351/5000000000 : ℝ)*x 1 + (1869/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5965103513/10000000000 : ℝ)^6 ≤ (10758991811353/20000000000000 : ℝ)^5 := by
    have hnat : (5965103513 : ℕ)^6*20000000000000^5 ≤ 10758991811353^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5965103513 10000000000 10758991811353 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627510351/5000000000 : ℝ)^6 ≤ (9241007296919/20000000000000 : ℝ)^5 := by
    have hnat : (2627510351 : ℕ)^6*20000000000000^5 ≤ 9241007296919^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627510351 5000000000 9241007296919 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1869/2500000000 : ℝ)^6 ≤ (4450443/100000000000000 : ℝ)^5 := by
    have hnat : (1869 : ℕ)^6*100000000000000^5 ≤ 4450443^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869 2500000000 4450443 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5965103513/10000000000 : ℝ), (2627510351/5000000000 : ℝ), (1869/2500000000 : ℝ)] ![(10758991811353/20000000000000 : ℝ), (9241007296919/20000000000000 : ℝ), (4450443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5965103513/10000000000 : ℝ)|^6 ≤ (10758991811353/20000000000000 : ℝ)^5
        have hw : |(5965103513/10000000000 : ℝ)|=(5965103513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627510351/5000000000 : ℝ)|^6 ≤ (9241007296919/20000000000000 : ℝ)^5
        have hw : |(2627510351/5000000000 : ℝ)|=(2627510351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1869/2500000000 : ℝ)|^6 ≤ (4450443/100000000000000 : ℝ)^5
        have hw : |(1869/2500000000 : ℝ)|=(1869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330057_s0_27 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (2110616743/10000000000 : ℝ)*x 0 + (2627510351/5000000000 : ℝ)*x 1 + (4497471249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110616743/10000000000 : ℝ)^6 ≤ (7731455474021/50000000000000 : ℝ)^5 := by
    have hnat : (2110616743 : ℕ)^6*50000000000000^5 ≤ 7731455474021^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110616743 10000000000 7731455474021 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627510351/5000000000 : ℝ)^6 ≤ (9241007296919/20000000000000 : ℝ)^5 := by
    have hnat : (2627510351 : ℕ)^6*20000000000000^5 ≤ 9241007296919^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627510351 5000000000 9241007296919 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497471249/10000000000 : ℝ)^6 ≤ (38332052549573/100000000000000 : ℝ)^5 := by
    have hnat : (4497471249 : ℕ)^6*100000000000000^5 ≤ 38332052549573^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497471249 10000000000 38332052549573 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2110616743/10000000000 : ℝ), (2627510351/5000000000 : ℝ), (4497471249/10000000000 : ℝ)] ![(7731455474021/50000000000000 : ℝ), (9241007296919/20000000000000 : ℝ), (38332052549573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2110616743/10000000000 : ℝ)|^6 ≤ (7731455474021/50000000000000 : ℝ)^5
        have hw : |(2110616743/10000000000 : ℝ)|=(2110616743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627510351/5000000000 : ℝ)|^6 ≤ (9241007296919/20000000000000 : ℝ)^5
        have hw : |(2627510351/5000000000 : ℝ)|=(2627510351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497471249/10000000000 : ℝ)|^6 ≤ (38332052549573/100000000000000 : ℝ)^5
        have hw : |(4497471249/10000000000 : ℝ)|=(4497471249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330057_s1_0 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (-800430829/2500000000 : ℝ)*x 0 + (320101849/1000000000 : ℝ)*x 1 + (5520124137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (800430829/2500000000 : ℝ)^6 ≤ (6373831337247/25000000000000 : ℝ)^5 := by
    have hnat : (800430829 : ℕ)^6*25000000000000^5 ≤ 6373831337247^5*2500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800430829 2500000000 6373831337247 25000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (320101849/1000000000 : ℝ)^6 ≤ (25488590461253/100000000000000 : ℝ)^5 := by
    have hnat : (320101849 : ℕ)^6*100000000000000^5 ≤ 25488590461253^5*1000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320101849 1000000000 25488590461253 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5520124137/10000000000 : ℝ)^6 ≤ (4901608417621/10000000000000 : ℝ)^5 := by
    have hnat : (5520124137 : ℕ)^6*10000000000000^5 ≤ 4901608417621^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520124137 10000000000 4901608417621 10000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-800430829/2500000000 : ℝ), (320101849/1000000000 : ℝ), (5520124137/10000000000 : ℝ)] ![(6373831337247/25000000000000 : ℝ), (25488590461253/100000000000000 : ℝ), (4901608417621/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-800430829/2500000000 : ℝ)|^6 ≤ (6373831337247/25000000000000 : ℝ)^5
        have hw : |(-800430829/2500000000 : ℝ)|=(800430829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(320101849/1000000000 : ℝ)|^6 ≤ (25488590461253/100000000000000 : ℝ)^5
        have hw : |(320101849/1000000000 : ℝ)|=(320101849/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5520124137/10000000000 : ℝ)|^6 ≤ (4901608417621/10000000000000 : ℝ)^5
        have hw : |(5520124137/10000000000 : ℝ)|=(5520124137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330057_s1_1 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (3200990927/10000000000 : ℝ)*x 0 + (-1600143131/5000000000 : ℝ)*x 1 + (345089843/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3200990927/10000000000 : ℝ)^6 ≤ (1593020443253/6250000000000 : ℝ)^5 := by
    have hnat : (3200990927 : ℕ)^6*6250000000000^5 ≤ 1593020443253^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3200990927 10000000000 1593020443253 6250000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1600143131/5000000000 : ℝ)^6 ≤ (3185199256351/12500000000000 : ℝ)^5 := by
    have hnat : (1600143131 : ℕ)^6*12500000000000^5 ≤ 3185199256351^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1600143131 5000000000 3185199256351 12500000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345089843/625000000 : ℝ)^6 ≤ (24515039414951/50000000000000 : ℝ)^5 := by
    have hnat : (345089843 : ℕ)^6*50000000000000^5 ≤ 24515039414951^5*625000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345089843 625000000 24515039414951 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3200990927/10000000000 : ℝ), (-1600143131/5000000000 : ℝ), (345089843/625000000 : ℝ)] ![(1593020443253/6250000000000 : ℝ), (3185199256351/12500000000000 : ℝ), (24515039414951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3200990927/10000000000 : ℝ)|^6 ≤ (1593020443253/6250000000000 : ℝ)^5
        have hw : |(3200990927/10000000000 : ℝ)|=(3200990927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1600143131/5000000000 : ℝ)|^6 ≤ (3185199256351/12500000000000 : ℝ)^5
        have hw : |(-1600143131/5000000000 : ℝ)|=(1600143131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(345089843/625000000 : ℝ)|^6 ≤ (24515039414951/50000000000000 : ℝ)^5
        have hw : |(345089843/625000000 : ℝ)|=(345089843/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330057_s1_2 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (267809889/500000000 : ℝ)*x 0 + (2678675253/5000000000 : ℝ)*x 1 + (-110445429/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267809889/500000000 : ℝ)^6 ≤ (23637303445563/50000000000000 : ℝ)^5 := by
    have hnat : (267809889 : ℕ)^6*50000000000000^5 ≤ 23637303445563^5*500000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267809889 500000000 23637303445563 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2678675253/5000000000 : ℝ)^6 ≤ (9457363222689/20000000000000 : ℝ)^5 := by
    have hnat : (2678675253 : ℕ)^6*20000000000000^5 ≤ 9457363222689^5*5000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678675253 5000000000 9457363222689 20000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110445429/1250000000 : ℝ)^6 ≤ (5438576980347/100000000000000 : ℝ)^5 := by
    have hnat : (110445429 : ℕ)^6*100000000000000^5 ≤ 5438576980347^5*1250000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110445429 1250000000 5438576980347 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267809889/500000000 : ℝ), (2678675253/5000000000 : ℝ), (-110445429/1250000000 : ℝ)] ![(23637303445563/50000000000000 : ℝ), (9457363222689/20000000000000 : ℝ), (5438576980347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267809889/500000000 : ℝ)|^6 ≤ (23637303445563/50000000000000 : ℝ)^5
        have hw : |(267809889/500000000 : ℝ)|=(267809889/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2678675253/5000000000 : ℝ)|^6 ≤ (9457363222689/20000000000000 : ℝ)^5
        have hw : |(2678675253/5000000000 : ℝ)|=(2678675253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-110445429/1250000000 : ℝ)|^6 ≤ (5438576980347/100000000000000 : ℝ)^5
        have hw : |(-110445429/1250000000 : ℝ)|=(110445429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c330057_s1_6 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ)) (x : Fin 3 → ℝ) :
    (4195746381/10000000000 : ℝ)*x 0 + (4196649363/10000000000 : ℝ)*x 1 + (3611192709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4195746381/10000000000 : ℝ)^6 ≤ (35267207606421/100000000000000 : ℝ)^5 := by
    have hnat : (4195746381 : ℕ)^6*100000000000000^5 ≤ 35267207606421^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4195746381 10000000000 35267207606421 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4196649363/10000000000 : ℝ)^6 ≤ (35276315784873/100000000000000 : ℝ)^5 := by
    have hnat : (4196649363 : ℕ)^6*100000000000000^5 ≤ 35276315784873^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4196649363 10000000000 35276315784873 100000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3611192709/10000000000 : ℝ)^6 ≤ (14728238295131/50000000000000 : ℝ)^5 := by
    have hnat : (3611192709 : ℕ)^6*50000000000000^5 ≤ 14728238295131^5*10000000000^6 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3611192709 10000000000 14728238295131 50000000000000 6 5 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6 : ℝ)) 6 5 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4195746381/10000000000 : ℝ), (4196649363/10000000000 : ℝ), (3611192709/10000000000 : ℝ)] ![(35267207606421/100000000000000 : ℝ), (35276315784873/100000000000000 : ℝ), (14728238295131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4195746381/10000000000 : ℝ)|^6 ≤ (35267207606421/100000000000000 : ℝ)^5
        have hw : |(4195746381/10000000000 : ℝ)|=(4195746381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4196649363/10000000000 : ℝ)|^6 ≤ (35276315784873/100000000000000 : ℝ)^5
        have hw : |(4196649363/10000000000 : ℝ)|=(4196649363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3611192709/10000000000 : ℝ)|^6 ≤ (14728238295131/50000000000000 : ℝ)^5
        have hw : |(3611192709/10000000000 : ℝ)|=(3611192709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c330057 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (41553/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (41553/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (41553/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (41553/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (41553/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (41553/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (31839/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1238278459541601/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(794260151493959/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (95/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^95 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^95*1^16 ≤ 1^16*1^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11238278459541601/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11238278459541601/10000000000000000 : ℝ)^95 := by
      have hnat : (2 : ℕ)^16*10000000000000000^95 ≤ 11238278459541601^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11238278459541601 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11238278459541601/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (300813465275889/250000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (300813465275889/250000000000000 : ℝ)^95 := by
      have hnat : (3 : ℕ)^16*250000000000000^95 ≤ 300813465275889^95*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 300813465275889 250000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (300813465275889/250000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1238278459541601/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(794260151493959/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1238278459541601/10000000000000000 : ℝ)) (beta := (794260151493959/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1238278459541601/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(794260151493959/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2888640981/10000000000 : ℝ)*X 0 0+(57772841/200000000 : ℝ)*X 0 1+(6070044633/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2888640977/10000000000 : ℝ)*X 1 0+(-2888642047/10000000000 : ℝ)*X 1 1+(3035022319/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5612310363/10000000000 : ℝ)*X 2 0+(2806154593/5000000000 : ℝ)*X 2 1+(-14647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1261659577/5000000000 : ℝ)*X 0 0+(425039657/5000000000 : ℝ)*X 0 1+(3962534197/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((988916167/5000000000 : ℝ)*X 1 0+(-736829023/5000000000 : ℝ)*X 1 1+(63400547/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((30039061/80000000 : ℝ)*X 2 0+(1470336849/2000000000 : ℝ)*X 2 1+(-7157/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2708399957/10000000000 : ℝ)*X 0 0+(1470336849/2000000000 : ℝ)*X 0 1+(1469414143/10000000000 : ℝ)*X 0 2+(2708399957/10000000000 : ℝ)*X 1 0+(1470336849/2000000000 : ℝ)*X 1 1+(1469414143/10000000000 : ℝ)*X 1 2+(2708399957/10000000000 : ℝ)*X 2 0+(1470336849/2000000000 : ℝ)*X 2 1+(1469414143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1346386863/10000000000 : ℝ)*X 0 0+(2071952973/10000000000 : ℝ)*X 0 1+(1588705813/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((187973159/2000000000 : ℝ)*X 1 0+(-97070611/400000000 : ℝ)*X 1 1+(1985881371/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7648008209/10000000000 : ℝ)*X 2 0+(3411365877/10000000000 : ℝ)*X 2 1+(-1148817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((7031288627/10000000000 : ℝ)*X 0 0+(3089959729/10000000000 : ℝ)*X 0 1+(184065151/1250000000 : ℝ)*X 0 2+(7031288627/10000000000 : ℝ)*X 1 0+(3089959729/10000000000 : ℝ)*X 1 1+(184065151/1250000000 : ℝ)*X 1 2+(7031288627/10000000000 : ℝ)*X 2 0+(3089959729/10000000000 : ℝ)*X 2 1+(184065151/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-287827349/625000000 : ℝ)*X 0 0+(351047453/2000000000 : ℝ)*X 0 1+(5440545961/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((85134181/1000000000 : ℝ)*X 1 0+(-560524659/1250000000 : ℝ)*X 1 1+(6223401981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((5965103513/10000000000 : ℝ)*X 2 0+(2627510351/5000000000 : ℝ)*X 2 1+(1869/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((2110616743/10000000000 : ℝ)*X 0 0+(2627510351/5000000000 : ℝ)*X 0 1+(4497471249/10000000000 : ℝ)*X 0 2+(2110616743/10000000000 : ℝ)*X 1 0+(2627510351/5000000000 : ℝ)*X 1 1+(4497471249/10000000000 : ℝ)*X 1 2+(2110616743/10000000000 : ℝ)*X 2 0+(2627510351/5000000000 : ℝ)*X 2 1+(4497471249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((5829/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5829/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15331514229460962280953/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (181259460669/1000000000000 : ℝ)*(base5) + (31044358387/25000000000 : ℝ)*(base7) + (8694338813/200000000000 : ℝ)*(base59) + (824693084211/500000000000 : ℝ)*(major_s0_0) + (824693084211/500000000000 : ℝ)*(major_s0_1) + (824693084211/500000000000 : ℝ)*(major_s0_2) + (5394547/1000000000000 : ℝ)*(sp_s0_0) + (5722823/1000000000000 : ℝ)*(sp_s0_1) + (478902856917/250000000000 : ℝ)*(sp_s0_7) + (957788066677/500000000000 : ℝ)*(sp_s0_8) + (524220155583/250000000000 : ℝ)*(sp_s0_9) + (892357205229/500000000000 : ℝ)*(sp_s0_13) + (4339449/1000000000000 : ℝ)*(sp_s0_14) + (19652743/500000000000 : ℝ)*(sp_s0_15) + (724199535647/1000000000000 : ℝ)*(f.failure) + (29931580651/15625000000 : ℝ)*(f.sum) + (44339583/500000000000000000000 : ℝ)*base63 + (3212089360718651/5000000000000000000000000000 : ℝ)*base65 + (1399829983781349/5000000000000000000000000000 : ℝ)*base67 + (3174196057738189/5000000000000000000000000000 : ℝ)*base69 + (61026195759769/2500000000000000000000000000 : ℝ)*base70 + (5335264273781349/5000000000000000000000000000 : ℝ)*base73 + (3738244047761811/5000000000000000000000000000 : ℝ)*base75 + (5158213175761811/5000000000000000000000000000 : ℝ)*base77 + (287275131281349/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (11191/100000000000000000 : ℝ)*base87 + (11191/100000000000000000 : ℝ)*base89 + (11191/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(58061/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(58061/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (124096068616191924939/9765625000000000000000000 : ℝ) := by norm_num
    linear_combination (191832774429/1000000000000 : ℝ)*(base5) + (620000274837/500000000000 : ℝ)*(base7) + (13169321789/1000000000000 : ℝ)*(base60) + (25562108419/15625000000 : ℝ)*(major_s0_0) + (25562108419/15625000000 : ℝ)*(major_s0_1) + (25562108419/15625000000 : ℝ)*(major_s0_2) + (4318881/500000000000 : ℝ)*(sp_s0_0) + (1361349/500000000000 : ℝ)*(sp_s0_1) + (11307089/250000000000 : ℝ)*(sp_s0_7) + (236946805727/125000000000 : ℝ)*(sp_s0_14) + (189562260777/100000000000 : ℝ)*(sp_s0_15) + (2087461086363/1000000000000 : ℝ)*(sp_s0_16) + (1766478813439/1000000000000 : ℝ)*(sp_s0_20) + (2981467/1000000000000 : ℝ)*(sp_s0_22) + (718311038193/1000000000000 : ℝ)*(f.failure) + (379125662387/200000000000 : ℝ)*(f.sum) + (4631687699/10000000000000000000000 : ℝ)*base62 + (1859377489447/4882812500000000000000000 : ℝ)*base65 + (102070282134571/156250000000000000000000000 : ℝ)*base67 + (16282375005347/78125000000000000000000000 : ℝ)*base68 + (7877983001123/156250000000000000000000000 : ℝ)*base71 + (6622956440527/78125000000000000000000000 : ℝ)*base72 + (52562738463819/156250000000000000000000000 : ℝ)*base75 + (53737406245069/156250000000000000000000000 : ℝ)*base77 + (1839057871483/156250000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (29671/100000000000000000 : ℝ)*base86 + (29671/100000000000000000 : ℝ)*base88 + (29671/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(667/3125 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(667/3125 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (49348198788999235663293/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (170535980633/200000000000 : ℝ)*(base5) + (402449543989/1000000000000 : ℝ)*(base7) + (329371/62500000000 : ℝ)*(base40) + (149843790089/1000000000000 : ℝ)*(base50) + (840905194709/1000000000000 : ℝ)*(base59) + (1363011091557/1000000000000 : ℝ)*(major_s0_0) + (1363011091557/1000000000000 : ℝ)*(major_s0_1) + (1363011091557/1000000000000 : ℝ)*(major_s0_2) + (482419/1000000000000 : ℝ)*(sp_s0_0) + (128529689/1000000000000 : ℝ)*(sp_s0_2) + (478499586533/250000000000 : ℝ)*(sp_s0_21) + (1913998828551/1000000000000 : ℝ)*(sp_s0_22) + (2766550202027/1000000000000 : ℝ)*(sp_s0_23) + (29645970997/200000000000 : ℝ)*(sp_s0_27) + (598460214161/1000000000000 : ℝ)*(f.failure) + (1913998828551/1000000000000 : ℝ)*(f.sum) + (151114017/625000000000000000000 : ℝ)*base63 + (3706268281404163/10000000000000000000000000000 : ℝ)*base64 + (4461965462595837/10000000000000000000000000000 : ℝ)*base66 + (1609072026362757/10000000000000000000000000000 : ℝ)*base68 + (3867093309020703/5000000000000000000000000000 : ℝ)*base70 + (3559655085404163/10000000000000000000000000000 : ℝ)*base73 + (130260951637243/10000000000000000000000000000 : ℝ)*base74 + (7730644716637243/10000000000000000000000000000 : ℝ)*base76 + (402828214404163/5000000000000000000000000000 : ℝ)*base79 + (110233/100000000000000000 : ℝ)*base87 + (110233/100000000000000000 : ℝ)*base89 + (110233/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (5829/10000 : ℝ) ^ (95/16 : ℝ) ≤ (4057090574755779499/100000000000000000000 : ℝ) := by
    have hpowers : (5829/10000 : ℝ)^95 ≤ (4057090574755779499/100000000000000000000 : ℝ)^16 := by
      have hnat : (5829 : ℕ)^95*100000000000000000000^16 ≤ 4057090574755779499^16*10000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5829 10000 4057090574755779499 100000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5829/10000 : ℝ)) (X := (4057090574755779499/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (104057090574755779499/100000000000000000000 : ℝ) ≤ (10067205047207681/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (104057090574755779499/100000000000000000000 : ℝ)^16 ≤ (10067205047207681/10000000000000000 : ℝ)^95 := by
      have hnat : (104057090574755779499 : ℕ)^16*10000000000000000^95 ≤ 10067205047207681^95*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104057090574755779499 100000000000000000000 10067205047207681 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10067205047207681/10000000000000000 : ℝ)) (X := (104057090574755779499/100000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (54057090574755779499/50000000000000000000 : ℝ) ≤ (10132265326381101/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (54057090574755779499/50000000000000000000 : ℝ)^16 ≤ (10132265326381101/10000000000000000 : ℝ)^95 := by
      have hnat : (54057090574755779499 : ℕ)^16*10000000000000000^95 ≤ 10132265326381101^95*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54057090574755779499 50000000000000000000 10132265326381101 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10132265326381101/10000000000000000 : ℝ)) (X := (54057090574755779499/50000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(67205047207681/5829000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3253013958671/291450000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (5829/10000 : ℝ)) (alpha := (67205047207681/5829000000000000 : ℝ)) (beta := (3253013958671/291450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5829/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(67205047207681/5829000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3253013958671/291450000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (58061/100000 : ℝ) ^ (95/16 : ℝ) ≤ (396336698349814979/10000000000000000000 : ℝ) := by
    have hpowers : (58061/100000 : ℝ)^95 ≤ (396336698349814979/10000000000000000000 : ℝ)^16 := by
      have hnat : (58061 : ℕ)^95*10000000000000000000^16 ≤ 396336698349814979^16*100000^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58061 100000 396336698349814979 10000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (58061/100000 : ℝ)) (X := (396336698349814979/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (10396336698349814979/10000000000000000000 : ℝ) ≤ (2516419330507537/2500000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (10396336698349814979/10000000000000000000 : ℝ)^16 ≤ (2516419330507537/2500000000000000 : ℝ)^95 := by
      have hnat : (10396336698349814979 : ℕ)^16*2500000000000000^95 ≤ 2516419330507537^95*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10396336698349814979 10000000000000000000 2516419330507537 2500000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2516419330507537/2500000000000000 : ℝ)) (X := (10396336698349814979/10000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (5396336698349814979/5000000000000000000 : ℝ) ≤ (10129304503129071/10000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (5396336698349814979/5000000000000000000 : ℝ)^16 ≤ (10129304503129071/10000000000000000 : ℝ)^95 := by
      have hnat : (5396336698349814979 : ℕ)^16*10000000000000000^95 ≤ 10129304503129071^95*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5396336698349814979 5000000000000000000 10129304503129071 10000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10129304503129071/10000000000000000 : ℝ)) (X := (5396336698349814979/5000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(16419330507537/1451525000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(63627181098923/5806100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (58061/100000 : ℝ)) (alpha := (16419330507537/1451525000000000 : ℝ)) (beta := (63627181098923/5806100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (58061/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(16419330507537/1451525000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(63627181098923/5806100000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (667/3125 : ℝ) ^ (95/16 : ℝ) ≤ (10412982419321367/100000000000000000000 : ℝ) := by
    have hpowers : (667/3125 : ℝ)^95 ≤ (10412982419321367/100000000000000000000 : ℝ)^16 := by
      have hnat : (667 : ℕ)^95*100000000000000000000^16 ≤ 10412982419321367^16*3125^95 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        667 3125 10412982419321367 100000000000000000000 95 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (667/3125 : ℝ)) (X := (10412982419321367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100010412982419321367/100000000000000000000 : ℝ) ≤ (80001402951627/80000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (100010412982419321367/100000000000000000000 : ℝ)^16 ≤ (80001402951627/80000000000000 : ℝ)^95 := by
      have hnat : (100010412982419321367 : ℕ)^16*80000000000000^95 ≤ 80001402951627^95*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100010412982419321367 100000000000000000000 80001402951627 80000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80001402951627/80000000000000 : ℝ)) (X := (100010412982419321367/100000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50010412982419321367/50000000000000000000 : ℝ) ≤ (1000035072272341/1000000000000000 : ℝ) ^ (95/16 : ℝ) := by
    have hpowers : (50010412982419321367/50000000000000000000 : ℝ)^16 ≤ (1000035072272341/1000000000000000 : ℝ)^95 := by
      have hnat : (50010412982419321367 : ℕ)^16*1000000000000000^95 ≤ 1000035072272341^95*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010412982419321367 50000000000000000000 1000035072272341 1000000000000000 16 95 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000035072272341/1000000000000000 : ℝ)) (X := (50010412982419321367/50000000000000000000 : ℝ)) (by norm_num) 95 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1402951627/17075200000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(35070754007/426880000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (95/16 : ℝ)) (rho := (667/3125 : ℝ)) (alpha := (1402951627/17075200000000 : ℝ)) (beta := (35070754007/426880000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (667/3125 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1402951627/17075200000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(35070754007/426880000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-800430829/2500000000 : ℝ)*X 0 0+(320101849/1000000000 : ℝ)*X 0 1+(5520124137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3200990927/10000000000 : ℝ)*X 1 0+(-1600143131/5000000000 : ℝ)*X 1 1+(345089843/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((267809889/500000000 : ℝ)*X 2 0+(2678675253/5000000000 : ℝ)*X 2 1+(-110445429/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4195746381/10000000000 : ℝ)*X 0 0+(4196649363/10000000000 : ℝ)*X 0 1+(3611192709/10000000000 : ℝ)*X 0 2+(4195746381/10000000000 : ℝ)*X 1 0+(4196649363/10000000000 : ℝ)*X 1 1+(3611192709/10000000000 : ℝ)*X 1 2+(4195746381/10000000000 : ℝ)*X 2 0+(4196649363/10000000000 : ℝ)*X 2 1+(3611192709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c330057_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-533259/50000 : ℝ) < ((-227753/100000 : ℝ)*P 0+(-227753/100000 : ℝ)*P 1+(-227753/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-533259/50000 : ℝ) < (-703730603609084261371731/66700000000000000000000 : ℝ) := by norm_num
    linear_combination (13557/1000000000000 : ℝ)*(base5) + (9007/1000000000000 : ℝ)*(base7) + (3961/500000000000 : ℝ)*(base8) + (89/200000000000 : ℝ)*(base11) + (137/100000000000 : ℝ)*(base15) + (91495436671/62500000000 : ℝ)*(base59) + (22875421363/31250000000 : ℝ)*(base60) + (1138765003047/500000000000 : ℝ)*(major_s1_0) + (227753/100000 : ℝ)*(major_s1_1) + (227753/100000 : ℝ)*(major_s1_2) + (3516894545423/1000000000000 : ℝ)*(sp_s1_0) + (1758447273163/500000000000 : ℝ)*(sp_s1_1) + (1758447280627/500000000000 : ℝ)*(sp_s1_2) + (1000000001543/1000000000000 : ℝ)*(sp_s1_6) + (219805909231/62500000000 : ℝ)*(f.sum) + (15901119964480491/77453374000000000000000000000 : ℝ)*base62 + (6546324457457/6670000000000000000000000 : ℝ)*base65 + (47875712787391/290305000000000000000000000 : ℝ)*base67 + (10071945089/1334000000000000000000000 : ℝ)*base68 + (12206988447673237/22344500000000000000000000000 : ℝ)*base71 + (19720875066733/97150000000000000000000000 : ℝ)*base73 + (109715573423817/580610000000000000000000000 : ℝ)*base75 + (149086538711281/971500000000000000000000000 : ℝ)*base76 + (145443111674141447/5640626150000000000000000000000 : ℝ)*base78 + (3047/500000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (3047/500000000000 : ℝ)*base86 + (6093/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p030_b028 (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (c : Fin 88) (hlo : 57 ≤ c.val) (hhi : c.val < 58)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=57 := by omega
  rcases hc with rfl
  · exact collision_c330057 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (95/16 : ℝ) ≤ p) (hpb : p ≤ (6 : ℝ))
    (c : Fin 88) (hlo : 57 ≤ c.val) (hhi : c.val < 58)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (227753/100000 : ℝ) (31839/20000 : ℝ) (41553/50000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p030_b028 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p005_b032
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:28:23.22198+00:00
-- url     : https://prove2.me/submissions/4f0342d6-9d81-4814-b22c-9931b982ada7

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305075_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305075_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305075_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305075_s3
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305076_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305076_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305076_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c305076_s3
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
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
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c305075 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, true]]) : False := by
  have h0 := collision_c305075_s0 p hpa hpb X hX
  have h1 := collision_c305075_s1 p hpa hpb X hX h0
  have h2 := collision_c305075_s2 p hpa hpb X hX h1
  exact collision_c305075_s3 p hpa hpb X hX h2

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c305076 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]]) : False := by
  have h0 := collision_c305076_s0 p hpa hpb X hX
  have h1 := collision_c305076_s1 p hpa hpb X hX h0
  have h2 := collision_c305076_s2 p hpa hpb X hX h1
  exact collision_c305076_s3 p hpa hpb X hX h2

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
theorem collision_support_c305073_s0_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3884053797/10000000000 : ℝ)*x 0 + (-178188599/400000000 : ℝ)*x 1 + (4649534223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3884053797/10000000000 : ℝ)^67 ≤ (1804320001429/6250000000000 : ℝ)^51 := by
    have hnat : (3884053797 : ℕ)^67*6250000000000^51 ≤ 1804320001429^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3884053797 10000000000 1804320001429 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (178188599/400000000 : ℝ)^67 ≤ (17282866850019/50000000000000 : ℝ)^51 := by
    have hnat : (178188599 : ℕ)^67*50000000000000^51 ≤ 17282866850019^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178188599 400000000 17282866850019 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4649534223/10000000000 : ℝ)^67 ≤ (3656514626133/10000000000000 : ℝ)^51 := by
    have hnat : (4649534223 : ℕ)^67*10000000000000^51 ≤ 3656514626133^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4649534223 10000000000 3656514626133 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3884053797/10000000000 : ℝ), (-178188599/400000000 : ℝ), (4649534223/10000000000 : ℝ)] ![(1804320001429/6250000000000 : ℝ), (17282866850019/50000000000000 : ℝ), (3656514626133/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3884053797/10000000000 : ℝ)|^67 ≤ (1804320001429/6250000000000 : ℝ)^51
        have hw : |(-3884053797/10000000000 : ℝ)|=(3884053797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-178188599/400000000 : ℝ)|^67 ≤ (17282866850019/50000000000000 : ℝ)^51
        have hw : |(-178188599/400000000 : ℝ)|=(178188599/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4649534223/10000000000 : ℝ)|^67 ≤ (3656514626133/10000000000000 : ℝ)^51
        have hw : |(4649534223/10000000000 : ℝ)|=(4649534223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305073_s0_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (277174781/625000000 : ℝ)*x 0 + (5086375059/10000000000 : ℝ)*x 1 + (3427294543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (277174781/625000000 : ℝ)^67 ≤ (17181416947451/50000000000000 : ℝ)^51 := by
    have hnat : (277174781 : ℕ)^67*50000000000000^51 ≤ 17181416947451^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277174781 625000000 17181416947451 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5086375059/10000000000 : ℝ)^67 ≤ (41143497431697/100000000000000 : ℝ)^51 := by
    have hnat : (5086375059 : ℕ)^67*100000000000000^51 ≤ 41143497431697^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5086375059 10000000000 41143497431697 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3427294543/10000000000 : ℝ)^67 ≤ (2449366866663/10000000000000 : ℝ)^51 := by
    have hnat : (3427294543 : ℕ)^67*10000000000000^51 ≤ 2449366866663^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3427294543 10000000000 2449366866663 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(277174781/625000000 : ℝ), (5086375059/10000000000 : ℝ), (3427294543/10000000000 : ℝ)] ![(17181416947451/50000000000000 : ℝ), (41143497431697/100000000000000 : ℝ), (2449366866663/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(277174781/625000000 : ℝ)|^67 ≤ (17181416947451/50000000000000 : ℝ)^51
        have hw : |(277174781/625000000 : ℝ)|=(277174781/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5086375059/10000000000 : ℝ)|^67 ≤ (41143497431697/100000000000000 : ℝ)^51
        have hw : |(5086375059/10000000000 : ℝ)|=(5086375059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3427294543/10000000000 : ℝ)|^67 ≤ (2449366866663/10000000000000 : ℝ)^51
        have hw : |(3427294543/10000000000 : ℝ)|=(3427294543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305073_s0_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1865242221/10000000000 : ℝ)*x 0 + (-378923587/2500000000 : ℝ)*x 1 + (4243001301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1865242221/10000000000 : ℝ)^67 ≤ (11014030944527/100000000000000 : ℝ)^51 := by
    have hnat : (1865242221 : ℕ)^67*100000000000000^51 ≤ 11014030944527^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865242221 10000000000 11014030944527 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (378923587/2500000000 : ℝ)^67 ≤ (524117463791/6250000000000 : ℝ)^51 := by
    have hnat : (378923587 : ℕ)^67*6250000000000^51 ≤ 524117463791^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378923587 2500000000 524117463791 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4243001301/5000000000 : ℝ)^67 ≤ (80600089620351/100000000000000 : ℝ)^51 := by
    have hnat : (4243001301 : ℕ)^67*100000000000000^51 ≤ 80600089620351^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243001301 5000000000 80600089620351 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1865242221/10000000000 : ℝ), (-378923587/2500000000 : ℝ), (4243001301/5000000000 : ℝ)] ![(11014030944527/100000000000000 : ℝ), (524117463791/6250000000000 : ℝ), (80600089620351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1865242221/10000000000 : ℝ)|^67 ≤ (11014030944527/100000000000000 : ℝ)^51
        have hw : |(1865242221/10000000000 : ℝ)|=(1865242221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-378923587/2500000000 : ℝ)|^67 ≤ (524117463791/6250000000000 : ℝ)^51
        have hw : |(-378923587/2500000000 : ℝ)|=(378923587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4243001301/5000000000 : ℝ)|^67 ≤ (80600089620351/100000000000000 : ℝ)^51
        have hw : |(4243001301/5000000000 : ℝ)|=(4243001301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305073_s0_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3914923227/10000000000 : ℝ)*x 0 + (-295049623/625000000 : ℝ)*x 1 + (4352341039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3914923227/10000000000 : ℝ)^67 ≤ (7292730427949/25000000000000 : ℝ)^51 := by
    have hnat : (3914923227 : ℕ)^67*25000000000000^51 ≤ 7292730427949^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3914923227 10000000000 7292730427949 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (295049623/625000000 : ℝ)^67 ≤ (37303128598749/100000000000000 : ℝ)^51 := by
    have hnat : (295049623 : ℕ)^67*100000000000000^51 ≤ 37303128598749^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295049623 625000000 37303128598749 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4352341039/10000000000 : ℝ)^67 ≤ (2095371854563/6250000000000 : ℝ)^51 := by
    have hnat : (4352341039 : ℕ)^67*6250000000000^51 ≤ 2095371854563^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352341039 10000000000 2095371854563 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3914923227/10000000000 : ℝ), (-295049623/625000000 : ℝ), (4352341039/10000000000 : ℝ)] ![(7292730427949/25000000000000 : ℝ), (37303128598749/100000000000000 : ℝ), (2095371854563/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3914923227/10000000000 : ℝ)|^67 ≤ (7292730427949/25000000000000 : ℝ)^51
        have hw : |(-3914923227/10000000000 : ℝ)|=(3914923227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-295049623/625000000 : ℝ)|^67 ≤ (37303128598749/100000000000000 : ℝ)^51
        have hw : |(-295049623/625000000 : ℝ)|=(295049623/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4352341039/10000000000 : ℝ)|^67 ≤ (2095371854563/6250000000000 : ℝ)^51
        have hw : |(4352341039/10000000000 : ℝ)|=(4352341039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305073_s0_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2131033941/5000000000 : ℝ)*x 0 + (5139396913/10000000000 : ℝ)*x 1 + (111018449/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131033941/5000000000 : ℝ)^67 ≤ (32615409008519/100000000000000 : ℝ)^51 := by
    have hnat : (2131033941 : ℕ)^67*100000000000000^51 ≤ 32615409008519^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131033941 5000000000 32615409008519 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5139396913/10000000000 : ℝ)^67 ≤ (20853931330667/50000000000000 : ℝ)^51 := by
    have hnat : (5139396913 : ℕ)^67*50000000000000^51 ≤ 20853931330667^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139396913 10000000000 20853931330667 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111018449/312500000 : ℝ)^67 ≤ (25676728312649/100000000000000 : ℝ)^51 := by
    have hnat : (111018449 : ℕ)^67*100000000000000^51 ≤ 25676728312649^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111018449 312500000 25676728312649 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2131033941/5000000000 : ℝ), (5139396913/10000000000 : ℝ), (111018449/312500000 : ℝ)] ![(32615409008519/100000000000000 : ℝ), (20853931330667/50000000000000 : ℝ), (25676728312649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2131033941/5000000000 : ℝ)|^67 ≤ (32615409008519/100000000000000 : ℝ)^51
        have hw : |(2131033941/5000000000 : ℝ)|=(2131033941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5139396913/10000000000 : ℝ)|^67 ≤ (20853931330667/50000000000000 : ℝ)^51
        have hw : |(5139396913/10000000000 : ℝ)|=(5139396913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(111018449/312500000 : ℝ)|^67 ≤ (25676728312649/100000000000000 : ℝ)^51
        have hw : |(111018449/312500000 : ℝ)|=(111018449/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305073_s0_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5758340173/10000000000 : ℝ)*x 0 + (-4511915653/10000000000 : ℝ)*x 1 + (-1264029877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5758340173/10000000000 : ℝ)^67 ≤ (12106998376549/25000000000000 : ℝ)^51 := by
    have hnat : (5758340173 : ℕ)^67*25000000000000^51 ≤ 12106998376549^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5758340173 10000000000 12106998376549 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4511915653/10000000000 : ℝ)^67 ≤ (4393748679289/12500000000000 : ℝ)^51 := by
    have hnat : (4511915653 : ℕ)^67*12500000000000^51 ≤ 4393748679289^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511915653 10000000000 4393748679289 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1264029877/5000000000 : ℝ)^67 ≤ (4105504262769/25000000000000 : ℝ)^51 := by
    have hnat : (1264029877 : ℕ)^67*25000000000000^51 ≤ 4105504262769^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1264029877 5000000000 4105504262769 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5758340173/10000000000 : ℝ), (-4511915653/10000000000 : ℝ), (-1264029877/5000000000 : ℝ)] ![(12106998376549/25000000000000 : ℝ), (4393748679289/12500000000000 : ℝ), (4105504262769/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5758340173/10000000000 : ℝ)|^67 ≤ (12106998376549/25000000000000 : ℝ)^51
        have hw : |(5758340173/10000000000 : ℝ)|=(5758340173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4511915653/10000000000 : ℝ)|^67 ≤ (4393748679289/12500000000000 : ℝ)^51
        have hw : |(-4511915653/10000000000 : ℝ)|=(4511915653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1264029877/5000000000 : ℝ)|^67 ≤ (4105504262769/25000000000000 : ℝ)^51
        have hw : |(-1264029877/5000000000 : ℝ)|=(1264029877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305073_s0_12 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1275939629/10000000000 : ℝ)*x 0 + (-999755453/10000000000 : ℝ)*x 1 + (1821732313/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1275939629/10000000000 : ℝ)^67 ≤ (209004802769/3125000000000 : ℝ)^51 := by
    have hnat : (1275939629 : ℕ)^67*3125000000000^51 ≤ 209004802769^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275939629 10000000000 209004802769 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999755453/10000000000 : ℝ)^67 ≤ (2427196696311/50000000000000 : ℝ)^51 := by
    have hnat : (999755453 : ℕ)^67*50000000000000^51 ≤ 2427196696311^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999755453 10000000000 2427196696311 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1821732313/2000000000 : ℝ)^67 ≤ (88457452905517/100000000000000 : ℝ)^51 := by
    have hnat : (1821732313 : ℕ)^67*100000000000000^51 ≤ 88457452905517^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1821732313 2000000000 88457452905517 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1275939629/10000000000 : ℝ), (-999755453/10000000000 : ℝ), (1821732313/2000000000 : ℝ)] ![(209004802769/3125000000000 : ℝ), (2427196696311/50000000000000 : ℝ), (88457452905517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1275939629/10000000000 : ℝ)|^67 ≤ (209004802769/3125000000000 : ℝ)^51
        have hw : |(1275939629/10000000000 : ℝ)|=(1275939629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-999755453/10000000000 : ℝ)|^67 ≤ (2427196696311/50000000000000 : ℝ)^51
        have hw : |(-999755453/10000000000 : ℝ)|=(999755453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1821732313/2000000000 : ℝ)|^67 ≤ (88457452905517/100000000000000 : ℝ)^51
        have hw : |(1821732313/2000000000 : ℝ)|=(1821732313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305073_s0_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-935795817/2500000000 : ℝ)*x 0 + (-4203922761/10000000000 : ℝ)*x 1 + (2511266691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (935795817/2500000000 : ℝ)^67 ≤ (27501472198451/100000000000000 : ℝ)^51 := by
    have hnat : (935795817 : ℕ)^67*100000000000000^51 ≤ 27501472198451^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935795817 2500000000 27501472198451 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4203922761/10000000000 : ℝ)^67 ≤ (32032115605643/100000000000000 : ℝ)^51 := by
    have hnat : (4203922761 : ℕ)^67*100000000000000^51 ≤ 32032115605643^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203922761 10000000000 32032115605643 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2511266691/5000000000 : ℝ)^67 ≤ (20233206088577/50000000000000 : ℝ)^51 := by
    have hnat : (2511266691 : ℕ)^67*50000000000000^51 ≤ 20233206088577^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2511266691 5000000000 20233206088577 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-935795817/2500000000 : ℝ), (-4203922761/10000000000 : ℝ), (2511266691/5000000000 : ℝ)] ![(27501472198451/100000000000000 : ℝ), (32032115605643/100000000000000 : ℝ), (20233206088577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-935795817/2500000000 : ℝ)|^67 ≤ (27501472198451/100000000000000 : ℝ)^51
        have hw : |(-935795817/2500000000 : ℝ)|=(935795817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4203922761/10000000000 : ℝ)|^67 ≤ (32032115605643/100000000000000 : ℝ)^51
        have hw : |(-4203922761/10000000000 : ℝ)|=(4203922761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2511266691/5000000000 : ℝ)|^67 ≤ (20233206088577/50000000000000 : ℝ)^51
        have hw : |(2511266691/5000000000 : ℝ)|=(2511266691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305073_s0_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2292556399/5000000000 : ℝ)*x 0 + (5149483387/10000000000 : ℝ)*x 1 + (159462829/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2292556399/5000000000 : ℝ)^67 ≤ (35901028830653/100000000000000 : ℝ)^51 := by
    have hnat : (2292556399 : ℕ)^67*100000000000000^51 ≤ 35901028830653^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2292556399 5000000000 35901028830653 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5149483387/10000000000 : ℝ)^67 ≤ (10453857683971/25000000000000 : ℝ)^51 := by
    have hnat : (5149483387 : ℕ)^67*25000000000000^51 ≤ 10453857683971^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149483387 10000000000 10453857683971 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (159462829/500000000 : ℝ)^67 ≤ (11141770208433/50000000000000 : ℝ)^51 := by
    have hnat : (159462829 : ℕ)^67*50000000000000^51 ≤ 11141770208433^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159462829 500000000 11141770208433 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2292556399/5000000000 : ℝ), (5149483387/10000000000 : ℝ), (159462829/500000000 : ℝ)] ![(35901028830653/100000000000000 : ℝ), (10453857683971/25000000000000 : ℝ), (11141770208433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2292556399/5000000000 : ℝ)|^67 ≤ (35901028830653/100000000000000 : ℝ)^51
        have hw : |(2292556399/5000000000 : ℝ)|=(2292556399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5149483387/10000000000 : ℝ)|^67 ≤ (10453857683971/25000000000000 : ℝ)^51
        have hw : |(5149483387/10000000000 : ℝ)|=(5149483387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(159462829/500000000 : ℝ)|^67 ≤ (11141770208433/50000000000000 : ℝ)^51
        have hw : |(159462829/500000000 : ℝ)|=(159462829/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305073_s0_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2931356167/5000000000 : ℝ)*x 0 + (-4612938279/10000000000 : ℝ)*x 1 + (-1133312219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2931356167/5000000000 : ℝ)^67 ≤ (24792207862137/50000000000000 : ℝ)^51 := by
    have hnat : (2931356167 : ℕ)^67*50000000000000^51 ≤ 24792207862137^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2931356167 5000000000 24792207862137 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4612938279/10000000000 : ℝ)^67 ≤ (18093761845033/50000000000000 : ℝ)^51 := by
    have hnat : (4612938279 : ℕ)^67*50000000000000^51 ≤ 18093761845033^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4612938279 10000000000 18093761845033 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133312219/5000000000 : ℝ)^67 ≤ (177850757191/1250000000000 : ℝ)^51 := by
    have hnat : (1133312219 : ℕ)^67*1250000000000^51 ≤ 177850757191^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133312219 5000000000 177850757191 1250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2931356167/5000000000 : ℝ), (-4612938279/10000000000 : ℝ), (-1133312219/5000000000 : ℝ)] ![(24792207862137/50000000000000 : ℝ), (18093761845033/50000000000000 : ℝ), (177850757191/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2931356167/5000000000 : ℝ)|^67 ≤ (24792207862137/50000000000000 : ℝ)^51
        have hw : |(2931356167/5000000000 : ℝ)|=(2931356167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4612938279/10000000000 : ℝ)|^67 ≤ (18093761845033/50000000000000 : ℝ)^51
        have hw : |(-4612938279/10000000000 : ℝ)|=(4612938279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1133312219/5000000000 : ℝ)|^67 ≤ (177850757191/1250000000000 : ℝ)^51
        have hw : |(-1133312219/5000000000 : ℝ)|=(1133312219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305073_s0_18 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (343139481/2500000000 : ℝ)*x 0 + (-1079965147/10000000000 : ℝ)*x 1 + (9015151629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343139481/2500000000 : ℝ)^67 ≤ (7361258547801/100000000000000 : ℝ)^51 := by
    have hnat : (343139481 : ℕ)^67*100000000000000^51 ≤ 7361258547801^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343139481 2500000000 7361258547801 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079965147/10000000000 : ℝ)^67 ≤ (335772987071/6250000000000 : ℝ)^51 := by
    have hnat : (1079965147 : ℕ)^67*6250000000000^51 ≤ 335772987071^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079965147 10000000000 335772987071 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9015151629/10000000000 : ℝ)^67 ≤ (87266373641949/100000000000000 : ℝ)^51 := by
    have hnat : (9015151629 : ℕ)^67*100000000000000^51 ≤ 87266373641949^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9015151629 10000000000 87266373641949 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(343139481/2500000000 : ℝ), (-1079965147/10000000000 : ℝ), (9015151629/10000000000 : ℝ)] ![(7361258547801/100000000000000 : ℝ), (335772987071/6250000000000 : ℝ), (87266373641949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(343139481/2500000000 : ℝ)|^67 ≤ (7361258547801/100000000000000 : ℝ)^51
        have hw : |(343139481/2500000000 : ℝ)|=(343139481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1079965147/10000000000 : ℝ)|^67 ≤ (335772987071/6250000000000 : ℝ)^51
        have hw : |(-1079965147/10000000000 : ℝ)|=(1079965147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9015151629/10000000000 : ℝ)|^67 ≤ (87266373641949/100000000000000 : ℝ)^51
        have hw : |(9015151629/10000000000 : ℝ)|=(9015151629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305073_s0_19 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-254381091/625000000 : ℝ)*x 0 + (-4283772327/10000000000 : ℝ)*x 1 + (2320013683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (254381091/625000000 : ℝ)^67 ≤ (30699258469909/100000000000000 : ℝ)^51 := by
    have hnat : (254381091 : ℕ)^67*100000000000000^51 ≤ 30699258469909^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254381091 625000000 30699258469909 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4283772327/10000000000 : ℝ)^67 ≤ (32833783627053/100000000000000 : ℝ)^51 := by
    have hnat : (4283772327 : ℕ)^67*100000000000000^51 ≤ 32833783627053^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283772327 10000000000 32833783627053 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2320013683/5000000000 : ℝ)^67 ≤ (36466957886253/100000000000000 : ℝ)^51 := by
    have hnat : (2320013683 : ℕ)^67*100000000000000^51 ≤ 36466957886253^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2320013683 5000000000 36466957886253 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-254381091/625000000 : ℝ), (-4283772327/10000000000 : ℝ), (2320013683/5000000000 : ℝ)] ![(30699258469909/100000000000000 : ℝ), (32833783627053/100000000000000 : ℝ), (36466957886253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-254381091/625000000 : ℝ)|^67 ≤ (30699258469909/100000000000000 : ℝ)^51
        have hw : |(-254381091/625000000 : ℝ)|=(254381091/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4283772327/10000000000 : ℝ)|^67 ≤ (32833783627053/100000000000000 : ℝ)^51
        have hw : |(-4283772327/10000000000 : ℝ)|=(4283772327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2320013683/5000000000 : ℝ)|^67 ≤ (36466957886253/100000000000000 : ℝ)^51
        have hw : |(2320013683/5000000000 : ℝ)|=(2320013683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305073_s0_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2129099457/5000000000 : ℝ)*x 0 + (2613897643/5000000000 : ℝ)*x 1 + (432094459/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129099457/5000000000 : ℝ)^67 ≤ (8144129697747/25000000000000 : ℝ)^51 := by
    have hnat : (2129099457 : ℕ)^67*25000000000000^51 ≤ 8144129697747^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129099457 5000000000 8144129697747 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613897643/5000000000 : ℝ)^67 ≤ (42652837585699/100000000000000 : ℝ)^51 := by
    have hnat : (2613897643 : ℕ)^67*100000000000000^51 ≤ 42652837585699^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613897643 5000000000 42652837585699 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (432094459/1250000000 : ℝ)^67 ≤ (24770643610249/100000000000000 : ℝ)^51 := by
    have hnat : (432094459 : ℕ)^67*100000000000000^51 ≤ 24770643610249^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432094459 1250000000 24770643610249 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2129099457/5000000000 : ℝ), (2613897643/5000000000 : ℝ), (432094459/1250000000 : ℝ)] ![(8144129697747/25000000000000 : ℝ), (42652837585699/100000000000000 : ℝ), (24770643610249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2129099457/5000000000 : ℝ)|^67 ≤ (8144129697747/25000000000000 : ℝ)^51
        have hw : |(2129099457/5000000000 : ℝ)|=(2129099457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613897643/5000000000 : ℝ)|^67 ≤ (42652837585699/100000000000000 : ℝ)^51
        have hw : |(2613897643/5000000000 : ℝ)|=(2613897643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(432094459/1250000000 : ℝ)|^67 ≤ (24770643610249/100000000000000 : ℝ)^51
        have hw : |(432094459/1250000000 : ℝ)|=(432094459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305073_s0_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (56830371/100000000 : ℝ)*x 0 + (-4532688197/10000000000 : ℝ)*x 1 + (-260010171/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56830371/100000000 : ℝ)^67 ≤ (47597718425761/100000000000000 : ℝ)^51 := by
    have hnat : (56830371 : ℕ)^67*100000000000000^51 ≤ 47597718425761^51*100000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56830371 100000000 47597718425761 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4532688197/10000000000 : ℝ)^67 ≤ (35362740497513/100000000000000 : ℝ)^51 := by
    have hnat : (4532688197 : ℕ)^67*100000000000000^51 ≤ 35362740497513^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532688197 10000000000 35362740497513 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260010171/1000000000 : ℝ)^67 ≤ (1064971316749/6250000000000 : ℝ)^51 := by
    have hnat : (260010171 : ℕ)^67*6250000000000^51 ≤ 1064971316749^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260010171 1000000000 1064971316749 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(56830371/100000000 : ℝ), (-4532688197/10000000000 : ℝ), (-260010171/1000000000 : ℝ)] ![(47597718425761/100000000000000 : ℝ), (35362740497513/100000000000000 : ℝ), (1064971316749/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(56830371/100000000 : ℝ)|^67 ≤ (47597718425761/100000000000000 : ℝ)^51
        have hw : |(56830371/100000000 : ℝ)|=(56830371/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4532688197/10000000000 : ℝ)|^67 ≤ (35362740497513/100000000000000 : ℝ)^51
        have hw : |(-4532688197/10000000000 : ℝ)|=(4532688197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-260010171/1000000000 : ℝ)|^67 ≤ (1064971316749/6250000000000 : ℝ)^51
        have hw : |(-260010171/1000000000 : ℝ)|=(260010171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305073_s0_25 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1742429229/10000000000 : ℝ)*x 0 + (-209332073/1250000000 : ℝ)*x 1 + (8467462197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1742429229/10000000000 : ℝ)^67 ≤ (1258914360053/12500000000000 : ℝ)^51 := by
    have hnat : (1742429229 : ℕ)^67*12500000000000^51 ≤ 1258914360053^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742429229 10000000000 1258914360053 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209332073/1250000000 : ℝ)^67 ≤ (9559859075347/100000000000000 : ℝ)^51 := by
    have hnat : (209332073 : ℕ)^67*100000000000000^51 ≤ 9559859075347^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209332073 1250000000 9559859075347 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8467462197/10000000000 : ℝ)^67 ≤ (20092206507033/25000000000000 : ℝ)^51 := by
    have hnat : (8467462197 : ℕ)^67*25000000000000^51 ≤ 20092206507033^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8467462197 10000000000 20092206507033 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1742429229/10000000000 : ℝ), (-209332073/1250000000 : ℝ), (8467462197/10000000000 : ℝ)] ![(1258914360053/12500000000000 : ℝ), (9559859075347/100000000000000 : ℝ), (20092206507033/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1742429229/10000000000 : ℝ)|^67 ≤ (1258914360053/12500000000000 : ℝ)^51
        have hw : |(1742429229/10000000000 : ℝ)|=(1742429229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-209332073/1250000000 : ℝ)|^67 ≤ (9559859075347/100000000000000 : ℝ)^51
        have hw : |(-209332073/1250000000 : ℝ)|=(209332073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8467462197/10000000000 : ℝ)|^67 ≤ (20092206507033/25000000000000 : ℝ)^51
        have hw : |(8467462197/10000000000 : ℝ)|=(8467462197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305073_s1_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-196768179/500000000 : ℝ)*x 0 + (-4057543923/10000000000 : ℝ)*x 1 + (311469571/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196768179/500000000 : ℝ)^67 ≤ (29371172871151/100000000000000 : ℝ)^51 := by
    have hnat : (196768179 : ℕ)^67*100000000000000^51 ≤ 29371172871151^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196768179 500000000 29371172871151 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4057543923/10000000000 : ℝ)^67 ≤ (30574926345611/100000000000000 : ℝ)^51 := by
    have hnat : (4057543923 : ℕ)^67*100000000000000^51 ≤ 30574926345611^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4057543923 10000000000 30574926345611 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (311469571/625000000 : ℝ)^67 ≤ (20026950382349/50000000000000 : ℝ)^51 := by
    have hnat : (311469571 : ℕ)^67*50000000000000^51 ≤ 20026950382349^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311469571 625000000 20026950382349 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-196768179/500000000 : ℝ), (-4057543923/10000000000 : ℝ), (311469571/625000000 : ℝ)] ![(29371172871151/100000000000000 : ℝ), (30574926345611/100000000000000 : ℝ), (20026950382349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-196768179/500000000 : ℝ)|^67 ≤ (29371172871151/100000000000000 : ℝ)^51
        have hw : |(-196768179/500000000 : ℝ)|=(196768179/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4057543923/10000000000 : ℝ)|^67 ≤ (30574926345611/100000000000000 : ℝ)^51
        have hw : |(-4057543923/10000000000 : ℝ)|=(4057543923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(311469571/625000000 : ℝ)|^67 ≤ (20026950382349/50000000000000 : ℝ)^51
        have hw : |(311469571/625000000 : ℝ)|=(311469571/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305073_s1_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2257749963/5000000000 : ℝ)*x 0 + (4655691631/10000000000 : ℝ)*x 1 + (190687277/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2257749963/5000000000 : ℝ)^67 ≤ (35186677434453/100000000000000 : ℝ)^51 := by
    have hnat : (2257749963 : ℕ)^67*100000000000000^51 ≤ 35186677434453^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257749963 5000000000 35186677434453 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4655691631/10000000000 : ℝ)^67 ≤ (4578596825397/12500000000000 : ℝ)^51 := by
    have hnat : (4655691631 : ℕ)^67*12500000000000^51 ≤ 4578596825397^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4655691631 10000000000 4578596825397 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190687277/500000000 : ℝ)^67 ≤ (2818454795241/10000000000000 : ℝ)^51 := by
    have hnat : (190687277 : ℕ)^67*10000000000000^51 ≤ 2818454795241^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190687277 500000000 2818454795241 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2257749963/5000000000 : ℝ), (4655691631/10000000000 : ℝ), (190687277/500000000 : ℝ)] ![(35186677434453/100000000000000 : ℝ), (4578596825397/12500000000000 : ℝ), (2818454795241/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2257749963/5000000000 : ℝ)|^67 ≤ (35186677434453/100000000000000 : ℝ)^51
        have hw : |(2257749963/5000000000 : ℝ)|=(2257749963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4655691631/10000000000 : ℝ)|^67 ≤ (4578596825397/12500000000000 : ℝ)^51
        have hw : |(4655691631/10000000000 : ℝ)|=(4655691631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(190687277/500000000 : ℝ)|^67 ≤ (2818454795241/10000000000000 : ℝ)^51
        have hw : |(190687277/500000000 : ℝ)|=(190687277/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305073_s1_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2364883513/5000000000 : ℝ)*x 0 + (-2271742537/5000000000 : ℝ)*x 1 + (-926165193/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2364883513/5000000000 : ℝ)^67 ≤ (37396304740841/100000000000000 : ℝ)^51 := by
    have hnat : (2364883513 : ℕ)^67*100000000000000^51 ≤ 37396304740841^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2364883513 5000000000 37396304740841 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2271742537/5000000000 : ℝ)^67 ≤ (17736721189719/50000000000000 : ℝ)^51 := by
    have hnat : (2271742537 : ℕ)^67*50000000000000^51 ≤ 17736721189719^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271742537 5000000000 17736721189719 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (926165193/2500000000 : ℝ)^67 ≤ (6782563218833/25000000000000 : ℝ)^51 := by
    have hnat : (926165193 : ℕ)^67*25000000000000^51 ≤ 6782563218833^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926165193 2500000000 6782563218833 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2364883513/5000000000 : ℝ), (-2271742537/5000000000 : ℝ), (-926165193/2500000000 : ℝ)] ![(37396304740841/100000000000000 : ℝ), (17736721189719/50000000000000 : ℝ), (6782563218833/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2364883513/5000000000 : ℝ)|^67 ≤ (37396304740841/100000000000000 : ℝ)^51
        have hw : |(2364883513/5000000000 : ℝ)|=(2364883513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2271742537/5000000000 : ℝ)|^67 ≤ (17736721189719/50000000000000 : ℝ)^51
        have hw : |(-2271742537/5000000000 : ℝ)|=(2271742537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-926165193/2500000000 : ℝ)|^67 ≤ (6782563218833/25000000000000 : ℝ)^51
        have hw : |(-926165193/2500000000 : ℝ)|=(926165193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305073_s1_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3909996661/10000000000 : ℝ)*x 0 + (-3756001379/10000000000 : ℝ)*x 1 + (1320901279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3909996661/10000000000 : ℝ)^67 ≤ (29122705834619/100000000000000 : ℝ)^51 := by
    have hnat : (3909996661 : ℕ)^67*100000000000000^51 ≤ 29122705834619^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3909996661 10000000000 29122705834619 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3756001379/10000000000 : ℝ)^67 ≤ (345315745357/1250000000000 : ℝ)^51 := by
    have hnat : (3756001379 : ℕ)^67*1250000000000^51 ≤ 345315745357^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3756001379 10000000000 345315745357 1250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320901279/2500000000 : ℝ)^67 ≤ (43252034516167/100000000000000 : ℝ)^51 := by
    have hnat : (1320901279 : ℕ)^67*100000000000000^51 ≤ 43252034516167^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320901279 2500000000 43252034516167 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3909996661/10000000000 : ℝ), (-3756001379/10000000000 : ℝ), (1320901279/2500000000 : ℝ)] ![(29122705834619/100000000000000 : ℝ), (345315745357/1250000000000 : ℝ), (43252034516167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3909996661/10000000000 : ℝ)|^67 ≤ (29122705834619/100000000000000 : ℝ)^51
        have hw : |(3909996661/10000000000 : ℝ)|=(3909996661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3756001379/10000000000 : ℝ)|^67 ≤ (345315745357/1250000000000 : ℝ)^51
        have hw : |(-3756001379/10000000000 : ℝ)|=(3756001379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320901279/2500000000 : ℝ)|^67 ≤ (43252034516167/100000000000000 : ℝ)^51
        have hw : |(1320901279/2500000000 : ℝ)|=(1320901279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305073 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base31 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(907425780553129/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(907425780553129/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-3884053797/10000000000 : ℝ)*X 0 0+(-178188599/400000000 : ℝ)*X 0 1+(4649534223/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((277174781/625000000 : ℝ)*X 1 0+(5086375059/10000000000 : ℝ)*X 1 1+(3427294543/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1865242221/10000000000 : ℝ)*X 0 0+(-378923587/2500000000 : ℝ)*X 0 1+(4243001301/5000000000 : ℝ)*X 0 2+(1865242221/10000000000 : ℝ)*X 1 0+(-378923587/2500000000 : ℝ)*X 1 1+(4243001301/5000000000 : ℝ)*X 1 2+(1865242221/10000000000 : ℝ)*X 2 0+(-378923587/2500000000 : ℝ)*X 2 1+(4243001301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-3914923227/10000000000 : ℝ)*X 0 0+(-295049623/625000000 : ℝ)*X 0 1+(4352341039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2131033941/5000000000 : ℝ)*X 1 0+(5139396913/10000000000 : ℝ)*X 1 1+(111018449/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((5758340173/10000000000 : ℝ)*X 2 0+(-4511915653/10000000000 : ℝ)*X 2 1+(-1264029877/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((1275939629/10000000000 : ℝ)*X 0 0+(-999755453/10000000000 : ℝ)*X 0 1+(1821732313/2000000000 : ℝ)*X 0 2+(1275939629/10000000000 : ℝ)*X 1 0+(-999755453/10000000000 : ℝ)*X 1 1+(1821732313/2000000000 : ℝ)*X 1 2+(1275939629/10000000000 : ℝ)*X 2 0+(-999755453/10000000000 : ℝ)*X 2 1+(1821732313/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-935795817/2500000000 : ℝ)*X 0 0+(-4203922761/10000000000 : ℝ)*X 0 1+(2511266691/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((2292556399/5000000000 : ℝ)*X 1 0+(5149483387/10000000000 : ℝ)*X 1 1+(159462829/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2931356167/5000000000 : ℝ)*X 2 0+(-4612938279/10000000000 : ℝ)*X 2 1+(-1133312219/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_18 : ((343139481/2500000000 : ℝ)*X 0 0+(-1079965147/10000000000 : ℝ)*X 0 1+(9015151629/10000000000 : ℝ)*X 0 2+(343139481/2500000000 : ℝ)*X 1 0+(-1079965147/10000000000 : ℝ)*X 1 1+(9015151629/10000000000 : ℝ)*X 1 2+(343139481/2500000000 : ℝ)*X 2 0+(-1079965147/10000000000 : ℝ)*X 2 1+(9015151629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s0_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((-254381091/625000000 : ℝ)*X 0 0+(-4283772327/10000000000 : ℝ)*X 0 1+(2320013683/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s0_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2129099457/5000000000 : ℝ)*X 1 0+(2613897643/5000000000 : ℝ)*X 1 1+(432094459/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s0_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((56830371/100000000 : ℝ)*X 2 0+(-4532688197/10000000000 : ℝ)*X 2 1+(-260010171/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s0_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((1742429229/10000000000 : ℝ)*X 0 0+(-209332073/1250000000 : ℝ)*X 0 1+(8467462197/10000000000 : ℝ)*X 0 2+(1742429229/10000000000 : ℝ)*X 1 0+(-209332073/1250000000 : ℝ)*X 1 1+(8467462197/10000000000 : ℝ)*X 1 2+(1742429229/10000000000 : ℝ)*X 2 0+(-209332073/1250000000 : ℝ)*X 2 1+(8467462197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((20667/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20667/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (122125651205853051/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (119837238919/250000000000 : ℝ)*(base40) + (1618890407787/500000000000 : ℝ)*(base59) + (57227640093/40000000000 : ℝ)*(base60) + (2536746621523/250000000000 : ℝ)*(major_s0_0) + (2536746621523/250000000000 : ℝ)*(major_s0_1) + (2536746621523/250000000000 : ℝ)*(major_s0_2) + (41824063/125000000000 : ℝ)*(sp_s0_0) + (3414623644737/250000000000 : ℝ)*(sp_s0_7) + (13658208469681/1000000000000 : ℝ)*(sp_s0_8) + (682879818723/50000000000 : ℝ)*(sp_s0_9) + (663422756651/100000000000 : ℝ)*(sp_s0_12) + (912163357/1000000000000 : ℝ)*(sp_s0_18) + (620701771/1000000000000 : ℝ)*(sp_s0_20) + (19262453/15625000000 : ℝ)*(sp_s0_21) + (6635139729867/1000000000000 : ℝ)*(f.failure) + (3414707292863/250000000000 : ℝ)*(f.sum) + (898007177409197/2500000000000000000000000000 : ℝ)*base63 + (1178942359549869/2500000000000000000000000000 : ℝ)*base65 + (1095690198020467/1250000000000000000000000000 : ℝ)*base67 + (1113067794354533/1250000000000000000000000000 : ℝ)*base69 + (3736092441590803/2500000000000000000000000000 : ℝ)*base71 + (956666110549869/2500000000000000000000000000 : ℝ)*base73 + (1142140174200131/2500000000000000000000000000 : ℝ)*base75 + (56450370520467/1250000000000000000000000000 : ℝ)*base77 + (29247256659197/2500000000000000000000000000 : ℝ)*base78 + (3107/3125000000000000 : ℝ)*base86 + (3107/3125000000000000 : ℝ)*base88 + (3107/3125000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-7339/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-7339/25000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7421460754738358156463/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1215992904647/1000000000000 : ℝ)*(base40) + (1957825733467/500000000000 : ℝ)*(base59) + (165823107941/125000000000 : ℝ)*(base60) + (1189099341241/100000000000 : ℝ)*(major_s0_0) + (1189099341241/100000000000 : ℝ)*(major_s0_1) + (1189099341241/100000000000 : ℝ)*(major_s0_2) + (158688377/250000000000 : ℝ)*(sp_s0_1) + (213476633/1000000000000 : ℝ)*(sp_s0_6) + (199214441/250000000000 : ℝ)*(sp_s0_9) + (16005996541947/1000000000000 : ℝ)*(sp_s0_13) + (8002898460997/500000000000 : ℝ)*(sp_s0_14) + (16005634817739/1000000000000 : ℝ)*(sp_s0_15) + (1943834181259/250000000000 : ℝ)*(sp_s0_18) + (87026711/200000000000 : ℝ)*(sp_s0_19) + (777555020167/100000000000 : ℝ)*(f.failure) + (8003215837751/500000000000 : ℝ)*(f.sum) + (581011222995001/1000000000000000000000000000 : ℝ)*base62 + (523838734891177/1000000000000000000000000000 : ℝ)*base64 + (657906321593089/500000000000000000000000000 : ℝ)*base67 + (62142781856911/500000000000000000000000000 : ℝ)*base69 + (599550387495001/1000000000000000000000000000 : ℝ)*base71 + (879402384908823/1000000000000000000000000000 : ℝ)*base73 + (72661292191177/1000000000000000000000000000 : ℝ)*base75 + (130822583743089/500000000000000000000000000 : ℝ)*base77 + (626633697695001/1000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (1/9765625000000 : ℝ)*base86 + (1/9765625000000 : ℝ)*base88 + (1/9765625000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1219/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(1219/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (36251776402523013/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (796587/250000000000 : ℝ)*(base1) + (188124637693/250000000000 : ℝ)*(base40) + (733685699109/500000000000 : ℝ)*(base59) + (1522278668507/200000000000 : ℝ)*(major_s0_0) + (1522278668507/200000000000 : ℝ)*(major_s0_1) + (1522278668507/200000000000 : ℝ)*(major_s0_2) + (24539909/1000000000000 : ℝ)*(sp_s0_7) + (23909881/200000000000 : ℝ)*(sp_s0_9) + (1065639/250000000000 : ℝ)*(sp_s0_14) + (20249009/1000000000000 : ℝ)*(sp_s0_15) + (5122827531799/500000000000 : ℝ)*(sp_s0_19) + (5122836077301/500000000000 : ℝ)*(sp_s0_20) + (1280692077343/125000000000 : ℝ)*(sp_s0_21) + (4977105873167/1000000000000 : ℝ)*(sp_s0_25) + (995421811903/200000000000 : ℝ)*(f.failure) + (5122838208579/500000000000 : ℝ)*(f.sum) + (644116690179973/2000000000000000000000000000 : ℝ)*base63 + (2036782679403221/2000000000000000000000000000 : ℝ)*base65 + (904973529191597/1000000000000000000000000000 : ℝ)*base66 + (351577308508403/1000000000000000000000000000 : ℝ)*base68 + (83818095779973/2000000000000000000000000000 : ℝ)*base70 + (573135702396779/2000000000000000000000000000 : ℝ)*base72 + (763767025003221/2000000000000000000000000000 : ℝ)*base74 + (28137899808403/1000000000000000000000000000 : ℝ)*base77 + (37100798020027/2000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (31/312500000000000 : ℝ)*base87 + (31/312500000000000 : ℝ)*base89 + (31/312500000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (20667/100000 : ℝ) ^ (133/32 : ℝ) ≤ (71300382902959843/50000000000000000000 : ℝ) := by
    have hpowers : (20667/100000 : ℝ)^133 ≤ (71300382902959843/50000000000000000000 : ℝ)^32 := by
      have hnat : (20667 : ℕ)^133*50000000000000000000^32 ≤ 71300382902959843^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20667 100000 71300382902959843 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20667/100000 : ℝ)) (X := (71300382902959843/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (50071300382902959843/50000000000000000000 : ℝ) ≤ (2500857284923639/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (50071300382902959843/50000000000000000000 : ℝ)^32 ≤ (2500857284923639/2500000000000000 : ℝ)^133 := by
      have hnat : (50071300382902959843 : ℕ)^32*2500000000000000^133 ≤ 2500857284923639^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50071300382902959843 50000000000000000000 2500857284923639 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500857284923639/2500000000000000 : ℝ)) (X := (50071300382902959843/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (25071300382902959843/25000000000000000000 : ℝ) ≤ (10006854573236403/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (25071300382902959843/25000000000000000000 : ℝ)^32 ≤ (10006854573236403/10000000000000000 : ℝ)^133 := by
      have hnat : (25071300382902959843 : ℕ)^32*10000000000000000^133 ≤ 10006854573236403^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25071300382902959843 25000000000000000000 10006854573236403 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006854573236403/10000000000000000 : ℝ)) (X := (25071300382902959843/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(285761641213/172225000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3425433541847/2066700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (20667/100000 : ℝ)) (alpha := (285761641213/172225000000000 : ℝ)) (beta := (3425433541847/2066700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (20667/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(285761641213/172225000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3425433541847/2066700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (7339/25000 : ℝ) ^ (133/32 : ℝ) ≤ (38326147864737167/6250000000000000000 : ℝ) := by
    have hpowers : (7339/25000 : ℝ)^133 ≤ (38326147864737167/6250000000000000000 : ℝ)^32 := by
      have hnat : (7339 : ℕ)^133*6250000000000000000^32 ≤ 38326147864737167^32*25000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7339 25000 38326147864737167 6250000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7339/25000 : ℝ)) (X := (38326147864737167/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (6288326147864737167/6250000000000000000 : ℝ) ≤ (5007359947913407/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (6288326147864737167/6250000000000000000 : ℝ)^32 ≤ (5007359947913407/5000000000000000 : ℝ)^133 := by
      have hnat : (6288326147864737167 : ℕ)^32*5000000000000000^133 ≤ 5007359947913407^133*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6288326147864737167 6250000000000000000 5007359947913407 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007359947913407/5000000000000000 : ℝ)) (X := (6288326147864737167/6250000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (3163326147864737167/3125000000000000000 : ℝ) ≤ (10029371819093357/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3163326147864737167/3125000000000000000 : ℝ)^32 ≤ (10029371819093357/10000000000000000 : ℝ)^133 := by
      have hnat : (3163326147864737167 : ℕ)^32*10000000000000000^133 ≤ 10029371819093357^133*3125000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3163326147864737167 3125000000000000000 10029371819093357 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10029371819093357/10000000000000000 : ℝ)) (X := (3163326147864737167/3125000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(7359947913407/1467800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(14651923266543/2935600000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (7339/25000 : ℝ)) (alpha := (7359947913407/1467800000000000 : ℝ)) (beta := (14651923266543/2935600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (7339/25000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(7359947913407/1467800000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(14651923266543/2935600000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (1219/50000 : ℝ) ^ (133/32 : ℝ) ≤ (197746507049/1000000000000000000 : ℝ) := by
    have hpowers : (1219/50000 : ℝ)^133 ≤ (197746507049/1000000000000000000 : ℝ)^32 := by
      have hnat : (1219 : ℕ)^133*1000000000000000000^32 ≤ 197746507049^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1219 50000 197746507049 1000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1219/50000 : ℝ)) (X := (197746507049/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (1000000197746507049/1000000000000000000 : ℝ) ≤ (5000000237890517/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (1000000197746507049/1000000000000000000 : ℝ)^32 ≤ (5000000237890517/5000000000000000 : ℝ)^133 := by
      have hnat : (1000000197746507049 : ℕ)^32*5000000000000000^133 ≤ 5000000237890517^133*1000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000000197746507049 1000000000000000000 5000000237890517 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000237890517/5000000000000000 : ℝ)) (X := (1000000197746507049/1000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (500000197746507049/500000000000000000 : ℝ) ≤ (10000000951561997/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (500000197746507049/500000000000000000 : ℝ)^32 ≤ (10000000951561997/10000000000000000 : ℝ)^133 := by
      have hnat : (500000197746507049 : ℕ)^32*10000000000000000^133 ≤ 10000000951561997^133*500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500000197746507049 500000000000000000 10000000951561997 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000951561997/10000000000000000 : ℝ)) (X := (500000197746507049/500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(237890517/121900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(475780963/243800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1219/50000 : ℝ)) (alpha := (237890517/121900000000000 : ℝ)) (beta := (475780963/243800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1219/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(237890517/121900000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(475780963/243800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-196768179/500000000 : ℝ)*X 0 0+(-4057543923/10000000000 : ℝ)*X 0 1+(311469571/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2257749963/5000000000 : ℝ)*X 1 0+(4655691631/10000000000 : ℝ)*X 1 1+(190687277/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2364883513/5000000000 : ℝ)*X 2 0+(-2271742537/5000000000 : ℝ)*X 2 1+(-926165193/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3909996661/10000000000 : ℝ)*X 0 0+(-3756001379/10000000000 : ℝ)*X 0 1+(1320901279/2500000000 : ℝ)*X 0 2+(3909996661/10000000000 : ℝ)*X 1 0+(-3756001379/10000000000 : ℝ)*X 1 1+(1320901279/2500000000 : ℝ)*X 1 2+(3909996661/10000000000 : ℝ)*X 2 0+(-3756001379/10000000000 : ℝ)*X 2 1+(1320901279/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305073_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-19299/3125 : ℝ) < ((-4779/3125 : ℝ)*P 0+(-4779/3125 : ℝ)*P 1+(-4779/3125 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-19299/3125 : ℝ) < (-509869711628446812062900967111/83976910000000000000000000000 : ℝ) := by norm_num
    linear_combination (181/1000000000000 : ℝ)*(base17) + (4451/500000000000 : ℝ)*(base19) + (9187/1000000000000 : ℝ)*(base31) + (57902431893/250000000000 : ℝ)*(base40) + (21369/1000000000000 : ℝ)*(base43) + (173414188883/1000000000000 : ℝ)*(base49) + (556899754453/1000000000000 : ℝ)*(base59) + (56102108923/250000000000 : ℝ)*(base60) + (4779/3125 : ℝ)*(major_s1_0) + (1529279978631/1000000000000 : ℝ)*(major_s1_1) + (4779/3125 : ℝ)*(major_s1_2) + (2023848802581/1000000000000 : ℝ)*(sp_s1_0) + (1011924407433/500000000000 : ℝ)*(sp_s1_1) + (2023848802581/1000000000000 : ℝ)*(sp_s1_2) + (999999990813/1000000000000 : ℝ)*(sp_s1_6) + (2023848823949/1000000000000 : ℝ)*(f.sum) + (465765011798329053/3578496400000000000000000000000 : ℝ)*base63 + (769174099941/1219000000000000000000000 : ℝ)*base65 + (421501609490903/1467800000000000000000000000 : ℝ)*base66 + (5782617498329/12190000000000000000000000 : ℝ)*base69 + (8905802477068429/83976910000000000000000000000 : ℝ)*base70 + (11348034006307/17222500000000000000000000 : ℝ)*base73 + (1757966995369073/2935600000000000000000000000 : ℝ)*base74 + (406278556569/68890000000000000000000000 : ℝ)*base77 + (4062539690896435393/10111674200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c305074_s0_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2584718913/10000000000 : ℝ)*x 0 + (-6114093669/10000000000 : ℝ)*x 1 + (-4069835787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584718913/10000000000 : ℝ)^67 ≤ (8453613851151/50000000000000 : ℝ)^51 := by
    have hnat : (2584718913 : ℕ)^67*50000000000000^51 ≤ 8453613851151^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584718913 10000000000 8453613851151 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6114093669/10000000000 : ℝ)^67 ≤ (26198053324613/50000000000000 : ℝ)^51 := by
    have hnat : (6114093669 : ℕ)^67*50000000000000^51 ≤ 26198053324613^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6114093669 10000000000 26198053324613 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4069835787/10000000000 : ℝ)^67 ≤ (15348332815311/50000000000000 : ℝ)^51 := by
    have hnat : (4069835787 : ℕ)^67*50000000000000^51 ≤ 15348332815311^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4069835787 10000000000 15348332815311 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2584718913/10000000000 : ℝ), (-6114093669/10000000000 : ℝ), (-4069835787/10000000000 : ℝ)] ![(8453613851151/50000000000000 : ℝ), (26198053324613/50000000000000 : ℝ), (15348332815311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2584718913/10000000000 : ℝ)|^67 ≤ (8453613851151/50000000000000 : ℝ)^51
        have hw : |(-2584718913/10000000000 : ℝ)|=(2584718913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6114093669/10000000000 : ℝ)|^67 ≤ (26198053324613/50000000000000 : ℝ)^51
        have hw : |(-6114093669/10000000000 : ℝ)|=(6114093669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4069835787/10000000000 : ℝ)|^67 ≤ (15348332815311/50000000000000 : ℝ)^51
        have hw : |(-4069835787/10000000000 : ℝ)|=(4069835787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305074_s0_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6280183297/10000000000 : ℝ)*x 0 + (673879617/2500000000 : ℝ)*x 1 + (-756062103/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6280183297/10000000000 : ℝ)^67 ≤ (13568476757819/25000000000000 : ℝ)^51 := by
    have hnat : (6280183297 : ℕ)^67*25000000000000^51 ≤ 13568476757819^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6280183297 10000000000 13568476757819 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673879617/2500000000 : ℝ)^67 ≤ (1116606905019/6250000000000 : ℝ)^51 := by
    have hnat : (673879617 : ℕ)^67*6250000000000^51 ≤ 1116606905019^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673879617 2500000000 1116606905019 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (756062103/2000000000 : ℝ)^67 ≤ (435318475989/1562500000000 : ℝ)^51 := by
    have hnat : (756062103 : ℕ)^67*1562500000000^51 ≤ 435318475989^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      756062103 2000000000 435318475989 1562500000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6280183297/10000000000 : ℝ), (673879617/2500000000 : ℝ), (-756062103/2000000000 : ℝ)] ![(13568476757819/25000000000000 : ℝ), (1116606905019/6250000000000 : ℝ), (435318475989/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6280183297/10000000000 : ℝ)|^67 ≤ (13568476757819/25000000000000 : ℝ)^51
        have hw : |(6280183297/10000000000 : ℝ)|=(6280183297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673879617/2500000000 : ℝ)|^67 ≤ (1116606905019/6250000000000 : ℝ)^51
        have hw : |(673879617/2500000000 : ℝ)|=(673879617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-756062103/2000000000 : ℝ)|^67 ≤ (435318475989/1562500000000 : ℝ)^51
        have hw : |(-756062103/2000000000 : ℝ)|=(756062103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305074_s0_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3518445703/10000000000 : ℝ)*x 0 + (-3858125441/10000000000 : ℝ)*x 1 + (1385014843/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3518445703/10000000000 : ℝ)^67 ≤ (5070602288419/20000000000000 : ℝ)^51 := by
    have hnat : (3518445703 : ℕ)^67*20000000000000^51 ≤ 5070602288419^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3518445703 10000000000 5070602288419 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3858125441/10000000000 : ℝ)^67 ≤ (1144648256307/4000000000000 : ℝ)^51 := by
    have hnat : (3858125441 : ℕ)^67*4000000000000^51 ≤ 1144648256307^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3858125441 10000000000 1144648256307 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1385014843/2500000000 : ℝ)^67 ≤ (46030782146011/100000000000000 : ℝ)^51 := by
    have hnat : (1385014843 : ℕ)^67*100000000000000^51 ≤ 46030782146011^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385014843 2500000000 46030782146011 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3518445703/10000000000 : ℝ), (-3858125441/10000000000 : ℝ), (1385014843/2500000000 : ℝ)] ![(5070602288419/20000000000000 : ℝ), (1144648256307/4000000000000 : ℝ), (46030782146011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3518445703/10000000000 : ℝ)|^67 ≤ (5070602288419/20000000000000 : ℝ)^51
        have hw : |(3518445703/10000000000 : ℝ)|=(3518445703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3858125441/10000000000 : ℝ)|^67 ≤ (1144648256307/4000000000000 : ℝ)^51
        have hw : |(-3858125441/10000000000 : ℝ)|=(3858125441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1385014843/2500000000 : ℝ)|^67 ≤ (46030782146011/100000000000000 : ℝ)^51
        have hw : |(1385014843/2500000000 : ℝ)|=(1385014843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305074_s0_3 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9999999999/10000000000 : ℝ)*x 0 + (117/10000000000 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9999999999/10000000000 : ℝ)^67 ≤ (99999999986863/100000000000000 : ℝ)^51 := by
    have hnat : (9999999999 : ℕ)^67*100000000000000^51 ≤ 99999999986863^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999999 10000000000 99999999986863 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117/10000000000 : ℝ)^67 ≤ (19/500000000000 : ℝ)^51 := by
    have hnat : (117 : ℕ)^67*500000000000^51 ≤ 19^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117 10000000000 19 500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^67 ≤ (0 : ℝ)^51 := by
    have hnat : (0 : ℕ)^67*1^51 ≤ 0^51*1^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9999999999/10000000000 : ℝ), (117/10000000000 : ℝ), (0 : ℝ)] ![(99999999986863/100000000000000 : ℝ), (19/500000000000 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9999999999/10000000000 : ℝ)|^67 ≤ (99999999986863/100000000000000 : ℝ)^51
        have hw : |(9999999999/10000000000 : ℝ)|=(9999999999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(117/10000000000 : ℝ)|^67 ≤ (19/500000000000 : ℝ)^51
        have hw : |(117/10000000000 : ℝ)|=(117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^67 ≤ (0 : ℝ)^51
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305074_s0_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5187775851/10000000000 : ℝ)*x 0 + (-4604498929/10000000000 : ℝ)*x 1 + (-195171489/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5187775851/10000000000 : ℝ)^67 ≤ (21112202644307/50000000000000 : ℝ)^51 := by
    have hnat : (5187775851 : ℕ)^67*50000000000000^51 ≤ 21112202644307^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187775851 10000000000 21112202644307 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4604498929/10000000000 : ℝ)^67 ≤ (18050286789321/50000000000000 : ℝ)^51 := by
    have hnat : (4604498929 : ℕ)^67*50000000000000^51 ≤ 18050286789321^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4604498929 10000000000 18050286789321 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (195171489/625000000 : ℝ)^67 ≤ (21675021117707/100000000000000 : ℝ)^51 := by
    have hnat : (195171489 : ℕ)^67*100000000000000^51 ≤ 21675021117707^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195171489 625000000 21675021117707 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5187775851/10000000000 : ℝ), (-4604498929/10000000000 : ℝ), (-195171489/625000000 : ℝ)] ![(21112202644307/50000000000000 : ℝ), (18050286789321/50000000000000 : ℝ), (21675021117707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5187775851/10000000000 : ℝ)|^67 ≤ (21112202644307/50000000000000 : ℝ)^51
        have hw : |(5187775851/10000000000 : ℝ)|=(5187775851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4604498929/10000000000 : ℝ)|^67 ≤ (18050286789321/50000000000000 : ℝ)^51
        have hw : |(-4604498929/10000000000 : ℝ)|=(4604498929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-195171489/625000000 : ℝ)|^67 ≤ (21675021117707/100000000000000 : ℝ)^51
        have hw : |(-195171489/625000000 : ℝ)|=(195171489/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305074 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1210699070121103/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (133/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^133 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^133*1^32 ≤ 1^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5907425780553129/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (5907425780553129/5000000000000000 : ℝ)^133 := by
      have hnat : (2 : ℕ)^32*5000000000000000^133 ≤ 5907425780553129^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5907425780553129 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5907425780553129/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (13025550631227361/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13025550631227361/10000000000000000 : ℝ)^133 := by
      have hnat : (3 : ℕ)^32*10000000000000000^133 ≤ 13025550631227361^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13025550631227361 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13025550631227361/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (907425780553129/5000000000000000 : ℝ)) (beta := (1210699070121103/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(907425780553129/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1210699070121103/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2584718913/10000000000 : ℝ)*X 0 0+(-6114093669/10000000000 : ℝ)*X 0 1+(-4069835787/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305074_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((6280183297/10000000000 : ℝ)*X 1 0+(673879617/2500000000 : ℝ)*X 1 1+(-756062103/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305074_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3518445703/10000000000 : ℝ)*X 2 0+(-3858125441/10000000000 : ℝ)*X 2 1+(1385014843/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305074_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_3 : ((9999999999/10000000000 : ℝ)*X 1 0+(117/10000000000 : ℝ)*X 1 1+(9999999999/10000000000 : ℝ)*X 2 0+(117/10000000000 : ℝ)*X 2 1+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305074_s0_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((5187775851/10000000000 : ℝ)*X 0 0+(-4604498929/10000000000 : ℝ)*X 0 1+(-195171489/625000000 : ℝ)*X 0 2+(5187775851/10000000000 : ℝ)*X 1 0+(-4604498929/10000000000 : ℝ)*X 1 1+(-195171489/625000000 : ℝ)*X 1 2+(5187775851/10000000000 : ℝ)*X 2 0+(-4604498929/10000000000 : ℝ)*X 2 1+(-195171489/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305074_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-19299/3125 : ℝ) < ((-4779/3125 : ℝ)*P 0+(-4779/3125 : ℝ)*P 1+(-4779/3125 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-19299/3125 : ℝ) < (-6152898064196927674789226109/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57323/250000000000 : ℝ)*(base1) + (12489/100000000000 : ℝ)*(base17) + (38439/500000000000 : ℝ)*(base22) + (256527022407/1000000000000 : ℝ)*(base39) + (8339440007/40000000000 : ℝ)*(base49) + (104754485167/1000000000000 : ℝ)*(base50) + (23207/1000000000000 : ℝ)*(base60) + (1529280701687/1000000000000 : ℝ)*(major_s0_0) + (4779/3125 : ℝ)*(major_s0_1) + (4779/3125 : ℝ)*(major_s0_2) + (2050966250687/1000000000000 : ℝ)*(sp_s0_0) + (1025482948253/500000000000 : ℝ)*(sp_s0_1) + (2050965944517/1000000000000 : ℝ)*(sp_s0_2) + (701687/1000000000000 : ℝ)*(sp_s0_3) + (249999942677/250000000000 : ℝ)*(sp_s0_6) + (410193204279/200000000000 : ℝ)*(f.sum) + (5333590877/10000000000000000000000 : ℝ)*base62 + (303044701/2000000000000000000000 : ℝ)*base64 + (6432722699/10000000000000000000000 : ℝ)*base66 + (467503137/10000000000000000000000 : ℝ)*base69 + (1712501044071377/5000000000000000000000000000 : ℝ)*base70 + (4455479888400761/10000000000000000000000000000 : ℝ)*base73 + (559290889/1250000000000000000000 : ℝ)*base74 + (1446388221571377/5000000000000000000000000000 : ℝ)*base76 + (762290214400761/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p005_b032 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (c : Fin 88) (hlo : 73 ≤ c.val) (hhi : c.val < 77)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=73 ∨ c=74 ∨ c=75 ∨ c=76 := by omega
  rcases hc with rfl|rfl|rfl|rfl
  · exact collision_c305073 p hpa (by linarith only [hpb]) X hX
  · exact collision_c305074 p hpa (by linarith only [hpb]) X hX
  · exact collision_c305075 p hpa (by linarith only [hpb]) X hX
  · exact collision_c305076 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (c : Fin 88) (hlo : 73 ≤ c.val) (hhi : c.val < 77)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p005_b032 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

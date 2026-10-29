-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p016_b025
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:01:48.30699+00:00
-- url     : https://prove2.me/submissions/28d09ce7-cd67-4cd2-b852-48c9a22715af

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316059_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316059_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316059_s2
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316060_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316060_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316060_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316061_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316061_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316061_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316061_s3
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316062_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316062_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316062_s2
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c316059 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]]) : False := by
  have h0 := collision_c316059_s0 p hpa hpb X hX
  have h1 := collision_c316059_s1 p hpa hpb X hX h0
  exact collision_c316059_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c316060 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]]) : False := by
  have h0 := collision_c316060_s0 p hpa hpb X hX
  have h1 := collision_c316060_s1 p hpa hpb X hX h0
  exact collision_c316060_s2 p hpa hpb X hX h1

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c316061 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]]) : False := by
  have h0 := collision_c316061_s0 p hpa hpb X hX
  have h1 := collision_c316061_s1 p hpa hpb X hX h0
  have h2 := collision_c316061_s2 p hpa hpb X hX h1
  exact collision_c316061_s3 p hpa hpb X hX h2

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6 HlawkaSchatten.DiagonalCutoff4
theorem HlawkaSchatten.DiagonalCutoff4.collision_c316062 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]]) : False := by
  have h0 := collision_c316062_s0 p hpa hpb X hX
  have h1 := collision_c316062_s1 p hpa hpb X hX h0
  exact collision_c316062_s2 p hpa hpb X hX h1

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
theorem collision_support_c316058_s0_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2988015439/10000000000 : ℝ)*x 0 + (597603073/2000000000 : ℝ)*x 1 + (-635881387/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2988015439/10000000000 : ℝ)^77 ≤ (1360374093387/6250000000000 : ℝ)^61 := by
    have hnat : (2988015439 : ℕ)^77*6250000000000^61 ≤ 1360374093387^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2988015439 10000000000 1360374093387 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597603073/2000000000 : ℝ)^77 ≤ (4353196962751/20000000000000 : ℝ)^61 := by
    have hnat : (597603073 : ℕ)^77*20000000000000^61 ≤ 4353196962751^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597603073 2000000000 4353196962751 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (635881387/1000000000 : ℝ)^77 ≤ (14117007418441/25000000000000 : ℝ)^61 := by
    have hnat : (635881387 : ℕ)^77*25000000000000^61 ≤ 14117007418441^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635881387 1000000000 14117007418441 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2988015439/10000000000 : ℝ), (597603073/2000000000 : ℝ), (-635881387/1000000000 : ℝ)] ![(1360374093387/6250000000000 : ℝ), (4353196962751/20000000000000 : ℝ), (14117007418441/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2988015439/10000000000 : ℝ)|^77 ≤ (1360374093387/6250000000000 : ℝ)^61
        have hw : |(-2988015439/10000000000 : ℝ)|=(2988015439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(597603073/2000000000 : ℝ)|^77 ≤ (4353196962751/20000000000000 : ℝ)^61
        have hw : |(597603073/2000000000 : ℝ)|=(597603073/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-635881387/1000000000 : ℝ)|^77 ≤ (14117007418441/25000000000000 : ℝ)^61
        have hw : |(-635881387/1000000000 : ℝ)|=(635881387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316058_s0_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2988015387/10000000000 : ℝ)*x 0 + (-1494007633/5000000000 : ℝ)*x 1 + (-3179406997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2988015387/10000000000 : ℝ)^77 ≤ (21765985016047/100000000000000 : ℝ)^61 := by
    have hnat : (2988015387 : ℕ)^77*100000000000000^61 ≤ 21765985016047^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2988015387 10000000000 21765985016047 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1494007633/5000000000 : ℝ)^77 ≤ (272074798793/1250000000000 : ℝ)^61 := by
    have hnat : (1494007633 : ℕ)^77*1250000000000^61 ≤ 272074798793^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1494007633 5000000000 272074798793 1250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3179406997/5000000000 : ℝ)^77 ≤ (28234015531873/50000000000000 : ℝ)^61 := by
    have hnat : (3179406997 : ℕ)^77*50000000000000^61 ≤ 28234015531873^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3179406997 5000000000 28234015531873 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2988015387/10000000000 : ℝ), (-1494007633/5000000000 : ℝ), (-3179406997/5000000000 : ℝ)] ![(21765985016047/100000000000000 : ℝ), (272074798793/1250000000000 : ℝ), (28234015531873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2988015387/10000000000 : ℝ)|^77 ≤ (21765985016047/100000000000000 : ℝ)^61
        have hw : |(2988015387/10000000000 : ℝ)|=(2988015387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1494007633/5000000000 : ℝ)|^77 ≤ (272074798793/1250000000000 : ℝ)^61
        have hw : |(-1494007633/5000000000 : ℝ)|=(1494007633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3179406997/5000000000 : ℝ)|^77 ≤ (28234015531873/50000000000000 : ℝ)^61
        have hw : |(-3179406997/5000000000 : ℝ)|=(3179406997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316058_s0_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-505753709/2500000000 : ℝ)*x 0 + (30406241/400000000 : ℝ)*x 1 + (-538351271/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (505753709/2500000000 : ℝ)^77 ≤ (6651751874087/50000000000000 : ℝ)^61 := by
    have hnat : (505753709 : ℕ)^77*50000000000000^61 ≤ 6651751874087^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505753709 2500000000 6651751874087 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30406241/400000000 : ℝ)^77 ≤ (3866954259949/100000000000000 : ℝ)^61 := by
    have hnat : (30406241 : ℕ)^77*100000000000000^61 ≤ 3866954259949^61*400000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30406241 400000000 3866954259949 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538351271/625000000 : ℝ)^77 ≤ (16565908397591/20000000000000 : ℝ)^61 := by
    have hnat : (538351271 : ℕ)^77*20000000000000^61 ≤ 16565908397591^61*625000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538351271 625000000 16565908397591 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-505753709/2500000000 : ℝ), (30406241/400000000 : ℝ), (-538351271/625000000 : ℝ)] ![(6651751874087/50000000000000 : ℝ), (3866954259949/100000000000000 : ℝ), (16565908397591/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-505753709/2500000000 : ℝ)|^77 ≤ (6651751874087/50000000000000 : ℝ)^61
        have hw : |(-505753709/2500000000 : ℝ)|=(505753709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(30406241/400000000 : ℝ)|^77 ≤ (3866954259949/100000000000000 : ℝ)^61
        have hw : |(30406241/400000000 : ℝ)|=(30406241/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-538351271/625000000 : ℝ)|^77 ≤ (16565908397591/20000000000000 : ℝ)^61
        have hw : |(-538351271/625000000 : ℝ)|=(538351271/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316058_s0_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (98911201/625000000 : ℝ)*x 0 + (-1272837947/10000000000 : ℝ)*x 1 + (-4306810113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98911201/625000000 : ℝ)^77 ≤ (9758048110073/100000000000000 : ℝ)^61 := by
    have hnat : (98911201 : ℕ)^77*100000000000000^61 ≤ 9758048110073^61*625000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98911201 625000000 9758048110073 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1272837947/10000000000 : ℝ)^77 ≤ (1482482245061/20000000000000 : ℝ)^61 := by
    have hnat : (1272837947 : ℕ)^77*20000000000000^61 ≤ 1482482245061^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272837947 10000000000 1482482245061 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4306810113/5000000000 : ℝ)^77 ≤ (41414770326367/50000000000000 : ℝ)^61 := by
    have hnat : (4306810113 : ℕ)^77*50000000000000^61 ≤ 41414770326367^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306810113 5000000000 41414770326367 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(98911201/625000000 : ℝ), (-1272837947/10000000000 : ℝ), (-4306810113/5000000000 : ℝ)] ![(9758048110073/100000000000000 : ℝ), (1482482245061/20000000000000 : ℝ), (41414770326367/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(98911201/625000000 : ℝ)|^77 ≤ (9758048110073/100000000000000 : ℝ)^61
        have hw : |(98911201/625000000 : ℝ)|=(98911201/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1272837947/10000000000 : ℝ)|^77 ≤ (1482482245061/20000000000000 : ℝ)^61
        have hw : |(-1272837947/10000000000 : ℝ)|=(1272837947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4306810113/5000000000 : ℝ)|^77 ≤ (41414770326367/50000000000000 : ℝ)^61
        have hw : |(-4306810113/5000000000 : ℝ)|=(4306810113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316058_s0_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (180929361/500000000 : ℝ)*x 0 + (169544881/250000000 : ℝ)*x 1 + (1744254839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (180929361/500000000 : ℝ)^77 ≤ (13858493165867/50000000000000 : ℝ)^61 := by
    have hnat : (180929361 : ℕ)^77*50000000000000^61 ≤ 13858493165867^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180929361 500000000 13858493165867 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169544881/250000000 : ℝ)^77 ≤ (6125015758363/10000000000000 : ℝ)^61 := by
    have hnat : (169544881 : ℕ)^77*10000000000000^61 ≤ 6125015758363^61*250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169544881 250000000 6125015758363 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1744254839/10000000000 : ℝ)^77 ≤ (1103285607081/10000000000000 : ℝ)^61 := by
    have hnat : (1744254839 : ℕ)^77*10000000000000^61 ≤ 1103285607081^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1744254839 10000000000 1103285607081 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(180929361/500000000 : ℝ), (169544881/250000000 : ℝ), (1744254839/10000000000 : ℝ)] ![(13858493165867/50000000000000 : ℝ), (6125015758363/10000000000000 : ℝ), (1103285607081/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(180929361/500000000 : ℝ)|^77 ≤ (13858493165867/50000000000000 : ℝ)^61
        have hw : |(180929361/500000000 : ℝ)|=(180929361/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169544881/250000000 : ℝ)|^77 ≤ (6125015758363/10000000000000 : ℝ)^61
        have hw : |(169544881/250000000 : ℝ)|=(169544881/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1744254839/10000000000 : ℝ)|^77 ≤ (1103285607081/10000000000000 : ℝ)^61
        have hw : |(1744254839/10000000000 : ℝ)|=(1744254839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316058_s0_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (221467539/1250000000 : ℝ)*x 0 + (4548800133/5000000000 : ℝ)*x 1 + (-94767/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221467539/1250000000 : ℝ)^77 ≤ (2250552229463/20000000000000 : ℝ)^61 := by
    have hnat : (221467539 : ℕ)^77*20000000000000^61 ≤ 2250552229463^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221467539 1250000000 2250552229463 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4548800133/5000000000 : ℝ)^77 ≤ (5546686025457/6250000000000 : ℝ)^61 := by
    have hnat : (4548800133 : ℕ)^77*6250000000000^61 ≤ 5546686025457^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4548800133 5000000000 5546686025457 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94767/2500000000 : ℝ)^77 ≤ (32805479/12500000000000 : ℝ)^61 := by
    have hnat : (94767 : ℕ)^77*12500000000000^61 ≤ 32805479^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94767 2500000000 32805479 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(221467539/1250000000 : ℝ), (4548800133/5000000000 : ℝ), (-94767/2500000000 : ℝ)] ![(2250552229463/20000000000000 : ℝ), (5546686025457/6250000000000 : ℝ), (32805479/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(221467539/1250000000 : ℝ)|^77 ≤ (2250552229463/20000000000000 : ℝ)^61
        have hw : |(221467539/1250000000 : ℝ)|=(221467539/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4548800133/5000000000 : ℝ)|^77 ≤ (5546686025457/6250000000000 : ℝ)^61
        have hw : |(4548800133/5000000000 : ℝ)|=(4548800133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94767/2500000000 : ℝ)|^77 ≤ (32805479/12500000000000 : ℝ)^61
        have hw : |(-94767/2500000000 : ℝ)|=(94767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316058_s0_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-12005383/100000000 : ℝ)*x 0 + (958155053/5000000000 : ℝ)*x 1 + (-1054621209/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12005383/100000000 : ℝ)^77 ≤ (2753980549/40000000000 : ℝ)^61 := by
    have hnat : (12005383 : ℕ)^77*40000000000^61 ≤ 2753980549^61*100000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12005383 100000000 2753980549 40000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (958155053/5000000000 : ℝ)^77 ≤ (496958458377/4000000000000 : ℝ)^61 := by
    have hnat : (958155053 : ℕ)^77*4000000000000^61 ≤ 496958458377^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958155053 5000000000 496958458377 4000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054621209/1250000000 : ℝ)^77 ≤ (80691087156121/100000000000000 : ℝ)^61 := by
    have hnat : (1054621209 : ℕ)^77*100000000000000^61 ≤ 80691087156121^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054621209 1250000000 80691087156121 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12005383/100000000 : ℝ), (958155053/5000000000 : ℝ), (-1054621209/1250000000 : ℝ)] ![(2753980549/40000000000 : ℝ), (496958458377/4000000000000 : ℝ), (80691087156121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12005383/100000000 : ℝ)|^77 ≤ (2753980549/40000000000 : ℝ)^61
        have hw : |(-12005383/100000000 : ℝ)|=(12005383/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(958155053/5000000000 : ℝ)|^77 ≤ (496958458377/4000000000000 : ℝ)^61
        have hw : |(958155053/5000000000 : ℝ)|=(958155053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1054621209/1250000000 : ℝ)|^77 ≤ (80691087156121/100000000000000 : ℝ)^61
        have hw : |(-1054621209/1250000000 : ℝ)|=(1054621209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316058_s0_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1200537417/10000000000 : ℝ)*x 0 + (-239538587/1250000000 : ℝ)*x 1 + (-8436971157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1200537417/10000000000 : ℝ)^77 ≤ (3442472490179/50000000000000 : ℝ)^61 := by
    have hnat : (1200537417 : ℕ)^77*50000000000000^61 ≤ 3442472490179^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200537417 10000000000 3442472490179 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (239538587/1250000000 : ℝ)^77 ≤ (12423949920263/100000000000000 : ℝ)^61 := by
    have hnat : (239538587 : ℕ)^77*100000000000000^61 ≤ 12423949920263^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239538587 1250000000 12423949920263 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8436971157/10000000000 : ℝ)^77 ≤ (80691105083897/100000000000000 : ℝ)^61 := by
    have hnat : (8436971157 : ℕ)^77*100000000000000^61 ≤ 80691105083897^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8436971157 10000000000 80691105083897 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1200537417/10000000000 : ℝ), (-239538587/1250000000 : ℝ), (-8436971157/10000000000 : ℝ)] ![(3442472490179/50000000000000 : ℝ), (12423949920263/100000000000000 : ℝ), (80691105083897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1200537417/10000000000 : ℝ)|^77 ≤ (3442472490179/50000000000000 : ℝ)^61
        have hw : |(1200537417/10000000000 : ℝ)|=(1200537417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-239538587/1250000000 : ℝ)|^77 ≤ (12423949920263/100000000000000 : ℝ)^61
        have hw : |(-239538587/1250000000 : ℝ)|=(239538587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8436971157/10000000000 : ℝ)|^77 ≤ (80691105083897/100000000000000 : ℝ)^61
        have hw : |(-8436971157/10000000000 : ℝ)|=(8436971157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316058_s0_16 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3839586809/5000000000 : ℝ)*x 0 + (1588087459/5000000000 : ℝ)*x 1 + (90763691/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3839586809/5000000000 : ℝ)^77 ≤ (7165277927417/10000000000000 : ℝ)^61 := by
    have hnat : (3839586809 : ℕ)^77*10000000000000^61 ≤ 7165277927417^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3839586809 5000000000 7165277927417 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1588087459/5000000000 : ℝ)^77 ≤ (1469387720099/6250000000000 : ℝ)^61 := by
    have hnat : (1588087459 : ℕ)^77*6250000000000^61 ≤ 1469387720099^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588087459 5000000000 1469387720099 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90763691/1000000000 : ℝ)^77 ≤ (2418508591693/50000000000000 : ℝ)^61 := by
    have hnat : (90763691 : ℕ)^77*50000000000000^61 ≤ 2418508591693^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90763691 1000000000 2418508591693 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3839586809/5000000000 : ℝ), (1588087459/5000000000 : ℝ), (90763691/1000000000 : ℝ)] ![(7165277927417/10000000000000 : ℝ), (1469387720099/6250000000000 : ℝ), (2418508591693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3839586809/5000000000 : ℝ)|^77 ≤ (7165277927417/10000000000000 : ℝ)^61
        have hw : |(3839586809/5000000000 : ℝ)|=(3839586809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1588087459/5000000000 : ℝ)|^77 ≤ (1469387720099/6250000000000 : ℝ)^61
        have hw : |(1588087459/5000000000 : ℝ)|=(1588087459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(90763691/1000000000 : ℝ)|^77 ≤ (2418508591693/50000000000000 : ℝ)^61
        have hw : |(90763691/1000000000 : ℝ)|=(90763691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316058_s0_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-5665353897/10000000000 : ℝ)*x 0 + (1087320439/5000000000 : ℝ)*x 1 + (-902346867/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5665353897/10000000000 : ℝ)^77 ≤ (3050561105383/6250000000000 : ℝ)^61 := by
    have hnat : (5665353897 : ℕ)^77*6250000000000^61 ≤ 3050561105383^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5665353897 10000000000 3050561105383 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087320439/5000000000 : ℝ)^77 ≤ (14574295135123/100000000000000 : ℝ)^61 := by
    have hnat : (1087320439 : ℕ)^77*100000000000000^61 ≤ 14574295135123^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087320439 5000000000 14574295135123 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902346867/2000000000 : ℝ)^77 ≤ (18308363584439/50000000000000 : ℝ)^61 := by
    have hnat : (902346867 : ℕ)^77*50000000000000^61 ≤ 18308363584439^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902346867 2000000000 18308363584439 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5665353897/10000000000 : ℝ), (1087320439/5000000000 : ℝ), (-902346867/2000000000 : ℝ)] ![(3050561105383/6250000000000 : ℝ), (14574295135123/100000000000000 : ℝ), (18308363584439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5665353897/10000000000 : ℝ)|^77 ≤ (3050561105383/6250000000000 : ℝ)^61
        have hw : |(-5665353897/10000000000 : ℝ)|=(5665353897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087320439/5000000000 : ℝ)|^77 ≤ (14574295135123/100000000000000 : ℝ)^61
        have hw : |(1087320439/5000000000 : ℝ)|=(1087320439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-902346867/2000000000 : ℝ)|^77 ≤ (18308363584439/50000000000000 : ℝ)^61
        have hw : |(-902346867/2000000000 : ℝ)|=(902346867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316058_s0_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (954137047/10000000000 : ℝ)*x 0 + (-594672509/5000000000 : ℝ)*x 1 + (-1808094041/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (954137047/10000000000 : ℝ)^77 ≤ (2575951509949/50000000000000 : ℝ)^61 := by
    have hnat : (954137047 : ℕ)^77*50000000000000^61 ≤ 2575951509949^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954137047 10000000000 2575951509949 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (594672509/5000000000 : ℝ)^77 ≤ (6804021173943/100000000000000 : ℝ)^61 := by
    have hnat : (594672509 : ℕ)^77*100000000000000^61 ≤ 6804021173943^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594672509 5000000000 6804021173943 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1808094041/2000000000 : ℝ)^77 ≤ (88044075795369/100000000000000 : ℝ)^61 := by
    have hnat : (1808094041 : ℕ)^77*100000000000000^61 ≤ 88044075795369^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1808094041 2000000000 88044075795369 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(954137047/10000000000 : ℝ), (-594672509/5000000000 : ℝ), (-1808094041/2000000000 : ℝ)] ![(2575951509949/50000000000000 : ℝ), (6804021173943/100000000000000 : ℝ), (88044075795369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(954137047/10000000000 : ℝ)|^77 ≤ (2575951509949/50000000000000 : ℝ)^61
        have hw : |(954137047/10000000000 : ℝ)|=(954137047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-594672509/5000000000 : ℝ)|^77 ≤ (6804021173943/100000000000000 : ℝ)^61
        have hw : |(-594672509/5000000000 : ℝ)|=(594672509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1808094041/2000000000 : ℝ)|^77 ≤ (88044075795369/100000000000000 : ℝ)^61
        have hw : |(-1808094041/2000000000 : ℝ)|=(1808094041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316058_s0_23 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (787298279/1000000000 : ℝ)*x 0 + (2695803777/10000000000 : ℝ)*x 1 + (1208493231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (787298279/1000000000 : ℝ)^77 ≤ (14788602898639/20000000000000 : ℝ)^61 := by
    have hnat : (787298279 : ℕ)^77*20000000000000^61 ≤ 14788602898639^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787298279 1000000000 14788602898639 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695803777/10000000000 : ℝ)^77 ≤ (9557198733181/50000000000000 : ℝ)^61 := by
    have hnat : (2695803777 : ℕ)^77*50000000000000^61 ≤ 9557198733181^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695803777 10000000000 9557198733181 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1208493231/10000000000 : ℝ)^77 ≤ (1388517606101/20000000000000 : ℝ)^61 := by
    have hnat : (1208493231 : ℕ)^77*20000000000000^61 ≤ 1388517606101^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208493231 10000000000 1388517606101 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(787298279/1000000000 : ℝ), (2695803777/10000000000 : ℝ), (1208493231/10000000000 : ℝ)] ![(14788602898639/20000000000000 : ℝ), (9557198733181/50000000000000 : ℝ), (1388517606101/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(787298279/1000000000 : ℝ)|^77 ≤ (14788602898639/20000000000000 : ℝ)^61
        have hw : |(787298279/1000000000 : ℝ)|=(787298279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695803777/10000000000 : ℝ)|^77 ≤ (9557198733181/50000000000000 : ℝ)^61
        have hw : |(2695803777/10000000000 : ℝ)|=(2695803777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1208493231/10000000000 : ℝ)|^77 ≤ (1388517606101/20000000000000 : ℝ)^61
        have hw : |(1208493231/10000000000 : ℝ)|=(1208493231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316058_s0_27 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (100361627/1000000000 : ℝ)*x 0 + (2390606239/2500000000 : ℝ)*x 1 + (-37309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100361627/1000000000 : ℝ)^77 ≤ (2745704615739/50000000000000 : ℝ)^61 := by
    have hnat : (100361627 : ℕ)^77*50000000000000^61 ≤ 2745704615739^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100361627 1000000000 2745704615739 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2390606239/2500000000 : ℝ)^77 ≤ (94508557032059/100000000000000 : ℝ)^61 := by
    have hnat : (2390606239 : ℕ)^77*100000000000000^61 ≤ 94508557032059^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2390606239 2500000000 94508557032059 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37309/5000000000 : ℝ)^77 ≤ (674599/2000000000000 : ℝ)^61 := by
    have hnat : (37309 : ℕ)^77*2000000000000^61 ≤ 674599^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37309 5000000000 674599 2000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(100361627/1000000000 : ℝ), (2390606239/2500000000 : ℝ), (-37309/5000000000 : ℝ)] ![(2745704615739/50000000000000 : ℝ), (94508557032059/100000000000000 : ℝ), (674599/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(100361627/1000000000 : ℝ)|^77 ≤ (2745704615739/50000000000000 : ℝ)^61
        have hw : |(100361627/1000000000 : ℝ)|=(100361627/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2390606239/2500000000 : ℝ)|^77 ≤ (94508557032059/100000000000000 : ℝ)^61
        have hw : |(2390606239/2500000000 : ℝ)|=(2390606239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-37309/5000000000 : ℝ)|^77 ≤ (674599/2000000000000 : ℝ)^61
        have hw : |(-37309/5000000000 : ℝ)|=(37309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316058_s1_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-423435469/1250000000 : ℝ)*x 0 + (1664530769/5000000000 : ℝ)*x 1 + (-1146692691/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423435469/1250000000 : ℝ)^77 ≤ (2550153531863/10000000000000 : ℝ)^61 := by
    have hnat : (423435469 : ℕ)^77*10000000000000^61 ≤ 2550153531863^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423435469 1250000000 2550153531863 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1664530769/5000000000 : ℝ)^77 ≤ (6236905953183/25000000000000 : ℝ)^61 := by
    have hnat : (1664530769 : ℕ)^77*25000000000000^61 ≤ 6236905953183^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1664530769 5000000000 6236905953183 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1146692691/2000000000 : ℝ)^77 ≤ (24775420426569/50000000000000 : ℝ)^61 := by
    have hnat : (1146692691 : ℕ)^77*50000000000000^61 ≤ 24775420426569^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146692691 2000000000 24775420426569 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-423435469/1250000000 : ℝ), (1664530769/5000000000 : ℝ), (-1146692691/2000000000 : ℝ)] ![(2550153531863/10000000000000 : ℝ), (6236905953183/25000000000000 : ℝ), (24775420426569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-423435469/1250000000 : ℝ)|^77 ≤ (2550153531863/10000000000000 : ℝ)^61
        have hw : |(-423435469/1250000000 : ℝ)|=(423435469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1664530769/5000000000 : ℝ)|^77 ≤ (6236905953183/25000000000000 : ℝ)^61
        have hw : |(1664530769/5000000000 : ℝ)|=(1664530769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1146692691/2000000000 : ℝ)|^77 ≤ (24775420426569/50000000000000 : ℝ)^61
        have hw : |(-1146692691/2000000000 : ℝ)|=(1146692691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316058_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3145923571/10000000000 : ℝ)*x 0 + (-3088754709/10000000000 : ℝ)*x 1 + (-3072221329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3145923571/10000000000 : ℝ)^77 ≤ (185823214609/800000000000 : ℝ)^61 := by
    have hnat : (3145923571 : ℕ)^77*800000000000^61 ≤ 185823214609^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3145923571 10000000000 185823214609 800000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3088754709/10000000000 : ℝ)^77 ≤ (22696355272919/100000000000000 : ℝ)^61 := by
    have hnat : (3088754709 : ℕ)^77*100000000000000^61 ≤ 22696355272919^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3088754709 10000000000 22696355272919 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3072221329/5000000000 : ℝ)^77 ≤ (27037871443391/50000000000000 : ℝ)^61 := by
    have hnat : (3072221329 : ℕ)^77*50000000000000^61 ≤ 27037871443391^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3072221329 5000000000 27037871443391 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3145923571/10000000000 : ℝ), (-3088754709/10000000000 : ℝ), (-3072221329/5000000000 : ℝ)] ![(185823214609/800000000000 : ℝ), (22696355272919/100000000000000 : ℝ), (27037871443391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3145923571/10000000000 : ℝ)|^77 ≤ (185823214609/800000000000 : ℝ)^61
        have hw : |(3145923571/10000000000 : ℝ)|=(3145923571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3088754709/10000000000 : ℝ)|^77 ≤ (22696355272919/100000000000000 : ℝ)^61
        have hw : |(-3088754709/10000000000 : ℝ)|=(3088754709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3072221329/5000000000 : ℝ)|^77 ≤ (27037871443391/50000000000000 : ℝ)^61
        have hw : |(-3072221329/5000000000 : ℝ)|=(3072221329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316058_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1087397701/2000000000 : ℝ)*x 0 + (2635757773/5000000000 : ℝ)*x 1 + (374211647/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087397701/2000000000 : ℝ)^77 ≤ (46338740837133/100000000000000 : ℝ)^61 := by
    have hnat : (1087397701 : ℕ)^77*100000000000000^61 ≤ 46338740837133^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087397701 2000000000 46338740837133 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2635757773/5000000000 : ℝ)^77 ≤ (1114142002711/2500000000000 : ℝ)^61 := by
    have hnat : (2635757773 : ℕ)^77*2500000000000^61 ≤ 1114142002711^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635757773 5000000000 1114142002711 2500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (374211647/2500000000 : ℝ)^77 ≤ (72764632261/800000000000 : ℝ)^61 := by
    have hnat : (374211647 : ℕ)^77*800000000000^61 ≤ 72764632261^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374211647 2500000000 72764632261 800000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087397701/2000000000 : ℝ), (2635757773/5000000000 : ℝ), (374211647/2500000000 : ℝ)] ![(46338740837133/100000000000000 : ℝ), (1114142002711/2500000000000 : ℝ), (72764632261/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087397701/2000000000 : ℝ)|^77 ≤ (46338740837133/100000000000000 : ℝ)^61
        have hw : |(1087397701/2000000000 : ℝ)|=(1087397701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2635757773/5000000000 : ℝ)|^77 ≤ (1114142002711/2500000000000 : ℝ)^61
        have hw : |(2635757773/5000000000 : ℝ)|=(2635757773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(374211647/2500000000 : ℝ)|^77 ≤ (72764632261/800000000000 : ℝ)^61
        have hw : |(374211647/2500000000 : ℝ)|=(374211647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316058_s1_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2402933929/5000000000 : ℝ)*x 0 + (1486613077/2500000000 : ℝ)*x 1 + (-1413234339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2402933929/5000000000 : ℝ)^77 ≤ (991384555303/2500000000000 : ℝ)^61 := by
    have hnat : (2402933929 : ℕ)^77*2500000000000^61 ≤ 991384555303^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2402933929 5000000000 991384555303 2500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1486613077/2500000000 : ℝ)^77 ≤ (51885607734407/100000000000000 : ℝ)^61 := by
    have hnat : (1486613077 : ℕ)^77*100000000000000^61 ≤ 51885607734407^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1486613077 2500000000 51885607734407 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1413234339/10000000000 : ℝ)^77 ≤ (8459010041837/100000000000000 : ℝ)^61 := by
    have hnat : (1413234339 : ℕ)^77*100000000000000^61 ≤ 8459010041837^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1413234339 10000000000 8459010041837 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2402933929/5000000000 : ℝ), (1486613077/2500000000 : ℝ), (-1413234339/10000000000 : ℝ)] ![(991384555303/2500000000000 : ℝ), (51885607734407/100000000000000 : ℝ), (8459010041837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2402933929/5000000000 : ℝ)|^77 ≤ (991384555303/2500000000000 : ℝ)^61
        have hw : |(2402933929/5000000000 : ℝ)|=(2402933929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1486613077/2500000000 : ℝ)|^77 ≤ (51885607734407/100000000000000 : ℝ)^61
        have hw : |(1486613077/2500000000 : ℝ)|=(1486613077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1413234339/10000000000 : ℝ)|^77 ≤ (8459010041837/100000000000000 : ℝ)^61
        have hw : |(-1413234339/10000000000 : ℝ)|=(1413234339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316058 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (173433/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base29 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (19/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^19 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^19*1^4 ≤ 1^4*1^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11571102372827199/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11571102372827199/10000000000000000 : ℝ)^19 := by
      have hnat : (2 : ℕ)^4*10000000000000000^19 ≤ 11571102372827199^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11571102372827199 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11571102372827199/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12602206158919821/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12602206158919821/10000000000000000 : ℝ)^19 := by
      have hnat : (3 : ℕ)^4*10000000000000000^19 ≤ 12602206158919821^19*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12602206158919821 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12602206158919821/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1571102372827199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1571102372827199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2988015439/10000000000 : ℝ)*X 0 0+(597603073/2000000000 : ℝ)*X 0 1+(-635881387/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316058_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2988015387/10000000000 : ℝ)*X 1 0+(-1494007633/5000000000 : ℝ)*X 1 1+(-3179406997/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316058_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-505753709/2500000000 : ℝ)*X 0 0+(30406241/400000000 : ℝ)*X 0 1+(-538351271/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316058_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((98911201/625000000 : ℝ)*X 1 0+(-1272837947/10000000000 : ℝ)*X 1 1+(-4306810113/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316058_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((180929361/500000000 : ℝ)*X 2 0+(169544881/250000000 : ℝ)*X 2 1+(1744254839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316058_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((221467539/1250000000 : ℝ)*X 0 0+(4548800133/5000000000 : ℝ)*X 0 1+(-94767/2500000000 : ℝ)*X 0 2+(221467539/1250000000 : ℝ)*X 1 0+(4548800133/5000000000 : ℝ)*X 1 1+(-94767/2500000000 : ℝ)*X 1 2+(221467539/1250000000 : ℝ)*X 2 0+(4548800133/5000000000 : ℝ)*X 2 1+(-94767/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316058_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-12005383/100000000 : ℝ)*X 0 0+(958155053/5000000000 : ℝ)*X 0 1+(-1054621209/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316058_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1200537417/10000000000 : ℝ)*X 1 0+(-239538587/1250000000 : ℝ)*X 1 1+(-8436971157/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316058_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3839586809/5000000000 : ℝ)*X 2 0+(1588087459/5000000000 : ℝ)*X 2 1+(90763691/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316058_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-5665353897/10000000000 : ℝ)*X 0 0+(1087320439/5000000000 : ℝ)*X 0 1+(-902346867/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316058_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((954137047/10000000000 : ℝ)*X 1 0+(-594672509/5000000000 : ℝ)*X 1 1+(-1808094041/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316058_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((787298279/1000000000 : ℝ)*X 2 0+(2695803777/10000000000 : ℝ)*X 2 1+(1208493231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316058_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((100361627/1000000000 : ℝ)*X 0 0+(2390606239/2500000000 : ℝ)*X 0 1+(-37309/5000000000 : ℝ)*X 0 2+(100361627/1000000000 : ℝ)*X 1 0+(2390606239/2500000000 : ℝ)*X 1 1+(-37309/5000000000 : ℝ)*X 1 2+(100361627/1000000000 : ℝ)*X 2 0+(2390606239/2500000000 : ℝ)*X 2 1+(-37309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316058_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((79543/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79543/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1753873466685659526861/100000000000000000000000000 : ℝ) := by norm_num
    linear_combination (248214485171/1000000000000 : ℝ)*(base5) + (543349890217/500000000000 : ℝ)*(base7) + (1542417/1000000000000 : ℝ)*(base44) + (181461/1000000000000 : ℝ)*(base50) + (28108391383/125000000000 : ℝ)*(base53) + (1500177672903/1000000000000 : ℝ)*(major_s0_0) + (750088065243/500000000000 : ℝ)*(major_s0_1) + (1275310541839/1000000000000 : ℝ)*(major_s0_2) + (40652014307/31250000000 : ℝ)*(sp_s0_7) + (1300919659529/1000000000000 : ℝ)*(sp_s0_8) + (88700140909/50000000000 : ℝ)*(sp_s0_9) + (1684778990543/1000000000000 : ℝ)*(sp_s0_13) + (56744121/1000000000000 : ℝ)*(sp_s0_14) + (529981/15625000000 : ℝ)*(sp_s0_27) + (846329156481/1000000000000 : ℝ)*(f.failure) + (1525788333009/1000000000000 : ℝ)*(f.sum) + (5085713184790247/10000000000000000000000000000 : ℝ)*base62 + (1790659453894071/5000000000000000000000000000 : ℝ)*base64 + (898729791468573/2500000000000000000000000000 : ℝ)*base67 + (366381366678961/10000000000000000000000000000 : ℝ)*base68 + (132139751019889/2000000000000000000000000000 : ℝ)*base70 + (2634689583810833/5000000000000000000000000000 : ℝ)*base73 + (2016118471055643/5000000000000000000000000000 : ℝ)*base74 + (1227624378311303/10000000000000000000000000000 : ℝ)*base76 + (2516553073747979/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (52617/100000000000000000 : ℝ)*base87 + (52617/100000000000000000 : ℝ)*base89 + (52617/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9263/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9263/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10149245679467378813883/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (205739167437/100000000000 : ℝ)*(base5) + (54868184619/50000000000 : ℝ)*(base7) + (427698285561/1000000000000 : ℝ)*(base59) + (243435630367/200000000000 : ℝ)*(base60) + (340343360007/200000000000 : ℝ)*(major_s0_0) + (340343360007/200000000000 : ℝ)*(major_s0_1) + (340343360007/200000000000 : ℝ)*(major_s0_2) + (18991/25000000000 : ℝ)*(sp_s0_0) + (364859/50000000000 : ℝ)*(sp_s0_1) + (15425591/250000000000 : ℝ)*(sp_s0_8) + (36180091023/20000000000 : ℝ)*(sp_s0_14) + (904468155623/500000000000 : ℝ)*(sp_s0_15) + (1933184103149/500000000000 : ℝ)*(sp_s0_16) + (14389431/500000000000 : ℝ)*(sp_s0_23) + (960027981989/1000000000000 : ℝ)*(f.failure) + (180900531079/100000000000 : ℝ)*(f.sum) + (50848413/125000000000000000000 : ℝ)*base62 + (122094453715823/1000000000000000000000000000 : ℝ)*base64 + (459922443715823/1000000000000000000000000000 : ℝ)*base66 + (128737031630393/2000000000000000000000000000 : ℝ)*base68 + (1032716788201253/2000000000000000000000000000 : ℝ)*base70 + (317027123115823/1000000000000000000000000000 : ℝ)*base72 + (414357429630393/2000000000000000000000000000 : ℝ)*base75 + (732404590830393/2000000000000000000000000000 : ℝ)*base77 + (26877481184177/500000000000000000000000000 : ℝ)*base79 + (75827/100000000000000000 : ℝ)*base86 + (75827/100000000000000000 : ℝ)*base88 + (75827/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1977/3125 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-1977/3125 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5026786856371630756551/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6594528591/200000000000 : ℝ)*(base5) + (123833177867/250000000000 : ℝ)*(base7) + (63541746719/250000000000 : ℝ)*(base33) + (867821823303/1000000000000 : ℝ)*(base44) + (291607/500000000000 : ℝ)*(base60) + (351963893437/250000000000 : ℝ)*(major_s0_0) + (794200737321/1000000000000 : ℝ)*(major_s0_1) + (103876410039/62500000000 : ℝ)*(major_s0_2) + (51664967/1000000000000 : ℝ)*(sp_s0_8) + (6771213/1000000000000 : ℝ)*(sp_s0_13) + (1050026642067/500000000000 : ℝ)*(sp_s0_21) + (244503202247/250000000000 : ℝ)*(sp_s0_22) + (469714735053/250000000000 : ℝ)*(sp_s0_23) + (532165847039/1000000000000 : ℝ)*(sp_s0_27) + (937634373043/1000000000000 : ℝ)*(f.failure) + (1050026642067/500000000000 : ℝ)*(f.sum) + (4069311918418297/10000000000000000000000000000 : ℝ)*base62 + (30834422496371/312500000000000000000000000 : ℝ)*base64 + (2019062237072831/5000000000000000000000000000 : ℝ)*base67 + (335216721725761/625000000000000000000000000 : ℝ)*base68 + (48474716505601/500000000000000000000000000 : ℝ)*base70 + (1273119943460907/1250000000000000000000000000 : ℝ)*base73 + (1714166657193879/10000000000000000000000000000 : ℝ)*base75 + (987856084692963/2500000000000000000000000000 : ℝ)*base77 + (143643745916459/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (83051/100000000000000000 : ℝ)*base87 + (83051/100000000000000000 : ℝ)*base89 + (83051/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (79543/100000 : ℝ) ^ (19/4 : ℝ) ≤ (3371780861270587229/10000000000000000000 : ℝ) := by
    have hpowers : (79543/100000 : ℝ)^19 ≤ (3371780861270587229/10000000000000000000 : ℝ)^4 := by
      have hnat : (79543 : ℕ)^19*10000000000000000000^4 ≤ 3371780861270587229^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79543 100000 3371780861270587229 10000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79543/100000 : ℝ)) (X := (3371780861270587229/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (13371780861270587229/10000000000000000000 : ℝ) ≤ (10630805148012249/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (13371780861270587229/10000000000000000000 : ℝ)^4 ≤ (10630805148012249/10000000000000000 : ℝ)^19 := by
      have hnat : (13371780861270587229 : ℕ)^4*10000000000000000^19 ≤ 10630805148012249^19*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13371780861270587229 10000000000000000000 10630805148012249 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10630805148012249/10000000000000000 : ℝ)) (X := (13371780861270587229/10000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (8371780861270587229/5000000000000000000 : ℝ) ≤ (11146175134095943/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (8371780861270587229/5000000000000000000 : ℝ)^4 ≤ (11146175134095943/10000000000000000 : ℝ)^19 := by
      have hnat : (8371780861270587229 : ℕ)^4*10000000000000000^19 ≤ 11146175134095943^19*5000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8371780861270587229 5000000000000000000 11146175134095943 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11146175134095943/10000000000000000 : ℝ)) (X := (8371780861270587229/5000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(630805148012249/7954300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(257684993041847/3977150000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (79543/100000 : ℝ)) (alpha := (630805148012249/7954300000000000 : ℝ)) (beta := (257684993041847/3977150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (79543/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(630805148012249/7954300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(257684993041847/3977150000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (9263/12500 : ℝ) ^ (19/4 : ℝ) ≤ (6021266523736668913/25000000000000000000 : ℝ) := by
    have hpowers : (9263/12500 : ℝ)^19 ≤ (6021266523736668913/25000000000000000000 : ℝ)^4 := by
      have hnat : (9263 : ℕ)^19*25000000000000000000^4 ≤ 6021266523736668913^4*12500^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9263 12500 6021266523736668913 25000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9263/12500 : ℝ)) (X := (6021266523736668913/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (31021266523736668913/25000000000000000000 : ℝ) ≤ (1308098469432999/1250000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (31021266523736668913/25000000000000000000 : ℝ)^4 ≤ (1308098469432999/1250000000000000 : ℝ)^19 := by
      have hnat : (31021266523736668913 : ℕ)^4*1250000000000000^19 ≤ 1308098469432999^19*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31021266523736668913 25000000000000000000 1308098469432999 1250000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1308098469432999/1250000000000000 : ℝ)) (X := (31021266523736668913/25000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (18521266523736668913/12500000000000000000 : ℝ) ≤ (2715748967277023/2500000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (18521266523736668913/12500000000000000000 : ℝ)^4 ≤ (2715748967277023/2500000000000000 : ℝ)^19 := by
      have hnat : (18521266523736668913 : ℕ)^4*2500000000000000^19 ≤ 2715748967277023^19*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18521266523736668913 12500000000000000000 2715748967277023 2500000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2715748967277023/2500000000000000 : ℝ)) (X := (18521266523736668913/12500000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(58098469432999/926300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(3982081136441/74104000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (9263/12500 : ℝ)) (alpha := (58098469432999/926300000000000 : ℝ)) (beta := (3982081136441/74104000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (9263/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(58098469432999/926300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(3982081136441/74104000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (1977/3125 : ℝ) ^ (19/4 : ℝ) ≤ (11363027984862287893/100000000000000000000 : ℝ) := by
    have hpowers : (1977/3125 : ℝ)^19 ≤ (11363027984862287893/100000000000000000000 : ℝ)^4 := by
      have hnat : (1977 : ℕ)^19*100000000000000000000^4 ≤ 11363027984862287893^4*3125^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1977 3125 11363027984862287893 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1977/3125 : ℝ)) (X := (11363027984862287893/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (111363027984862287893/100000000000000000000 : ℝ) ≤ (5114582889381701/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (111363027984862287893/100000000000000000000 : ℝ)^4 ≤ (5114582889381701/5000000000000000 : ℝ)^19 := by
      have hnat : (111363027984862287893 : ℕ)^4*5000000000000000^19 ≤ 5114582889381701^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111363027984862287893 100000000000000000000 5114582889381701 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5114582889381701/5000000000000000 : ℝ)) (X := (111363027984862287893/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (61363027984862287893/50000000000000000000 : ℝ) ≤ (10440553715664271/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (61363027984862287893/50000000000000000000 : ℝ)^4 ≤ (10440553715664271/10000000000000000 : ℝ)^19 := by
      have hnat : (61363027984862287893 : ℕ)^4*10000000000000000^19 ≤ 10440553715664271^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61363027984862287893 50000000000000000000 10440553715664271 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10440553715664271/10000000000000000 : ℝ)) (X := (61363027984862287893/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(38194296460567/1054400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(70462645633623/2108800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1977/3125 : ℝ)) (alpha := (38194296460567/1054400000000000 : ℝ)) (beta := (70462645633623/2108800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1977/3125 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(38194296460567/1054400000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(70462645633623/2108800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-423435469/1250000000 : ℝ)*X 0 0+(1664530769/5000000000 : ℝ)*X 0 1+(-1146692691/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316058_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3145923571/10000000000 : ℝ)*X 1 0+(-3088754709/10000000000 : ℝ)*X 1 1+(-3072221329/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316058_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1087397701/2000000000 : ℝ)*X 2 0+(2635757773/5000000000 : ℝ)*X 2 1+(374211647/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316058_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2402933929/5000000000 : ℝ)*X 0 0+(1486613077/2500000000 : ℝ)*X 0 1+(-1413234339/10000000000 : ℝ)*X 0 2+(2402933929/5000000000 : ℝ)*X 1 0+(1486613077/2500000000 : ℝ)*X 1 1+(-1413234339/10000000000 : ℝ)*X 1 2+(2402933929/5000000000 : ℝ)*X 2 0+(1486613077/2500000000 : ℝ)*X 2 1+(-1413234339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316058_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-381771/50000 : ℝ) < ((-177257/100000 : ℝ)*P 0+(-177257/100000 : ℝ)*P 1+(-177257/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-381771/50000 : ℝ) < (-37041859413714549564540322392915513/4855556871310000000000000000000000 : ℝ) := by norm_num
    linear_combination (40759153463/125000000000 : ℝ)*(base5) + (112891/250000000000 : ℝ)*(base15) + (4851/10000000000 : ℝ)*(base29) + (6009/12500000000 : ℝ)*(base44) + (2482079419/20000000000 : ℝ)*(base49) + (115593/1000000000000 : ℝ)*(base50) + (232077/200000000000 : ℝ)*(base59) + (29224906021/50000000000 : ℝ)*(base60) + (177257/100000 : ℝ)*(major_s1_0) + (22157118991/12500000000 : ℝ)*(major_s1_1) + (177257/100000 : ℝ)*(major_s1_2) + (2542918721469/1000000000000 : ℝ)*(sp_s1_0) + (508583557837/200000000000 : ℝ)*(sp_s1_1) + (2868991949173/1000000000000 : ℝ)*(sp_s1_2) + (673925806477/1000000000000 : ℝ)*(sp_s1_6) + (2542918721469/1000000000000 : ℝ)*(f.sum) + (12407970771205139/30521585000000000000000000000 : ℝ)*base62 + (1872436552523/1647500000000000000000000 : ℝ)*base64 + (6089750081063/46315000000000000000000000 : ℝ)*base66 + (2659763336259/6590000000000000000000000 : ℝ)*base68 + (560091265822677337/524188370000000000000000000000 : ℝ)*base70 + (284485711823119/795430000000000000000000000 : ℝ)*base73 + (8044678008881/92630000000000000000000000 : ℝ)*base74 + (285150793727541/397715000000000000000000000 : ℝ)*base76 + (1162907492942581689/7368068090000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p016_b025 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (c : Fin 88) (hlo : 58 ≤ c.val) (hhi : c.val < 64)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=58 ∨ c=59 ∨ c=60 ∨ c=61 ∨ c=62 ∨ c=63 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl
  · exact collision_c316058 p hpa (by linarith only [hpb]) X hX
  · exact collision_c316059 p hpa (by linarith only [hpb]) X hX
  · exact collision_c316060 p hpa (by linarith only [hpb]) X hX
  · exact collision_c316061 p hpa (by linarith only [hpb]) X hX
  · exact collision_c316062 p hpa (by linarith only [hpb]) X hX
  · exact (hn63 rfl).elim

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (c : Fin 88) (hlo : 58 ≤ c.val) (hhi : c.val < 64)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p016_b025 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

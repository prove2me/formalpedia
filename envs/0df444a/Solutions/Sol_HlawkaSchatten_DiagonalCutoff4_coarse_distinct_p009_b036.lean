-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p009_b036
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:01:50.475468+00:00
-- url     : https://prove2.me/submissions/651c6e22-d02a-4f5e-9fd7-4762c4356940

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309080_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309080_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309080_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c309080_s3
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c309080 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]]) : False := by
  have h0 := collision_c309080_s0 p hpa hpb X hX
  have h1 := collision_c309080_s1 p hpa hpb X hX h0
  have h2 := collision_c309080_s2 p hpa hpb X hX h1
  exact collision_c309080_s3 p hpa hpb X hX h2

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
theorem collision_support_c309079_s0_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (64544609/80000000 : ℝ)*x 0 + (-765411421/5000000000 : ℝ)*x 1 + (-1187525807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64544609/80000000 : ℝ)^35 ≤ (7570878556883/10000000000000 : ℝ)^27 := by
    have hnat : (64544609 : ℕ)^35*10000000000000^27 ≤ 7570878556883^27*80000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64544609 80000000 7570878556883 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (765411421/5000000000 : ℝ)^35 ≤ (4389259066757/50000000000000 : ℝ)^27 := by
    have hnat : (765411421 : ℕ)^35*50000000000000^27 ≤ 4389259066757^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765411421 5000000000 4389259066757 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1187525807/5000000000 : ℝ)^35 ≤ (15512696282451/100000000000000 : ℝ)^27 := by
    have hnat : (1187525807 : ℕ)^35*100000000000000^27 ≤ 15512696282451^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1187525807 5000000000 15512696282451 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(64544609/80000000 : ℝ), (-765411421/5000000000 : ℝ), (-1187525807/5000000000 : ℝ)] ![(7570878556883/10000000000000 : ℝ), (4389259066757/50000000000000 : ℝ), (15512696282451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(64544609/80000000 : ℝ)|^35 ≤ (7570878556883/10000000000000 : ℝ)^27
        have hw : |(64544609/80000000 : ℝ)|=(64544609/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-765411421/5000000000 : ℝ)|^35 ≤ (4389259066757/50000000000000 : ℝ)^27
        have hw : |(-765411421/5000000000 : ℝ)|=(765411421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1187525807/5000000000 : ℝ)|^35 ≤ (15512696282451/100000000000000 : ℝ)^27
        have hw : |(-1187525807/5000000000 : ℝ)|=(1187525807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s0_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3190286379/10000000000 : ℝ)*x 0 + (749637357/1250000000 : ℝ)*x 1 + (3507891259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3190286379/10000000000 : ℝ)^35 ≤ (22741349800873/100000000000000 : ℝ)^27 := by
    have hnat : (3190286379 : ℕ)^35*100000000000000^27 ≤ 22741349800873^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3190286379 10000000000 22741349800873 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (749637357/1250000000 : ℝ)^35 ≤ (12885047348203/25000000000000 : ℝ)^27 := by
    have hnat : (749637357 : ℕ)^35*25000000000000^27 ≤ 12885047348203^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749637357 1250000000 12885047348203 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3507891259/10000000000 : ℝ)^35 ≤ (25718460794351/100000000000000 : ℝ)^27 := by
    have hnat : (3507891259 : ℕ)^35*100000000000000^27 ≤ 25718460794351^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3507891259 10000000000 25718460794351 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3190286379/10000000000 : ℝ), (749637357/1250000000 : ℝ), (3507891259/10000000000 : ℝ)] ![(22741349800873/100000000000000 : ℝ), (12885047348203/25000000000000 : ℝ), (25718460794351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3190286379/10000000000 : ℝ)|^35 ≤ (22741349800873/100000000000000 : ℝ)^27
        have hw : |(3190286379/10000000000 : ℝ)|=(3190286379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(749637357/1250000000 : ℝ)|^35 ≤ (12885047348203/25000000000000 : ℝ)^27
        have hw : |(749637357/1250000000 : ℝ)|=(749637357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3507891259/10000000000 : ℝ)|^35 ≤ (25718460794351/100000000000000 : ℝ)^27
        have hw : |(3507891259/10000000000 : ℝ)|=(3507891259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s0_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3413185371/10000000000 : ℝ)*x 0 + (211934911/400000000 : ℝ)*x 1 + (-163205641/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3413185371/10000000000 : ℝ)^35 ≤ (24822005970173/100000000000000 : ℝ)^27 := by
    have hnat : (3413185371 : ℕ)^35*100000000000000^27 ≤ 24822005970173^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3413185371 10000000000 24822005970173 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211934911/400000000 : ℝ)^35 ≤ (21947090898177/50000000000000 : ℝ)^27 := by
    have hnat : (211934911 : ℕ)^35*50000000000000^27 ≤ 21947090898177^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211934911 400000000 21947090898177 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163205641/400000000 : ℝ)^35 ≤ (6256762442133/20000000000000 : ℝ)^27 := by
    have hnat : (163205641 : ℕ)^35*20000000000000^27 ≤ 6256762442133^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163205641 400000000 6256762442133 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3413185371/10000000000 : ℝ), (211934911/400000000 : ℝ), (-163205641/400000000 : ℝ)] ![(24822005970173/100000000000000 : ℝ), (21947090898177/50000000000000 : ℝ), (6256762442133/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3413185371/10000000000 : ℝ)|^35 ≤ (24822005970173/100000000000000 : ℝ)^27
        have hw : |(3413185371/10000000000 : ℝ)|=(3413185371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211934911/400000000 : ℝ)|^35 ≤ (21947090898177/50000000000000 : ℝ)^27
        have hw : |(211934911/400000000 : ℝ)|=(211934911/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-163205641/400000000 : ℝ)|^35 ≤ (6256762442133/20000000000000 : ℝ)^27
        have hw : |(-163205641/400000000 : ℝ)|=(163205641/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s0_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1722001923/10000000000 : ℝ)*x 0 + (2940777031/10000000000 : ℝ)*x 1 + (-18842301/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1722001923/10000000000 : ℝ)^35 ≤ (2556308331483/25000000000000 : ℝ)^27 := by
    have hnat : (1722001923 : ℕ)^35*25000000000000^27 ≤ 2556308331483^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722001923 10000000000 2556308331483 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2940777031/10000000000 : ℝ)^35 ≤ (10231501922311/50000000000000 : ℝ)^27 := by
    have hnat : (2940777031 : ℕ)^35*50000000000000^27 ≤ 10231501922311^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2940777031 10000000000 10231501922311 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18842301/25000000 : ℝ)^35 ≤ (34655881405789/50000000000000 : ℝ)^27 := by
    have hnat : (18842301 : ℕ)^35*50000000000000^27 ≤ 34655881405789^27*25000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18842301 25000000 34655881405789 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1722001923/10000000000 : ℝ), (2940777031/10000000000 : ℝ), (-18842301/25000000 : ℝ)] ![(2556308331483/25000000000000 : ℝ), (10231501922311/50000000000000 : ℝ), (34655881405789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1722001923/10000000000 : ℝ)|^35 ≤ (2556308331483/25000000000000 : ℝ)^27
        have hw : |(-1722001923/10000000000 : ℝ)|=(1722001923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2940777031/10000000000 : ℝ)|^35 ≤ (10231501922311/50000000000000 : ℝ)^27
        have hw : |(2940777031/10000000000 : ℝ)|=(2940777031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18842301/25000000 : ℝ)|^35 ≤ (34655881405789/50000000000000 : ℝ)^27
        have hw : |(-18842301/25000000 : ℝ)|=(18842301/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s0_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4022406027/5000000000 : ℝ)*x 0 + (-299619631/10000000000 : ℝ)*x 1 + (-409202913/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4022406027/5000000000 : ℝ)^35 ≤ (18856479916553/25000000000000 : ℝ)^27 := by
    have hnat : (4022406027 : ℕ)^35*25000000000000^27 ≤ 18856479916553^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022406027 5000000000 18856479916553 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299619631/10000000000 : ℝ)^35 ≤ (264925452803/25000000000000 : ℝ)^27 := by
    have hnat : (299619631 : ℕ)^35*25000000000000^27 ≤ 264925452803^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299619631 10000000000 264925452803 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (409202913/1250000000 : ℝ)^35 ≤ (23514378510511/100000000000000 : ℝ)^27 := by
    have hnat : (409202913 : ℕ)^35*100000000000000^27 ≤ 23514378510511^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409202913 1250000000 23514378510511 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4022406027/5000000000 : ℝ), (-299619631/10000000000 : ℝ), (-409202913/1250000000 : ℝ)] ![(18856479916553/25000000000000 : ℝ), (264925452803/25000000000000 : ℝ), (23514378510511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4022406027/5000000000 : ℝ)|^35 ≤ (18856479916553/25000000000000 : ℝ)^27
        have hw : |(4022406027/5000000000 : ℝ)|=(4022406027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-299619631/10000000000 : ℝ)|^35 ≤ (264925452803/25000000000000 : ℝ)^27
        have hw : |(-299619631/10000000000 : ℝ)|=(299619631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-409202913/1250000000 : ℝ)|^35 ≤ (23514378510511/100000000000000 : ℝ)^27
        have hw : |(-409202913/1250000000 : ℝ)|=(409202913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s0_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (724741791/5000000000 : ℝ)*x 0 + (981761763/1250000000 : ℝ)*x 1 + (2743909239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (724741791/5000000000 : ℝ)^35 ≤ (1635738605843/20000000000000 : ℝ)^27 := by
    have hnat : (724741791 : ℕ)^35*20000000000000^27 ≤ 1635738605843^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      724741791 5000000000 1635738605843 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (981761763/1250000000 : ℝ)^35 ≤ (3655808749511/5000000000000 : ℝ)^27 := by
    have hnat : (981761763 : ℕ)^35*5000000000000^27 ≤ 3655808749511^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981761763 1250000000 3655808749511 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2743909239/10000000000 : ℝ)^35 ≤ (9352565986121/50000000000000 : ℝ)^27 := by
    have hnat : (2743909239 : ℕ)^35*50000000000000^27 ≤ 9352565986121^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743909239 10000000000 9352565986121 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(724741791/5000000000 : ℝ), (981761763/1250000000 : ℝ), (2743909239/10000000000 : ℝ)] ![(1635738605843/20000000000000 : ℝ), (3655808749511/5000000000000 : ℝ), (9352565986121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(724741791/5000000000 : ℝ)|^35 ≤ (1635738605843/20000000000000 : ℝ)^27
        have hw : |(724741791/5000000000 : ℝ)|=(724741791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(981761763/1250000000 : ℝ)|^35 ≤ (3655808749511/5000000000000 : ℝ)^27
        have hw : |(981761763/1250000000 : ℝ)|=(981761763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2743909239/10000000000 : ℝ)|^35 ≤ (9352565986121/50000000000000 : ℝ)^27
        have hw : |(2743909239/10000000000 : ℝ)|=(2743909239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s0_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (593545917/2500000000 : ℝ)*x 0 + (3804313319/5000000000 : ℝ)*x 1 + (-139608219/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (593545917/2500000000 : ℝ)^35 ≤ (3876336992101/25000000000000 : ℝ)^27 := by
    have hnat : (593545917 : ℕ)^35*25000000000000^27 ≤ 3876336992101^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593545917 2500000000 3876336992101 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3804313319/5000000000 : ℝ)^35 ≤ (70167784118149/100000000000000 : ℝ)^27 := by
    have hnat : (3804313319 : ℕ)^35*100000000000000^27 ≤ 70167784118149^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3804313319 5000000000 70167784118149 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139608219/625000000 : ℝ)^35 ≤ (14326867904963/100000000000000 : ℝ)^27 := by
    have hnat : (139608219 : ℕ)^35*100000000000000^27 ≤ 14326867904963^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139608219 625000000 14326867904963 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(593545917/2500000000 : ℝ), (3804313319/5000000000 : ℝ), (-139608219/625000000 : ℝ)] ![(3876336992101/25000000000000 : ℝ), (70167784118149/100000000000000 : ℝ), (14326867904963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(593545917/2500000000 : ℝ)|^35 ≤ (3876336992101/25000000000000 : ℝ)^27
        have hw : |(593545917/2500000000 : ℝ)|=(593545917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3804313319/5000000000 : ℝ)|^35 ≤ (70167784118149/100000000000000 : ℝ)^27
        have hw : |(3804313319/5000000000 : ℝ)|=(3804313319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-139608219/625000000 : ℝ)|^35 ≤ (14326867904963/100000000000000 : ℝ)^27
        have hw : |(-139608219/625000000 : ℝ)|=(139608219/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s0_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-304657123/10000000000 : ℝ)*x 0 + (3569072377/10000000000 : ℝ)*x 1 + (-7812591269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (304657123/10000000000 : ℝ)^35 ≤ (1082854862587/100000000000000 : ℝ)^27 := by
    have hnat : (304657123 : ℕ)^35*100000000000000^27 ≤ 1082854862587^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304657123 10000000000 1082854862587 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3569072377/10000000000 : ℝ)^35 ≤ (26301418033663/100000000000000 : ℝ)^27 := by
    have hnat : (3569072377 : ℕ)^35*100000000000000^27 ≤ 26301418033663^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3569072377 10000000000 26301418033663 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7812591269/10000000000 : ℝ)^35 ≤ (14523145419631/20000000000000 : ℝ)^27 := by
    have hnat : (7812591269 : ℕ)^35*20000000000000^27 ≤ 14523145419631^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7812591269 10000000000 14523145419631 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-304657123/10000000000 : ℝ), (3569072377/10000000000 : ℝ), (-7812591269/10000000000 : ℝ)] ![(1082854862587/100000000000000 : ℝ), (26301418033663/100000000000000 : ℝ), (14523145419631/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-304657123/10000000000 : ℝ)|^35 ≤ (1082854862587/100000000000000 : ℝ)^27
        have hw : |(-304657123/10000000000 : ℝ)|=(304657123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3569072377/10000000000 : ℝ)|^35 ≤ (26301418033663/100000000000000 : ℝ)^27
        have hw : |(3569072377/10000000000 : ℝ)|=(3569072377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7812591269/10000000000 : ℝ)|^35 ≤ (14523145419631/20000000000000 : ℝ)^27
        have hw : |(-7812591269/10000000000 : ℝ)|=(7812591269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s0_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4612818349/5000000000 : ℝ)*x 0 + (-308927371/2500000000 : ℝ)*x 1 + (-357332103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4612818349/5000000000 : ℝ)^35 ≤ (5629954866089/6250000000000 : ℝ)^27 := by
    have hnat : (4612818349 : ℕ)^35*6250000000000^27 ≤ 5629954866089^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4612818349 5000000000 5629954866089 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (308927371/2500000000 : ℝ)^35 ≤ (1330100822963/20000000000000 : ℝ)^27 := by
    have hnat : (308927371 : ℕ)^35*20000000000000^27 ≤ 1330100822963^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      308927371 2500000000 1330100822963 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (357332103/5000000000 : ℝ)^35 ≤ (3270218016309/100000000000000 : ℝ)^27 := by
    have hnat : (357332103 : ℕ)^35*100000000000000^27 ≤ 3270218016309^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357332103 5000000000 3270218016309 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4612818349/5000000000 : ℝ), (-308927371/2500000000 : ℝ), (-357332103/5000000000 : ℝ)] ![(5629954866089/6250000000000 : ℝ), (1330100822963/20000000000000 : ℝ), (3270218016309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4612818349/5000000000 : ℝ)|^35 ≤ (5629954866089/6250000000000 : ℝ)^27
        have hw : |(4612818349/5000000000 : ℝ)|=(4612818349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-308927371/2500000000 : ℝ)|^35 ≤ (1330100822963/20000000000000 : ℝ)^27
        have hw : |(-308927371/2500000000 : ℝ)|=(308927371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-357332103/5000000000 : ℝ)|^35 ≤ (3270218016309/100000000000000 : ℝ)^27
        have hw : |(-357332103/5000000000 : ℝ)|=(357332103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s0_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1925220351/5000000000 : ℝ)*x 0 + (2929285041/5000000000 : ℝ)*x 1 + (149883829/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1925220351/5000000000 : ℝ)^35 ≤ (5804017504159/20000000000000 : ℝ)^27 := by
    have hnat : (1925220351 : ℕ)^35*20000000000000^27 ≤ 5804017504159^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925220351 5000000000 5804017504159 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2929285041/5000000000 : ℝ)^35 ≤ (50002204192853/100000000000000 : ℝ)^27 := by
    have hnat : (2929285041 : ℕ)^35*100000000000000^27 ≤ 50002204192853^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2929285041 5000000000 50002204192853 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149883829/500000000 : ℝ)^35 ≤ (20977708271053/100000000000000 : ℝ)^27 := by
    have hnat : (149883829 : ℕ)^35*100000000000000^27 ≤ 20977708271053^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149883829 500000000 20977708271053 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1925220351/5000000000 : ℝ), (2929285041/5000000000 : ℝ), (149883829/500000000 : ℝ)] ![(5804017504159/20000000000000 : ℝ), (50002204192853/100000000000000 : ℝ), (20977708271053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1925220351/5000000000 : ℝ)|^35 ≤ (5804017504159/20000000000000 : ℝ)^27
        have hw : |(1925220351/5000000000 : ℝ)|=(1925220351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2929285041/5000000000 : ℝ)|^35 ≤ (50002204192853/100000000000000 : ℝ)^27
        have hw : |(2929285041/5000000000 : ℝ)|=(2929285041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(149883829/500000000 : ℝ)|^35 ≤ (20977708271053/100000000000000 : ℝ)^27
        have hw : |(149883829/500000000 : ℝ)|=(149883829/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s0_17 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2499999987/2500000000 : ℝ)*x 0 + (2471/5000000000 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2499999987/2500000000 : ℝ)^35 ≤ (49999999662963/50000000000000 : ℝ)^27 := by
    have hnat : (2499999987 : ℕ)^35*50000000000000^27 ≤ 49999999662963^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2499999987 2500000000 49999999662963 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2471/5000000000 : ℝ)^35 ≤ (334503/50000000000000 : ℝ)^27 := by
    have hnat : (2471 : ℕ)^35*50000000000000^27 ≤ 334503^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2471 5000000000 334503 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^35 ≤ (0 : ℝ)^27 := by
    have hnat : (0 : ℕ)^35*1^27 ≤ 0^27*1^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2499999987/2500000000 : ℝ), (2471/5000000000 : ℝ), (0 : ℝ)] ![(49999999662963/50000000000000 : ℝ), (334503/50000000000000 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2499999987/2500000000 : ℝ)|^35 ≤ (49999999662963/50000000000000 : ℝ)^27
        have hw : |(2499999987/2500000000 : ℝ)|=(2499999987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2471/5000000000 : ℝ)|^35 ≤ (334503/50000000000000 : ℝ)^27
        have hw : |(2471/5000000000 : ℝ)|=(2471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^35 ≤ (0 : ℝ)^27
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s0_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (522658751/2000000000 : ℝ)*x 0 + (3251036441/10000000000 : ℝ)*x 1 + (-416757441/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522658751/2000000000 : ℝ)^35 ≤ (877957041279/5000000000000 : ℝ)^27 := by
    have hnat : (522658751 : ℕ)^35*5000000000000^27 ≤ 877957041279^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522658751 2000000000 877957041279 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3251036441/10000000000 : ℝ)^35 ≤ (5826070344203/25000000000000 : ℝ)^27 := by
    have hnat : (3251036441 : ℕ)^35*25000000000000^27 ≤ 5826070344203^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3251036441 10000000000 5826070344203 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416757441/625000000 : ℝ)^35 ≤ (29568288890523/50000000000000 : ℝ)^27 := by
    have hnat : (416757441 : ℕ)^35*50000000000000^27 ≤ 29568288890523^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416757441 625000000 29568288890523 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522658751/2000000000 : ℝ), (3251036441/10000000000 : ℝ), (-416757441/625000000 : ℝ)] ![(877957041279/5000000000000 : ℝ), (5826070344203/25000000000000 : ℝ), (29568288890523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522658751/2000000000 : ℝ)|^35 ≤ (877957041279/5000000000000 : ℝ)^27
        have hw : |(522658751/2000000000 : ℝ)|=(522658751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3251036441/10000000000 : ℝ)|^35 ≤ (5826070344203/25000000000000 : ℝ)^27
        have hw : |(3251036441/10000000000 : ℝ)|=(3251036441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-416757441/625000000 : ℝ)|^35 ≤ (29568288890523/50000000000000 : ℝ)^27
        have hw : |(-416757441/625000000 : ℝ)|=(416757441/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s0_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-110190323/2500000000 : ℝ)*x 0 + (2835037229/5000000000 : ℝ)*x 1 + (-58877669/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110190323/2500000000 : ℝ)^35 ≤ (873888360081/50000000000000 : ℝ)^27 := by
    have hnat : (110190323 : ℕ)^35*50000000000000^27 ≤ 873888360081^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110190323 2500000000 873888360081 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2835037229/5000000000 : ℝ)^35 ≤ (11981688744051/25000000000000 : ℝ)^27 := by
    have hnat : (2835037229 : ℕ)^35*25000000000000^27 ≤ 11981688744051^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2835037229 5000000000 11981688744051 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (58877669/100000000 : ℝ)^35 ≤ (2013018731677/4000000000000 : ℝ)^27 := by
    have hnat : (58877669 : ℕ)^35*4000000000000^27 ≤ 2013018731677^27*100000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58877669 100000000 2013018731677 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-110190323/2500000000 : ℝ), (2835037229/5000000000 : ℝ), (-58877669/100000000 : ℝ)] ![(873888360081/50000000000000 : ℝ), (11981688744051/25000000000000 : ℝ), (2013018731677/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-110190323/2500000000 : ℝ)|^35 ≤ (873888360081/50000000000000 : ℝ)^27
        have hw : |(-110190323/2500000000 : ℝ)|=(110190323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2835037229/5000000000 : ℝ)|^35 ≤ (11981688744051/25000000000000 : ℝ)^27
        have hw : |(2835037229/5000000000 : ℝ)|=(2835037229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-58877669/100000000 : ℝ)|^35 ≤ (2013018731677/4000000000000 : ℝ)^27
        have hw : |(-58877669/100000000 : ℝ)|=(58877669/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s0_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (9604680291/10000000000 : ℝ)*x 0 + (-86864659/2500000000 : ℝ)*x 1 + (-402041499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9604680291/10000000000 : ℝ)^35 ≤ (47452890258081/50000000000000 : ℝ)^27 := by
    have hnat : (9604680291 : ℕ)^35*50000000000000^27 ≤ 47452890258081^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9604680291 10000000000 47452890258081 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86864659/2500000000 : ℝ)^35 ≤ (256807735781/20000000000000 : ℝ)^27 := by
    have hnat : (86864659 : ℕ)^35*20000000000000^27 ≤ 256807735781^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86864659 2500000000 256807735781 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (402041499/5000000000 : ℝ)^35 ≤ (476272599967/12500000000000 : ℝ)^27 := by
    have hnat : (402041499 : ℕ)^35*12500000000000^27 ≤ 476272599967^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402041499 5000000000 476272599967 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9604680291/10000000000 : ℝ), (-86864659/2500000000 : ℝ), (-402041499/5000000000 : ℝ)] ![(47452890258081/50000000000000 : ℝ), (256807735781/20000000000000 : ℝ), (476272599967/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9604680291/10000000000 : ℝ)|^35 ≤ (47452890258081/50000000000000 : ℝ)^27
        have hw : |(9604680291/10000000000 : ℝ)|=(9604680291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-86864659/2500000000 : ℝ)|^35 ≤ (256807735781/20000000000000 : ℝ)^27
        have hw : |(-86864659/2500000000 : ℝ)|=(86864659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-402041499/5000000000 : ℝ)|^35 ≤ (476272599967/12500000000000 : ℝ)^27
        have hw : |(-402041499/5000000000 : ℝ)|=(402041499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s0_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2573372609/10000000000 : ℝ)*x 0 + (6097140207/10000000000 : ℝ)*x 1 + (3963589753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2573372609/10000000000 : ℝ)^35 ≤ (8606108240611/50000000000000 : ℝ)^27 := by
    have hnat : (2573372609 : ℕ)^35*50000000000000^27 ≤ 8606108240611^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2573372609 10000000000 8606108240611 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6097140207/10000000000 : ℝ)^35 ≤ (658218187849/1250000000000 : ℝ)^27 := by
    have hnat : (6097140207 : ℕ)^35*1250000000000^27 ≤ 658218187849^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6097140207 10000000000 658218187849 1250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3963589753/10000000000 : ℝ)^35 ≤ (15065164242517/50000000000000 : ℝ)^27 := by
    have hnat : (3963589753 : ℕ)^35*50000000000000^27 ≤ 15065164242517^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3963589753 10000000000 15065164242517 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2573372609/10000000000 : ℝ), (6097140207/10000000000 : ℝ), (3963589753/10000000000 : ℝ)] ![(8606108240611/50000000000000 : ℝ), (658218187849/1250000000000 : ℝ), (15065164242517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2573372609/10000000000 : ℝ)|^35 ≤ (8606108240611/50000000000000 : ℝ)^27
        have hw : |(2573372609/10000000000 : ℝ)|=(2573372609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6097140207/10000000000 : ℝ)|^35 ≤ (658218187849/1250000000000 : ℝ)^27
        have hw : |(6097140207/10000000000 : ℝ)|=(6097140207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3963589753/10000000000 : ℝ)|^35 ≤ (15065164242517/50000000000000 : ℝ)^27
        have hw : |(3963589753/10000000000 : ℝ)|=(3963589753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s0_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2139023017/5000000000 : ℝ)*x 0 + (1344891847/2500000000 : ℝ)*x 1 + (-12424661/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139023017/5000000000 : ℝ)^35 ≤ (16632397337127/50000000000000 : ℝ)^27 := by
    have hnat : (2139023017 : ℕ)^35*50000000000000^27 ≤ 16632397337127^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139023017 5000000000 16632397337127 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344891847/2500000000 : ℝ)^35 ≤ (8953622616301/20000000000000 : ℝ)^27 := by
    have hnat : (1344891847 : ℕ)^35*20000000000000^27 ≤ 8953622616301^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344891847 2500000000 8953622616301 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12424661/40000000 : ℝ)^35 ≤ (5491773059137/25000000000000 : ℝ)^27 := by
    have hnat : (12424661 : ℕ)^35*25000000000000^27 ≤ 5491773059137^27*40000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12424661 40000000 5491773059137 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2139023017/5000000000 : ℝ), (1344891847/2500000000 : ℝ), (-12424661/40000000 : ℝ)] ![(16632397337127/50000000000000 : ℝ), (8953622616301/20000000000000 : ℝ), (5491773059137/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2139023017/5000000000 : ℝ)|^35 ≤ (16632397337127/50000000000000 : ℝ)^27
        have hw : |(2139023017/5000000000 : ℝ)|=(2139023017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344891847/2500000000 : ℝ)|^35 ≤ (8953622616301/20000000000000 : ℝ)^27
        have hw : |(1344891847/2500000000 : ℝ)|=(1344891847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12424661/40000000 : ℝ)|^35 ≤ (5491773059137/25000000000000 : ℝ)^27
        have hw : |(-12424661/40000000 : ℝ)|=(12424661/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s1_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1328797273/5000000000 : ℝ)*x 0 + (4425560663/10000000000 : ℝ)*x 1 + (-5612312643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328797273/5000000000 : ℝ)^35 ≤ (3589193395199/20000000000000 : ℝ)^27 := by
    have hnat : (1328797273 : ℕ)^35*20000000000000^27 ≤ 3589193395199^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328797273 5000000000 3589193395199 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4425560663/10000000000 : ℝ)^35 ≤ (34759219510221/100000000000000 : ℝ)^27 := by
    have hnat : (4425560663 : ℕ)^35*100000000000000^27 ≤ 34759219510221^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4425560663 10000000000 34759219510221 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5612312643/10000000000 : ℝ)^35 ≤ (47294813494367/100000000000000 : ℝ)^27 := by
    have hnat : (5612312643 : ℕ)^35*100000000000000^27 ≤ 47294813494367^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5612312643 10000000000 47294813494367 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1328797273/5000000000 : ℝ), (4425560663/10000000000 : ℝ), (-5612312643/10000000000 : ℝ)] ![(3589193395199/20000000000000 : ℝ), (34759219510221/100000000000000 : ℝ), (47294813494367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1328797273/5000000000 : ℝ)|^35 ≤ (3589193395199/20000000000000 : ℝ)^27
        have hw : |(-1328797273/5000000000 : ℝ)|=(1328797273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4425560663/10000000000 : ℝ)|^35 ≤ (34759219510221/100000000000000 : ℝ)^27
        have hw : |(4425560663/10000000000 : ℝ)|=(4425560663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5612312643/10000000000 : ℝ)|^35 ≤ (47294813494367/100000000000000 : ℝ)^27
        have hw : |(-5612312643/10000000000 : ℝ)|=(5612312643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s1_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6439192529/10000000000 : ℝ)*x 0 + (-56456939/200000000 : ℝ)*x 1 + (-3333785827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6439192529/10000000000 : ℝ)^35 ≤ (28259135367573/50000000000000 : ℝ)^27 := by
    have hnat : (6439192529 : ℕ)^35*50000000000000^27 ≤ 28259135367573^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6439192529 10000000000 28259135367573 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56456939/200000000 : ℝ)^35 ≤ (1940564235329/10000000000000 : ℝ)^27 := by
    have hnat : (56456939 : ℕ)^35*10000000000000^27 ≤ 1940564235329^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56456939 200000000 1940564235329 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3333785827/10000000000 : ℝ)^35 ≤ (12038043448267/50000000000000 : ℝ)^27 := by
    have hnat : (3333785827 : ℕ)^35*50000000000000^27 ≤ 12038043448267^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3333785827 10000000000 12038043448267 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6439192529/10000000000 : ℝ), (-56456939/200000000 : ℝ), (-3333785827/10000000000 : ℝ)] ![(28259135367573/50000000000000 : ℝ), (1940564235329/10000000000000 : ℝ), (12038043448267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6439192529/10000000000 : ℝ)|^35 ≤ (28259135367573/50000000000000 : ℝ)^27
        have hw : |(6439192529/10000000000 : ℝ)|=(6439192529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-56456939/200000000 : ℝ)|^35 ≤ (1940564235329/10000000000000 : ℝ)^27
        have hw : |(-56456939/200000000 : ℝ)|=(56456939/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3333785827/10000000000 : ℝ)|^35 ≤ (12038043448267/50000000000000 : ℝ)^27
        have hw : |(-3333785827/10000000000 : ℝ)|=(3333785827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s1_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3828986237/10000000000 : ℝ)*x 0 + (5179296739/10000000000 : ℝ)*x 1 + (3804254873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3828986237/10000000000 : ℝ)^35 ≤ (5762130323829/20000000000000 : ℝ)^27 := by
    have hnat : (3828986237 : ℕ)^35*20000000000000^27 ≤ 5762130323829^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3828986237 10000000000 5762130323829 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5179296739/10000000000 : ℝ)^35 ≤ (2130984509279/5000000000000 : ℝ)^27 := by
    have hnat : (5179296739 : ℕ)^35*5000000000000^27 ≤ 2130984509279^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179296739 10000000000 2130984509279 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3804254873/10000000000 : ℝ)^35 ≤ (28569658177541/100000000000000 : ℝ)^27 := by
    have hnat : (3804254873 : ℕ)^35*100000000000000^27 ≤ 28569658177541^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3804254873 10000000000 28569658177541 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3828986237/10000000000 : ℝ), (5179296739/10000000000 : ℝ), (3804254873/10000000000 : ℝ)] ![(5762130323829/20000000000000 : ℝ), (2130984509279/5000000000000 : ℝ), (28569658177541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3828986237/10000000000 : ℝ)|^35 ≤ (5762130323829/20000000000000 : ℝ)^27
        have hw : |(3828986237/10000000000 : ℝ)|=(3828986237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5179296739/10000000000 : ℝ)|^35 ≤ (2130984509279/5000000000000 : ℝ)^27
        have hw : |(5179296739/10000000000 : ℝ)|=(5179296739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3804254873/10000000000 : ℝ)|^35 ≤ (28569658177541/100000000000000 : ℝ)^27
        have hw : |(3804254873/10000000000 : ℝ)|=(3804254873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309079_s1_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3790617397/10000000000 : ℝ)*x 0 + (4871814807/10000000000 : ℝ)*x 1 + (-2085708319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3790617397/10000000000 : ℝ)^35 ≤ (3554620845633/12500000000000 : ℝ)^27 := by
    have hnat : (3790617397 : ℕ)^35*12500000000000^27 ≤ 3554620845633^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3790617397 10000000000 3554620845633 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4871814807/10000000000 : ℝ)^35 ≤ (19684514488281/50000000000000 : ℝ)^27 := by
    have hnat : (4871814807 : ℕ)^35*50000000000000^27 ≤ 19684514488281^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4871814807 10000000000 19684514488281 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085708319/5000000000 : ℝ)^35 ≤ (32194004237527/100000000000000 : ℝ)^27 := by
    have hnat : (2085708319 : ℕ)^35*100000000000000^27 ≤ 32194004237527^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085708319 5000000000 32194004237527 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3790617397/10000000000 : ℝ), (4871814807/10000000000 : ℝ), (-2085708319/5000000000 : ℝ)] ![(3554620845633/12500000000000 : ℝ), (19684514488281/50000000000000 : ℝ), (32194004237527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3790617397/10000000000 : ℝ)|^35 ≤ (3554620845633/12500000000000 : ℝ)^27
        have hw : |(3790617397/10000000000 : ℝ)|=(3790617397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4871814807/10000000000 : ℝ)|^35 ≤ (19684514488281/50000000000000 : ℝ)^27
        have hw : |(4871814807/10000000000 : ℝ)|=(4871814807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2085708319/5000000000 : ℝ)|^35 ≤ (32194004237527/100000000000000 : ℝ)^27
        have hw : |(-2085708319/5000000000 : ℝ)|=(2085708319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309079 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (69/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^69 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^69*1^16 ≤ 1^16*1^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5871837947492399/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5871837947492399/5000000000000000 : ℝ)^69 := by
      have hnat : (2 : ℕ)^16*5000000000000000^69 ≤ 5871837947492399^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5871837947492399 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5871837947492399/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12901399174522839/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12901399174522839/10000000000000000 : ℝ)^69 := by
      have hnat : (3 : ℕ)^16*10000000000000000^69 ≤ 12901399174522839^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12901399174522839 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12901399174522839/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (69/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^69 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^69*1^16 ≤ 1^16*1^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5871837947492399/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5871837947492399/5000000000000000 : ℝ)^69 := by
      have hnat : (2 : ℕ)^16*5000000000000000^69 ≤ 5871837947492399^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5871837947492399 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5871837947492399/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12901399174522839/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12901399174522839/10000000000000000 : ℝ)^69 := by
      have hnat : (3 : ℕ)^16*10000000000000000^69 ≤ 12901399174522839^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12901399174522839 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12901399174522839/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(871837947492399/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1157723279538041/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(871837947492399/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1157723279538041/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (69/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^69 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^69*1^16 ≤ 1^16*1^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5871837947492399/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5871837947492399/5000000000000000 : ℝ)^69 := by
      have hnat : (2 : ℕ)^16*5000000000000000^69 ≤ 5871837947492399^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5871837947492399 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5871837947492399/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12901399174522839/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12901399174522839/10000000000000000 : ℝ)^69 := by
      have hnat : (3 : ℕ)^16*10000000000000000^69 ≤ 12901399174522839^69*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12901399174522839 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12901399174522839/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (871837947492399/5000000000000000 : ℝ)) (beta := (1157723279538041/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(871837947492399/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1157723279538041/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((64544609/80000000 : ℝ)*X 1 0+(-765411421/5000000000 : ℝ)*X 1 1+(-1187525807/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3190286379/10000000000 : ℝ)*X 2 0+(749637357/1250000000 : ℝ)*X 2 1+(3507891259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((3413185371/10000000000 : ℝ)*X 0 0+(211934911/400000000 : ℝ)*X 0 1+(-163205641/400000000 : ℝ)*X 0 2+(3413185371/10000000000 : ℝ)*X 1 0+(211934911/400000000 : ℝ)*X 1 1+(-163205641/400000000 : ℝ)*X 1 2+(3413185371/10000000000 : ℝ)*X 2 0+(211934911/400000000 : ℝ)*X 2 1+(-163205641/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1722001923/10000000000 : ℝ)*X 0 0+(2940777031/10000000000 : ℝ)*X 0 1+(-18842301/25000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4022406027/5000000000 : ℝ)*X 1 0+(-299619631/10000000000 : ℝ)*X 1 1+(-409202913/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((724741791/5000000000 : ℝ)*X 2 0+(981761763/1250000000 : ℝ)*X 2 1+(2743909239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((593545917/2500000000 : ℝ)*X 0 0+(3804313319/5000000000 : ℝ)*X 0 1+(-139608219/625000000 : ℝ)*X 0 2+(593545917/2500000000 : ℝ)*X 1 0+(3804313319/5000000000 : ℝ)*X 1 1+(-139608219/625000000 : ℝ)*X 1 2+(593545917/2500000000 : ℝ)*X 2 0+(3804313319/5000000000 : ℝ)*X 2 1+(-139608219/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-304657123/10000000000 : ℝ)*X 0 0+(3569072377/10000000000 : ℝ)*X 0 1+(-7812591269/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4612818349/5000000000 : ℝ)*X 1 0+(-308927371/2500000000 : ℝ)*X 1 1+(-357332103/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1925220351/5000000000 : ℝ)*X 2 0+(2929285041/5000000000 : ℝ)*X 2 1+(149883829/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_17 : ((2499999987/2500000000 : ℝ)*X 1 0+(2471/5000000000 : ℝ)*X 1 1+(2499999987/2500000000 : ℝ)*X 2 0+(2471/5000000000 : ℝ)*X 2 1+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s0_17 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((522658751/2000000000 : ℝ)*X 0 0+(3251036441/10000000000 : ℝ)*X 0 1+(-416757441/625000000 : ℝ)*X 0 2+(522658751/2000000000 : ℝ)*X 1 0+(3251036441/10000000000 : ℝ)*X 1 1+(-416757441/625000000 : ℝ)*X 1 2+(522658751/2000000000 : ℝ)*X 2 0+(3251036441/10000000000 : ℝ)*X 2 1+(-416757441/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-110190323/2500000000 : ℝ)*X 0 0+(2835037229/5000000000 : ℝ)*X 0 1+(-58877669/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((9604680291/10000000000 : ℝ)*X 1 0+(-86864659/2500000000 : ℝ)*X 1 1+(-402041499/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((2573372609/10000000000 : ℝ)*X 2 0+(6097140207/10000000000 : ℝ)*X 2 1+(3963589753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((2139023017/5000000000 : ℝ)*X 0 0+(1344891847/2500000000 : ℝ)*X 0 1+(-12424661/40000000 : ℝ)*X 0 2+(2139023017/5000000000 : ℝ)*X 1 0+(1344891847/2500000000 : ℝ)*X 1 1+(-12424661/40000000 : ℝ)*X 1 2+(2139023017/5000000000 : ℝ)*X 2 0+(1344891847/2500000000 : ℝ)*X 2 1+(-12424661/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((2047/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2047/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (66332756804077985539461/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (386844434371/500000000000 : ℝ)*(base39) + (124748371069/125000000000 : ℝ)*(base49) + (293329/40000000000 : ℝ)*(base53) + (9615976009/15625000000 : ℝ)*(base60) + (2624429520509/1000000000000 : ℝ)*(major_s0_0) + (2624429520509/1000000000000 : ℝ)*(major_s0_1) + (656105546821/250000000000 : ℝ)*(major_s0_2) + (5910391/250000000000 : ℝ)*(sp_s0_1) + (1041179/200000000000 : ℝ)*(sp_s0_6) + (3600795193519/1000000000000 : ℝ)*(sp_s0_7) + (3600799178577/1000000000000 : ℝ)*(sp_s0_8) + (1800415076683/500000000000 : ℝ)*(sp_s0_9) + (412004814891/250000000000 : ℝ)*(sp_s0_13) + (27626623/1000000000000 : ℝ)*(sp_s0_14) + (824012232729/500000000000 : ℝ)*(f.failure) + (1800415076683/500000000000 : ℝ)*(f.sum) + (4340099697274237/10000000000000000000000000000 : ℝ)*base62 + (978198221867661/2500000000000000000000000000 : ℝ)*base65 + (1753617916888909/5000000000000000000000000000 : ℝ)*base67 + (227132954238579/1250000000000000000000000000 : ℝ)*base69 + (698825403346413/5000000000000000000000000000 : ℝ)*base71 + (1209801990182869/10000000000000000000000000000 : ℝ)*base73 + (4354487535817131/10000000000000000000000000000 : ℝ)*base75 + (1357162231611091/5000000000000000000000000000 : ℝ)*base77 + (3940157827960687/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (54937/50000000000000000 : ℝ)*base86 + (54937/50000000000000000 : ℝ)*base88 + (54937/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((5261/10000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(5261/10000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15382669184224113521409/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (290439491641/250000000000 : ℝ)*(base39) + (37906628253/62500000000 : ℝ)*(base49) + (807929344379/1000000000000 : ℝ)*(base60) + (1580872608459/500000000000 : ℝ)*(major_s0_0) + (3161733199517/1000000000000 : ℝ)*(major_s0_1) + (3161733199517/1000000000000 : ℝ)*(major_s0_2) + (2680613/250000000000 : ℝ)*(sp_s0_1) + (4476897/200000000000 : ℝ)*(sp_s0_7) + (216900739861/50000000000 : ℝ)*(sp_s0_14) + (4337983240757/1000000000000 : ℝ)*(sp_s0_15) + (2169018590853/500000000000 : ℝ)*(sp_s0_16) + (12017401/1000000000000 : ℝ)*(sp_s0_17) + (19854271663/10000000000 : ℝ)*(sp_s0_20) + (675289/15625000000 : ℝ)*(sp_s0_22) + (19854271663/10000000000 : ℝ)*(f.failure) + (2169018590853/500000000000 : ℝ)*(f.sum) + (8618167813383631/10000000000000000000000000000 : ℝ)*base62 + (1960254369326197/10000000000000000000000000000 : ℝ)*base65 + (212697817971283/5000000000000000000000000000 : ℝ)*base66 + (13349127028717/5000000000000000000000000000 : ℝ)*base68 + (1059574852738761/10000000000000000000000000000 : ℝ)*base71 + (401208827888819/5000000000000000000000000000 : ℝ)*base73 + (7788297904326197/10000000000000000000000000000 : ℝ)*base74 + (1257128277896859/2500000000000000000000000000 : ℝ)*base76 + (17214295596327/156250000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (761/1000000000000000 : ℝ)*base87 + (761/1000000000000000 : ℝ)*base89 + (761/1000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2601/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2601/6250 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (36192100557329420636091/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6219483/1000000000000 : ℝ)*(base11) + (494276326637/500000000000 : ℝ)*(base39) + (637030876741/1000000000000 : ℝ)*(base49) + (1471551/500000000000 : ℝ)*(base50) + (1213363399377/500000000000 : ℝ)*(major_s0_0) + (1213363399377/500000000000 : ℝ)*(major_s0_1) + (1213363399377/500000000000 : ℝ)*(major_s0_2) + (153740453/1000000000000 : ℝ)*(sp_s0_2) + (19457/800000000 : ℝ)*(sp_s0_9) + (368061/200000000000 : ℝ)*(sp_s0_15) + (665913312361/200000000000 : ℝ)*(sp_s0_21) + (416196367623/125000000000 : ℝ)*(sp_s0_22) + (665878943917/200000000000 : ℝ)*(sp_s0_23) + (761937995301/500000000000 : ℝ)*(sp_s0_27) + (761937995301/500000000000 : ℝ)*(f.failure) + (416196597661/125000000000 : ℝ)*(f.sum) + (3447747133529611/5000000000000000000000000000 : ℝ)*base62 + (3104971814200457/5000000000000000000000000000 : ℝ)*base65 + (358124758835423/2500000000000000000000000000 : ℝ)*base66 + (606274416664577/2500000000000000000000000000 : ℝ)*base68 + (236322398871303/5000000000000000000000000000 : ℝ)*base71 + (3100549371799543/5000000000000000000000000000 : ℝ)*base72 + (1995317407200457/5000000000000000000000000000 : ℝ)*base74 + (1508265149085423/2500000000000000000000000000 : ℝ)*base77 + (305043611470389/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1653/50000000000000000 : ℝ)*base86 + (1653/50000000000000000 : ℝ)*base88 + (1653/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (2047/5000 : ℝ) ^ (69/16 : ℝ) ≤ (531285008559375513/25000000000000000000 : ℝ) := by
    have hpowers : (2047/5000 : ℝ)^69 ≤ (531285008559375513/25000000000000000000 : ℝ)^16 := by
      have hnat : (2047 : ℕ)^69*25000000000000000000^16 ≤ 531285008559375513^16*5000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2047 5000 531285008559375513 25000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2047/5000 : ℝ)) (X := (531285008559375513/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (25531285008559375513/25000000000000000000 : ℝ) ≤ (5024440686732367/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (25531285008559375513/25000000000000000000 : ℝ)^16 ≤ (5024440686732367/5000000000000000 : ℝ)^69 := by
      have hnat : (25531285008559375513 : ℕ)^16*5000000000000000^69 ≤ 5024440686732367^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25531285008559375513 25000000000000000000 5024440686732367 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5024440686732367/5000000000000000 : ℝ)) (X := (25531285008559375513/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (13031285008559375513/12500000000000000000 : ℝ) ≤ (5048493784069977/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (13031285008559375513/12500000000000000000 : ℝ)^16 ≤ (5048493784069977/5000000000000000 : ℝ)^69 := by
      have hnat : (13031285008559375513 : ℕ)^16*5000000000000000^69 ≤ 5048493784069977^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13031285008559375513 12500000000000000000 5048493784069977 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5048493784069977/5000000000000000 : ℝ)) (X := (13031285008559375513/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(24440686732367/2047000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(2405309733761/204700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (2047/5000 : ℝ)) (alpha := (24440686732367/2047000000000000 : ℝ)) (beta := (2405309733761/204700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2047/5000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(24440686732367/2047000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(2405309733761/204700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (5261/10000 : ℝ) ^ (69/16 : ℝ) ≤ (3133841705065884533/50000000000000000000 : ℝ) := by
    have hpowers : (5261/10000 : ℝ)^69 ≤ (3133841705065884533/50000000000000000000 : ℝ)^16 := by
      have hnat : (5261 : ℕ)^69*50000000000000000000^16 ≤ 3133841705065884533^16*10000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5261 10000 3133841705065884533 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5261/10000 : ℝ)) (X := (3133841705065884533/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (53133841705065884533/50000000000000000000 : ℝ) ≤ (10141962968374317/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (53133841705065884533/50000000000000000000 : ℝ)^16 ≤ (10141962968374317/10000000000000000 : ℝ)^69 := by
      have hnat : (53133841705065884533 : ℕ)^16*10000000000000000^69 ≤ 10141962968374317^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53133841705065884533 50000000000000000000 10141962968374317 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10141962968374317/10000000000000000 : ℝ)) (X := (53133841705065884533/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (28133841705065884533/25000000000000000000 : ℝ) ≤ (5138816535989251/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (28133841705065884533/25000000000000000000 : ℝ)^16 ≤ (5138816535989251/5000000000000000 : ℝ)^69 := by
      have hnat : (28133841705065884533 : ℕ)^16*5000000000000000^69 ≤ 5138816535989251^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28133841705065884533 25000000000000000000 5138816535989251 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5138816535989251/5000000000000000 : ℝ)) (X := (28133841705065884533/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(141962968374317/5261000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(27134020720837/1052200000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (5261/10000 : ℝ)) (alpha := (141962968374317/5261000000000000 : ℝ)) (beta := (27134020720837/1052200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (5261/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(141962968374317/5261000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(27134020720837/1052200000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (2601/6250 : ℝ) ^ (69/16 : ℝ) ≤ (2280658153690644769/100000000000000000000 : ℝ) := by
    have hpowers : (2601/6250 : ℝ)^69 ≤ (2280658153690644769/100000000000000000000 : ℝ)^16 := by
      have hnat : (2601 : ℕ)^69*100000000000000000000^16 ≤ 2280658153690644769^16*6250^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2601 6250 2280658153690644769 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2601/6250 : ℝ)) (X := (2280658153690644769/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (102280658153690644769/100000000000000000000 : ℝ) ≤ (10052427735739671/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (102280658153690644769/100000000000000000000 : ℝ)^16 ≤ (10052427735739671/10000000000000000 : ℝ)^69 := by
      have hnat : (102280658153690644769 : ℕ)^16*10000000000000000^69 ≤ 10052427735739671^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102280658153690644769 100000000000000000000 10052427735739671 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10052427735739671/10000000000000000 : ℝ)) (X := (102280658153690644769/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (52280658153690644769/50000000000000000000 : ℝ) ≤ (5051982530688509/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (52280658153690644769/50000000000000000000 : ℝ)^16 ≤ (5051982530688509/5000000000000000 : ℝ)^69 := by
      have hnat : (52280658153690644769 : ℕ)^16*5000000000000000^69 ≤ 5051982530688509^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52280658153690644769 50000000000000000000 5051982530688509 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5051982530688509/5000000000000000 : ℝ)) (X := (52280658153690644769/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(52427735739671/4161600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(51537325637347/4161600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (2601/6250 : ℝ)) (alpha := (52427735739671/4161600000000000 : ℝ)) (beta := (51537325637347/4161600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (2601/6250 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(52427735739671/4161600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(51537325637347/4161600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1328797273/5000000000 : ℝ)*X 0 0+(4425560663/10000000000 : ℝ)*X 0 1+(-5612312643/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((6439192529/10000000000 : ℝ)*X 1 0+(-56456939/200000000 : ℝ)*X 1 1+(-3333785827/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3828986237/10000000000 : ℝ)*X 2 0+(5179296739/10000000000 : ℝ)*X 2 1+(3804254873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3790617397/10000000000 : ℝ)*X 0 0+(4871814807/10000000000 : ℝ)*X 0 1+(-2085708319/5000000000 : ℝ)*X 0 2+(3790617397/10000000000 : ℝ)*X 1 0+(4871814807/10000000000 : ℝ)*X 1 1+(-2085708319/5000000000 : ℝ)*X 1 2+(3790617397/10000000000 : ℝ)*X 2 0+(4871814807/10000000000 : ℝ)*X 2 1+(-2085708319/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309079_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-327741/50000 : ℝ) < ((-159247/100000 : ℝ)*P 0+(-159247/100000 : ℝ)*P 1+(-159247/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-327741/50000 : ℝ) < (-115576742673614560674360502421/17747490000000000000000000000 : ℝ) := by norm_num
    linear_combination (81491/250000000000 : ℝ)*(base12) + (1323027/1000000000000 : ℝ)*(base15) + (152123/1000000000000 : ℝ)*(base25) + (432930961433/1000000000000 : ℝ)*(base39) + (341160240551/1000000000000 : ℝ)*(base49) + (90503/500000000000 : ℝ)*(base50) + (82162923933/500000000000 : ℝ)*(base60) + (67267/500000000000 : ℝ)*(ratio_s0_0) + (159247/100000 : ℝ)*(major_s1_0) + (159247/100000 : ℝ)*(major_s1_1) + (159247/100000 : ℝ)*(major_s1_2) + (217076189963/100000000000 : ℝ)*(sp_s1_0) + (1085380451283/500000000000 : ℝ)*(sp_s1_1) + (2170762073471/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2170762225593/1000000000000 : ℝ)*(f.sum) + (99343645921927/213810328125000000000000000 : ℝ)*base63 + (1611318763619/2601000000000000000000000 : ℝ)*base64 + (2425829231549/5261000000000000000000000 : ℝ)*base67 + (10878254478343/13005000000000000000000000 : ℝ)*base69 + (204585539467543/266212350000000000000000000 : ℝ)*base70 + (531204214073/10235000000000000000000000 : ℝ)*base72 + (4943721296647/52610000000000000000000000 : ℝ)*base74 + (8354406658243/20470000000000000000000000 : ℝ)*base76 + (85600271046733861/107692670000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p009_b036 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=79 ∨ c=80 := by omega
  rcases hc with rfl|rfl
  · exact collision_c309079 p hpa (by linarith only [hpb]) X hX
  · exact collision_c309080 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 79 ≤ c.val) (hhi : c.val < 81)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p009_b036 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

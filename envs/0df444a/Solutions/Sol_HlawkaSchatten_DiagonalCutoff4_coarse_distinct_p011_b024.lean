-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p011_b024
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:58:25.178992+00:00
-- url     : https://prove2.me/submissions/c616d73d-f524-4274-ba8f-ac81f74efdcd

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310045_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310045_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310045_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c310045_s3
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c310045 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]]) : False := by
  have h0 := collision_c310045_s0 p hpa hpb X hX
  have h1 := collision_c310045_s1 p hpa hpb X hX h0
  have h2 := collision_c310045_s2 p hpa hpb X hX h1
  exact collision_c310045_s3 p hpa hpb X hX h2

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
theorem collision_support_c311043_s0_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2652535601/10000000000 : ℝ)*x 0 + (-2254533963/5000000000 : ℝ)*x 1 + (216905561/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652535601/10000000000 : ℝ)^73 ≤ (3655206445831/20000000000000 : ℝ)^57 := by
    have hnat : (2652535601 : ℕ)^73*20000000000000^57 ≤ 3655206445831^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652535601 10000000000 3655206445831 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254533963/5000000000 : ℝ)^73 ≤ (721137906867/2000000000000 : ℝ)^57 := by
    have hnat : (2254533963 : ℕ)^73*2000000000000^57 ≤ 721137906867^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254533963 5000000000 721137906867 2000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216905561/400000000 : ℝ)^73 ≤ (45667072409407/100000000000000 : ℝ)^57 := by
    have hnat : (216905561 : ℕ)^73*100000000000000^57 ≤ 45667072409407^57*400000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216905561 400000000 45667072409407 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2652535601/10000000000 : ℝ), (-2254533963/5000000000 : ℝ), (216905561/400000000 : ℝ)] ![(3655206445831/20000000000000 : ℝ), (721137906867/2000000000000 : ℝ), (45667072409407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2652535601/10000000000 : ℝ)|^73 ≤ (3655206445831/20000000000000 : ℝ)^57
        have hw : |(-2652535601/10000000000 : ℝ)|=(2652535601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2254533963/5000000000 : ℝ)|^73 ≤ (721137906867/2000000000000 : ℝ)^57
        have hw : |(-2254533963/5000000000 : ℝ)|=(2254533963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216905561/400000000 : ℝ)|^73 ≤ (45667072409407/100000000000000 : ℝ)^57
        have hw : |(216905561/400000000 : ℝ)|=(216905561/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311043_s0_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (198861769/625000000 : ℝ)*x 0 + (1081749823/2000000000 : ℝ)*x 1 + (4048700073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (198861769/625000000 : ℝ)^73 ≤ (5767800705749/25000000000000 : ℝ)^57 := by
    have hnat : (198861769 : ℕ)^73*25000000000000^57 ≤ 5767800705749^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198861769 625000000 5767800705749 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081749823/2000000000 : ℝ)^73 ≤ (22758658303707/50000000000000 : ℝ)^57 := by
    have hnat : (1081749823 : ℕ)^73*50000000000000^57 ≤ 22758658303707^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081749823 2000000000 22758658303707 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4048700073/10000000000 : ℝ)^73 ≤ (314114805579/1000000000000 : ℝ)^57 := by
    have hnat : (4048700073 : ℕ)^73*1000000000000^57 ≤ 314114805579^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4048700073 10000000000 314114805579 1000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(198861769/625000000 : ℝ), (1081749823/2000000000 : ℝ), (4048700073/10000000000 : ℝ)] ![(5767800705749/25000000000000 : ℝ), (22758658303707/50000000000000 : ℝ), (314114805579/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(198861769/625000000 : ℝ)|^73 ≤ (5767800705749/25000000000000 : ℝ)^57
        have hw : |(198861769/625000000 : ℝ)|=(198861769/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081749823/2000000000 : ℝ)|^73 ≤ (22758658303707/50000000000000 : ℝ)^57
        have hw : |(1081749823/2000000000 : ℝ)|=(1081749823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4048700073/10000000000 : ℝ)|^73 ≤ (314114805579/1000000000000 : ℝ)^57
        have hw : |(4048700073/10000000000 : ℝ)|=(4048700073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311043_s0_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6537990229/10000000000 : ℝ)*x 0 + (-53331233/156250000 : ℝ)*x 1 + (-2475652873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6537990229/10000000000 : ℝ)^73 ≤ (7253525834991/12500000000000 : ℝ)^57 := by
    have hnat : (6537990229 : ℕ)^73*12500000000000^57 ≤ 7253525834991^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6537990229 10000000000 7253525834991 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53331233/156250000 : ℝ)^73 ≤ (25241737163543/100000000000000 : ℝ)^57 := by
    have hnat : (53331233 : ℕ)^73*100000000000000^57 ≤ 25241737163543^57*156250000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53331233 156250000 25241737163543 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2475652873/10000000000 : ℝ)^73 ≤ (4182514035917/25000000000000 : ℝ)^57 := by
    have hnat : (2475652873 : ℕ)^73*25000000000000^57 ≤ 4182514035917^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2475652873 10000000000 4182514035917 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6537990229/10000000000 : ℝ), (-53331233/156250000 : ℝ), (-2475652873/10000000000 : ℝ)] ![(7253525834991/12500000000000 : ℝ), (25241737163543/100000000000000 : ℝ), (4182514035917/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6537990229/10000000000 : ℝ)|^73 ≤ (7253525834991/12500000000000 : ℝ)^57
        have hw : |(6537990229/10000000000 : ℝ)|=(6537990229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-53331233/156250000 : ℝ)|^73 ≤ (25241737163543/100000000000000 : ℝ)^57
        have hw : |(-53331233/156250000 : ℝ)|=(53331233/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2475652873/10000000000 : ℝ)|^73 ≤ (4182514035917/25000000000000 : ℝ)^57
        have hw : |(-2475652873/10000000000 : ℝ)|=(2475652873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311043_s0_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (57320043/125000000 : ℝ)*x 0 + (-299242889/1250000000 : ℝ)*x 1 + (5557922599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (57320043/125000000 : ℝ)^73 ≤ (575665128601/1562500000000 : ℝ)^57 := by
    have hnat : (57320043 : ℕ)^73*1562500000000^57 ≤ 575665128601^57*125000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57320043 125000000 575665128601 1562500000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299242889/1250000000 : ℝ)^73 ≤ (16026178941619/100000000000000 : ℝ)^57 := by
    have hnat : (299242889 : ℕ)^73*100000000000000^57 ≤ 16026178941619^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299242889 1250000000 16026178941619 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5557922599/10000000000 : ℝ)^73 ≤ (47131252812167/100000000000000 : ℝ)^57 := by
    have hnat : (5557922599 : ℕ)^73*100000000000000^57 ≤ 47131252812167^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5557922599 10000000000 47131252812167 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(57320043/125000000 : ℝ), (-299242889/1250000000 : ℝ), (5557922599/10000000000 : ℝ)] ![(575665128601/1562500000000 : ℝ), (16026178941619/100000000000000 : ℝ), (47131252812167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(57320043/125000000 : ℝ)|^73 ≤ (575665128601/1562500000000 : ℝ)^57
        have hw : |(57320043/125000000 : ℝ)|=(57320043/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-299242889/1250000000 : ℝ)|^73 ≤ (16026178941619/100000000000000 : ℝ)^57
        have hw : |(-299242889/1250000000 : ℝ)|=(299242889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5557922599/10000000000 : ℝ)|^73 ≤ (47131252812167/100000000000000 : ℝ)^57
        have hw : |(5557922599/10000000000 : ℝ)|=(5557922599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311043 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19517/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19517/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (71/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^71 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^71*1^16 ≤ 1^16*1^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2338125084112429/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2338125084112429/2000000000000000 : ℝ)^71 := by
      have hnat : (2 : ℕ)^16*2000000000000000^71 ≤ 2338125084112429^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2338125084112429 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2338125084112429/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12809149154094097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12809149154094097/10000000000000000 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*10000000000000000^71 ≤ 12809149154094097^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12809149154094097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12809149154094097/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (71/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^71 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^71*1^16 ≤ 1^16*1^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2338125084112429/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2338125084112429/2000000000000000 : ℝ)^71 := by
      have hnat : (2 : ℕ)^16*2000000000000000^71 ≤ 2338125084112429^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2338125084112429 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2338125084112429/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12809149154094097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12809149154094097/10000000000000000 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*10000000000000000^71 ≤ 12809149154094097^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12809149154094097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12809149154094097/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (71/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^71 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^71*1^16 ≤ 1^16*1^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2338125084112429/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2338125084112429/2000000000000000 : ℝ)^71 := by
      have hnat : (2 : ℕ)^16*2000000000000000^71 ≤ 2338125084112429^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2338125084112429 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2338125084112429/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12809149154094097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12809149154094097/10000000000000000 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*10000000000000000^71 ≤ 12809149154094097^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12809149154094097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12809149154094097/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(338125084112429/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(338125084112429/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2652535601/10000000000 : ℝ)*X 0 0+(-2254533963/5000000000 : ℝ)*X 0 1+(216905561/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311043_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((198861769/625000000 : ℝ)*X 1 0+(1081749823/2000000000 : ℝ)*X 1 1+(4048700073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311043_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((6537990229/10000000000 : ℝ)*X 2 0+(-53331233/156250000 : ℝ)*X 2 1+(-2475652873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311043_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((57320043/125000000 : ℝ)*X 0 0+(-299242889/1250000000 : ℝ)*X 0 1+(5557922599/10000000000 : ℝ)*X 0 2+(57320043/125000000 : ℝ)*X 1 0+(-299242889/1250000000 : ℝ)*X 1 1+(5557922599/10000000000 : ℝ)*X 1 2+(57320043/125000000 : ℝ)*X 2 0+(-299242889/1250000000 : ℝ)*X 2 1+(5557922599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311043_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-85761/12500 : ℝ) < ((-41087/25000 : ℝ)*P 0+(-41087/25000 : ℝ)*P 1+(-41087/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-85761/12500 : ℝ) < (-6858214774762566734337/1000000000000000000000 : ℝ) := by norm_num
    linear_combination (54207/500000000000 : ℝ)*(base10) + (1151/250000000000 : ℝ)*(base17) + (19141/250000000000 : ℝ)*(base21) + (13543/100000000000 : ℝ)*(base27) + (17297656691/50000000000 : ℝ)*(base40) + (3982613759/125000000000 : ℝ)*(base50) + (369142406417/1000000000000 : ℝ)*(base59) + (179689092299/1000000000000 : ℝ)*(base60) + (41087/25000 : ℝ)*(major_s0_0) + (41087/25000 : ℝ)*(major_s0_1) + (41087/25000 : ℝ)*(major_s0_2) + (228607148317/100000000000 : ℝ)*(sp_s0_0) + (114303579349/50000000000 : ℝ)*(sp_s0_1) + (114303575751/50000000000 : ℝ)*(sp_s0_2) + (99999986457/100000000000 : ℝ)*(sp_s0_6) + (71439737237/31250000000 : ℝ)*(f.sum) + (242878563/1000000000000000000000 : ℝ)*base62 + (76368989/500000000000000000000 : ℝ)*base64 + (68066343/250000000000000000000 : ℝ)*base66 + (172071683/250000000000000000000 : ℝ)*base68 + (58696433/100000000000000000000 : ℝ)*base70 + (539820599/1000000000000000000000 : ℝ)*base73 + (111939789/500000000000000000000 : ℝ)*base74 + (144648383/250000000000000000000 : ℝ)*base76 + (47363619/200000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c311044_s0_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-404682067/5000000000 : ℝ)*x 0 + (-1669853407/2500000000 : ℝ)*x 1 + (-4538938559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404682067/5000000000 : ℝ)^73 ≤ (1998149838611/50000000000000 : ℝ)^57 := by
    have hnat : (404682067 : ℕ)^73*50000000000000^57 ≤ 1998149838611^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404682067 5000000000 1998149838611 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1669853407/2500000000 : ℝ)^73 ≤ (59640610780501/100000000000000 : ℝ)^57 := by
    have hnat : (1669853407 : ℕ)^73*100000000000000^57 ≤ 59640610780501^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1669853407 2500000000 59640610780501 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4538938559/10000000000 : ℝ)^73 ≤ (9090772383551/25000000000000 : ℝ)^57 := by
    have hnat : (4538938559 : ℕ)^73*25000000000000^57 ≤ 9090772383551^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4538938559 10000000000 9090772383551 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-404682067/5000000000 : ℝ), (-1669853407/2500000000 : ℝ), (-4538938559/10000000000 : ℝ)] ![(1998149838611/50000000000000 : ℝ), (59640610780501/100000000000000 : ℝ), (9090772383551/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-404682067/5000000000 : ℝ)|^73 ≤ (1998149838611/50000000000000 : ℝ)^57
        have hw : |(-404682067/5000000000 : ℝ)|=(404682067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1669853407/2500000000 : ℝ)|^73 ≤ (59640610780501/100000000000000 : ℝ)^57
        have hw : |(-1669853407/2500000000 : ℝ)|=(1669853407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4538938559/10000000000 : ℝ)|^73 ≤ (9090772383551/25000000000000 : ℝ)^57
        have hw : |(-4538938559/10000000000 : ℝ)|=(4538938559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311044_s0_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5088470703/10000000000 : ℝ)*x 0 + (-49249233/156250000 : ℝ)*x 1 + (883286887/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5088470703/10000000000 : ℝ)^73 ≤ (21047272165381/50000000000000 : ℝ)^57 := by
    have hnat : (5088470703 : ℕ)^73*50000000000000^57 ≤ 21047272165381^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5088470703 10000000000 21047272165381 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49249233/156250000 : ℝ)^73 ≤ (2279448664141/10000000000000 : ℝ)^57 := by
    have hnat : (49249233 : ℕ)^73*10000000000000^57 ≤ 2279448664141^57*156250000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49249233 156250000 2279448664141 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (883286887/2000000000 : ℝ)^73 ≤ (17555484503511/50000000000000 : ℝ)^57 := by
    have hnat : (883286887 : ℕ)^73*50000000000000^57 ≤ 17555484503511^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883286887 2000000000 17555484503511 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5088470703/10000000000 : ℝ), (-49249233/156250000 : ℝ), (883286887/2000000000 : ℝ)] ![(21047272165381/50000000000000 : ℝ), (2279448664141/10000000000000 : ℝ), (17555484503511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5088470703/10000000000 : ℝ)|^73 ≤ (21047272165381/50000000000000 : ℝ)^57
        have hw : |(5088470703/10000000000 : ℝ)|=(5088470703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49249233/156250000 : ℝ)|^73 ≤ (2279448664141/10000000000000 : ℝ)^57
        have hw : |(-49249233/156250000 : ℝ)|=(49249233/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(883286887/2000000000 : ℝ)|^73 ≤ (17555484503511/50000000000000 : ℝ)^57
        have hw : |(883286887/2000000000 : ℝ)|=(883286887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311044_s0_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (743108091/1000000000 : ℝ)*x 0 + (-1403527239/5000000000 : ℝ)*x 1 + (-238438741/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (743108091/1000000000 : ℝ)^73 ≤ (8546062612023/12500000000000 : ℝ)^57 := by
    have hnat : (743108091 : ℕ)^73*12500000000000^57 ≤ 8546062612023^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      743108091 1000000000 8546062612023 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1403527239/5000000000 : ℝ)^73 ≤ (19650512630751/100000000000000 : ℝ)^57 := by
    have hnat : (1403527239 : ℕ)^73*100000000000000^57 ≤ 19650512630751^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403527239 5000000000 19650512630751 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238438741/1250000000 : ℝ)^73 ≤ (11980986460761/100000000000000 : ℝ)^57 := by
    have hnat : (238438741 : ℕ)^73*100000000000000^57 ≤ 11980986460761^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238438741 1250000000 11980986460761 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(743108091/1000000000 : ℝ), (-1403527239/5000000000 : ℝ), (-238438741/1250000000 : ℝ)] ![(8546062612023/12500000000000 : ℝ), (19650512630751/100000000000000 : ℝ), (11980986460761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(743108091/1000000000 : ℝ)|^73 ≤ (8546062612023/12500000000000 : ℝ)^57
        have hw : |(743108091/1000000000 : ℝ)|=(743108091/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1403527239/5000000000 : ℝ)|^73 ≤ (19650512630751/100000000000000 : ℝ)^57
        have hw : |(-1403527239/5000000000 : ℝ)|=(1403527239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-238438741/1250000000 : ℝ)|^73 ≤ (11980986460761/100000000000000 : ℝ)^57
        have hw : |(-238438741/1250000000 : ℝ)|=(238438741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311044_s0_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-887705339/10000000000 : ℝ)*x 0 + (-7084452429/10000000000 : ℝ)*x 1 + (-100660991/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (887705339/10000000000 : ℝ)^73 ≤ (899655094393/20000000000000 : ℝ)^57 := by
    have hnat : (887705339 : ℕ)^73*20000000000000^57 ≤ 899655094393^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887705339 10000000000 899655094393 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7084452429/10000000000 : ℝ)^73 ≤ (64311257409273/100000000000000 : ℝ)^57 := by
    have hnat : (7084452429 : ℕ)^73*100000000000000^57 ≤ 64311257409273^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7084452429 10000000000 64311257409273 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100660991/250000000 : ℝ)^73 ≤ (3898808388227/12500000000000 : ℝ)^57 := by
    have hnat : (100660991 : ℕ)^73*12500000000000^57 ≤ 3898808388227^57*250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100660991 250000000 3898808388227 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-887705339/10000000000 : ℝ), (-7084452429/10000000000 : ℝ), (-100660991/250000000 : ℝ)] ![(899655094393/20000000000000 : ℝ), (64311257409273/100000000000000 : ℝ), (3898808388227/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-887705339/10000000000 : ℝ)|^73 ≤ (899655094393/20000000000000 : ℝ)^57
        have hw : |(-887705339/10000000000 : ℝ)|=(887705339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7084452429/10000000000 : ℝ)|^73 ≤ (64311257409273/100000000000000 : ℝ)^57
        have hw : |(-7084452429/10000000000 : ℝ)|=(7084452429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-100660991/250000000 : ℝ)|^73 ≤ (3898808388227/12500000000000 : ℝ)^57
        have hw : |(-100660991/250000000 : ℝ)|=(100660991/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311044_s0_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (958597187/2000000000 : ℝ)*x 0 + (503453263/1250000000 : ℝ)*x 1 + (-485798741/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (958597187/2000000000 : ℝ)^73 ≤ (9747466481843/25000000000000 : ℝ)^57 := by
    have hnat : (958597187 : ℕ)^73*25000000000000^57 ≤ 9747466481843^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958597187 2000000000 9747466481843 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503453263/1250000000 : ℝ)^73 ≤ (7800559579681/25000000000000 : ℝ)^57 := by
    have hnat : (503453263 : ℕ)^73*25000000000000^57 ≤ 7800559579681^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503453263 1250000000 7800559579681 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485798741/1250000000 : ℝ)^73 ≤ (29807895735997/100000000000000 : ℝ)^57 := by
    have hnat : (485798741 : ℕ)^73*100000000000000^57 ≤ 29807895735997^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485798741 1250000000 29807895735997 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(958597187/2000000000 : ℝ), (503453263/1250000000 : ℝ), (-485798741/1250000000 : ℝ)] ![(9747466481843/25000000000000 : ℝ), (7800559579681/25000000000000 : ℝ), (29807895735997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(958597187/2000000000 : ℝ)|^73 ≤ (9747466481843/25000000000000 : ℝ)^57
        have hw : |(958597187/2000000000 : ℝ)|=(958597187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(503453263/1250000000 : ℝ)|^73 ≤ (7800559579681/25000000000000 : ℝ)^57
        have hw : |(503453263/1250000000 : ℝ)|=(503453263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-485798741/1250000000 : ℝ)|^73 ≤ (29807895735997/100000000000000 : ℝ)^57
        have hw : |(-485798741/1250000000 : ℝ)|=(485798741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311044_s0_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4792986083/10000000000 : ℝ)*x 0 + (-470975077/2000000000 : ℝ)*x 1 + (168445607/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4792986083/10000000000 : ℝ)^73 ≤ (38989867469269/100000000000000 : ℝ)^57 := by
    have hnat : (4792986083 : ℕ)^73*100000000000000^57 ≤ 38989867469269^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4792986083 10000000000 38989867469269 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (470975077/2000000000 : ℝ)^73 ≤ (7845998678503/50000000000000 : ℝ)^57 := by
    have hnat : (470975077 : ℕ)^73*50000000000000^57 ≤ 7845998678503^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470975077 2000000000 7845998678503 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168445607/312500000 : ℝ)^73 ≤ (45318135160931/100000000000000 : ℝ)^57 := by
    have hnat : (168445607 : ℕ)^73*100000000000000^57 ≤ 45318135160931^57*312500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168445607 312500000 45318135160931 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4792986083/10000000000 : ℝ), (-470975077/2000000000 : ℝ), (168445607/312500000 : ℝ)] ![(38989867469269/100000000000000 : ℝ), (7845998678503/50000000000000 : ℝ), (45318135160931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4792986083/10000000000 : ℝ)|^73 ≤ (38989867469269/100000000000000 : ℝ)^57
        have hw : |(4792986083/10000000000 : ℝ)|=(4792986083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-470975077/2000000000 : ℝ)|^73 ≤ (7845998678503/50000000000000 : ℝ)^57
        have hw : |(-470975077/2000000000 : ℝ)|=(470975077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168445607/312500000 : ℝ)|^73 ≤ (45318135160931/100000000000000 : ℝ)^57
        have hw : |(168445607/312500000 : ℝ)|=(168445607/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311044_s0_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7587167697/10000000000 : ℝ)*x 0 + (-2071211999/10000000000 : ℝ)*x 1 + (-2445970159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7587167697/10000000000 : ℝ)^73 ≤ (7021305017841/10000000000000 : ℝ)^57 := by
    have hnat : (7587167697 : ℕ)^73*10000000000000^57 ≤ 7021305017841^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7587167697 10000000000 7021305017841 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071211999/10000000000 : ℝ)^73 ≤ (13313357247961/100000000000000 : ℝ)^57 := by
    have hnat : (2071211999 : ℕ)^73*100000000000000^57 ≤ 13313357247961^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071211999 10000000000 13313357247961 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2445970159/10000000000 : ℝ)^73 ≤ (16473592560837/100000000000000 : ℝ)^57 := by
    have hnat : (2445970159 : ℕ)^73*100000000000000^57 ≤ 16473592560837^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2445970159 10000000000 16473592560837 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7587167697/10000000000 : ℝ), (-2071211999/10000000000 : ℝ), (-2445970159/10000000000 : ℝ)] ![(7021305017841/10000000000000 : ℝ), (13313357247961/100000000000000 : ℝ), (16473592560837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7587167697/10000000000 : ℝ)|^73 ≤ (7021305017841/10000000000000 : ℝ)^57
        have hw : |(7587167697/10000000000 : ℝ)|=(7587167697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2071211999/10000000000 : ℝ)|^73 ≤ (13313357247961/100000000000000 : ℝ)^57
        have hw : |(-2071211999/10000000000 : ℝ)|=(2071211999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2445970159/10000000000 : ℝ)|^73 ≤ (16473592560837/100000000000000 : ℝ)^57
        have hw : |(-2445970159/10000000000 : ℝ)|=(2445970159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311044_s0_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3353419/2000000000 : ℝ)*x 0 + (-420121247/625000000 : ℝ)*x 1 + (-1218712143/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3353419/2000000000 : ℝ)^73 ≤ (27884205011/100000000000000 : ℝ)^57 := by
    have hnat : (3353419 : ℕ)^73*100000000000000^57 ≤ 27884205011^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3353419 2000000000 27884205011 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (420121247/625000000 : ℝ)^73 ≤ (2405094025339/4000000000000 : ℝ)^57 := by
    have hnat : (420121247 : ℕ)^73*4000000000000^57 ≤ 2405094025339^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420121247 625000000 2405094025339 4000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1218712143/2500000000 : ℝ)^73 ≤ (19922382574583/50000000000000 : ℝ)^57 := by
    have hnat : (1218712143 : ℕ)^73*50000000000000^57 ≤ 19922382574583^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1218712143 2500000000 19922382574583 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3353419/2000000000 : ℝ), (-420121247/625000000 : ℝ), (-1218712143/2500000000 : ℝ)] ![(27884205011/100000000000000 : ℝ), (2405094025339/4000000000000 : ℝ), (19922382574583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3353419/2000000000 : ℝ)|^73 ≤ (27884205011/100000000000000 : ℝ)^57
        have hw : |(-3353419/2000000000 : ℝ)|=(3353419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-420121247/625000000 : ℝ)|^73 ≤ (2405094025339/4000000000000 : ℝ)^57
        have hw : |(-420121247/625000000 : ℝ)|=(420121247/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1218712143/2500000000 : ℝ)|^73 ≤ (19922382574583/50000000000000 : ℝ)^57
        have hw : |(-1218712143/2500000000 : ℝ)|=(1218712143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311044_s0_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4458144351/10000000000 : ℝ)*x 0 + (3159594923/10000000000 : ℝ)*x 1 + (-5041588179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4458144351/10000000000 : ℝ)^73 ≤ (35536207265813/100000000000000 : ℝ)^57 := by
    have hnat : (4458144351 : ℕ)^73*100000000000000^57 ≤ 35536207265813^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4458144351 10000000000 35536207265813 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3159594923/10000000000 : ℝ)^73 ≤ (5716327127867/25000000000000 : ℝ)^57 := by
    have hnat : (3159594923 : ℕ)^73*25000000000000^57 ≤ 5716327127867^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3159594923 10000000000 5716327127867 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5041588179/10000000000 : ℝ)^73 ≤ (519981052579/1250000000000 : ℝ)^57 := by
    have hnat : (5041588179 : ℕ)^73*1250000000000^57 ≤ 519981052579^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5041588179 10000000000 519981052579 1250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4458144351/10000000000 : ℝ), (3159594923/10000000000 : ℝ), (-5041588179/10000000000 : ℝ)] ![(35536207265813/100000000000000 : ℝ), (5716327127867/25000000000000 : ℝ), (519981052579/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4458144351/10000000000 : ℝ)|^73 ≤ (35536207265813/100000000000000 : ℝ)^57
        have hw : |(4458144351/10000000000 : ℝ)|=(4458144351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3159594923/10000000000 : ℝ)|^73 ≤ (5716327127867/25000000000000 : ℝ)^57
        have hw : |(3159594923/10000000000 : ℝ)|=(3159594923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5041588179/10000000000 : ℝ)|^73 ≤ (519981052579/1250000000000 : ℝ)^57
        have hw : |(-5041588179/10000000000 : ℝ)|=(5041588179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311044_s0_16 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1488651439/2500000000 : ℝ)*x 0 + (-158179123/625000000 : ℝ)*x 1 + (2019180347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1488651439/2500000000 : ℝ)^73 ≤ (51481816066037/100000000000000 : ℝ)^57 := by
    have hnat : (1488651439 : ℕ)^73*100000000000000^57 ≤ 51481816066037^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1488651439 2500000000 51481816066037 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (158179123/625000000 : ℝ)^73 ≤ (3441880153051/20000000000000 : ℝ)^57 := by
    have hnat : (158179123 : ℕ)^73*20000000000000^57 ≤ 3441880153051^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158179123 625000000 3441880153051 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2019180347/5000000000 : ℝ)^73 ≤ (3130878315113/10000000000000 : ℝ)^57 := by
    have hnat : (2019180347 : ℕ)^73*10000000000000^57 ≤ 3130878315113^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019180347 5000000000 3130878315113 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1488651439/2500000000 : ℝ), (-158179123/625000000 : ℝ), (2019180347/5000000000 : ℝ)] ![(51481816066037/100000000000000 : ℝ), (3441880153051/20000000000000 : ℝ), (3130878315113/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1488651439/2500000000 : ℝ)|^73 ≤ (51481816066037/100000000000000 : ℝ)^57
        have hw : |(1488651439/2500000000 : ℝ)|=(1488651439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-158179123/625000000 : ℝ)|^73 ≤ (3441880153051/20000000000000 : ℝ)^57
        have hw : |(-158179123/625000000 : ℝ)|=(158179123/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2019180347/5000000000 : ℝ)|^73 ≤ (3130878315113/10000000000000 : ℝ)^57
        have hw : |(2019180347/5000000000 : ℝ)|=(2019180347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311044_s0_19 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1127213903/1250000000 : ℝ)*x 0 + (-1317591999/10000000000 : ℝ)*x 1 + (-119442109/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1127213903/1250000000 : ℝ)^73 ≤ (87597514367667/100000000000000 : ℝ)^57 := by
    have hnat : (1127213903 : ℕ)^73*100000000000000^57 ≤ 87597514367667^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127213903 1250000000 87597514367667 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1317591999/10000000000 : ℝ)^73 ≤ (932420750797/12500000000000 : ℝ)^57 := by
    have hnat : (1317591999 : ℕ)^73*12500000000000^57 ≤ 932420750797^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317591999 10000000000 932420750797 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119442109/1250000000 : ℝ)^73 ≤ (4943119621869/100000000000000 : ℝ)^57 := by
    have hnat : (119442109 : ℕ)^73*100000000000000^57 ≤ 4943119621869^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119442109 1250000000 4943119621869 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1127213903/1250000000 : ℝ), (-1317591999/10000000000 : ℝ), (-119442109/1250000000 : ℝ)] ![(87597514367667/100000000000000 : ℝ), (932420750797/12500000000000 : ℝ), (4943119621869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1127213903/1250000000 : ℝ)|^73 ≤ (87597514367667/100000000000000 : ℝ)^57
        have hw : |(1127213903/1250000000 : ℝ)|=(1127213903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1317591999/10000000000 : ℝ)|^73 ≤ (932420750797/12500000000000 : ℝ)^57
        have hw : |(-1317591999/10000000000 : ℝ)|=(1317591999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-119442109/1250000000 : ℝ)|^73 ≤ (4943119621869/100000000000000 : ℝ)^57
        have hw : |(-119442109/1250000000 : ℝ)|=(119442109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311044_s0_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-13193293/10000000000 : ℝ)*x 0 + (-3665056871/5000000000 : ℝ)*x 1 + (-418761839/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13193293/10000000000 : ℝ)^73 ≤ (20513100171/100000000000000 : ℝ)^57 := by
    have hnat : (13193293 : ℕ)^73*100000000000000^57 ≤ 20513100171^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13193293 10000000000 20513100171 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3665056871/5000000000 : ℝ)^73 ≤ (8397636413467/12500000000000 : ℝ)^57 := by
    have hnat : (3665056871 : ℕ)^73*12500000000000^57 ≤ 8397636413467^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3665056871 5000000000 8397636413467 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418761839/1000000000 : ℝ)^73 ≤ (4099799448141/12500000000000 : ℝ)^57 := by
    have hnat : (418761839 : ℕ)^73*12500000000000^57 ≤ 4099799448141^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418761839 1000000000 4099799448141 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13193293/10000000000 : ℝ), (-3665056871/5000000000 : ℝ), (-418761839/1000000000 : ℝ)] ![(20513100171/100000000000000 : ℝ), (8397636413467/12500000000000 : ℝ), (4099799448141/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13193293/10000000000 : ℝ)|^73 ≤ (20513100171/100000000000000 : ℝ)^57
        have hw : |(-13193293/10000000000 : ℝ)|=(13193293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3665056871/5000000000 : ℝ)|^73 ≤ (8397636413467/12500000000000 : ℝ)^57
        have hw : |(-3665056871/5000000000 : ℝ)|=(3665056871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-418761839/1000000000 : ℝ)|^73 ≤ (4099799448141/12500000000000 : ℝ)^57
        have hw : |(-418761839/1000000000 : ℝ)|=(418761839/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311044_s0_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2979089829/5000000000 : ℝ)*x 0 + (284321779/1000000000 : ℝ)*x 1 + (-3752926691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2979089829/5000000000 : ℝ)^73 ≤ (10304278343393/20000000000000 : ℝ)^57 := by
    have hnat : (2979089829 : ℕ)^73*20000000000000^57 ≤ 10304278343393^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2979089829 5000000000 10304278343393 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284321779/1000000000 : ℝ)^73 ≤ (19975316650129/100000000000000 : ℝ)^57 := by
    have hnat : (284321779 : ℕ)^73*100000000000000^57 ≤ 19975316650129^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284321779 1000000000 19975316650129 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3752926691/10000000000 : ℝ)^73 ≤ (28503291617181/100000000000000 : ℝ)^57 := by
    have hnat : (3752926691 : ℕ)^73*100000000000000^57 ≤ 28503291617181^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3752926691 10000000000 28503291617181 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2979089829/5000000000 : ℝ), (284321779/1000000000 : ℝ), (-3752926691/10000000000 : ℝ)] ![(10304278343393/20000000000000 : ℝ), (19975316650129/100000000000000 : ℝ), (28503291617181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2979089829/5000000000 : ℝ)|^73 ≤ (10304278343393/20000000000000 : ℝ)^57
        have hw : |(2979089829/5000000000 : ℝ)|=(2979089829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(284321779/1000000000 : ℝ)|^73 ≤ (19975316650129/100000000000000 : ℝ)^57
        have hw : |(284321779/1000000000 : ℝ)|=(284321779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3752926691/10000000000 : ℝ)|^73 ≤ (28503291617181/100000000000000 : ℝ)^57
        have hw : |(-3752926691/10000000000 : ℝ)|=(3752926691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311044_s0_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (897322287/2000000000 : ℝ)*x 0 + (-3539285159/10000000000 : ℝ)*x 1 + (4671706047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (897322287/2000000000 : ℝ)^73 ≤ (35827075557951/100000000000000 : ℝ)^57 := by
    have hnat : (897322287 : ℕ)^73*100000000000000^57 ≤ 35827075557951^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897322287 2000000000 35827075557951 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3539285159/10000000000 : ℝ)^73 ≤ (26442064478831/100000000000000 : ℝ)^57 := by
    have hnat : (3539285159 : ℕ)^73*100000000000000^57 ≤ 26442064478831^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3539285159 10000000000 26442064478831 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4671706047/10000000000 : ℝ)^73 ≤ (37730859948903/100000000000000 : ℝ)^57 := by
    have hnat : (4671706047 : ℕ)^73*100000000000000^57 ≤ 37730859948903^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4671706047 10000000000 37730859948903 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(897322287/2000000000 : ℝ), (-3539285159/10000000000 : ℝ), (4671706047/10000000000 : ℝ)] ![(35827075557951/100000000000000 : ℝ), (26442064478831/100000000000000 : ℝ), (37730859948903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(897322287/2000000000 : ℝ)|^73 ≤ (35827075557951/100000000000000 : ℝ)^57
        have hw : |(897322287/2000000000 : ℝ)|=(897322287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3539285159/10000000000 : ℝ)|^73 ≤ (26442064478831/100000000000000 : ℝ)^57
        have hw : |(-3539285159/10000000000 : ℝ)|=(3539285159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4671706047/10000000000 : ℝ)|^73 ≤ (37730859948903/100000000000000 : ℝ)^57
        have hw : |(4671706047/10000000000 : ℝ)|=(4671706047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311044_s0_25 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8952608077/10000000000 : ℝ)*x 0 + (-754697211/5000000000 : ℝ)*x 1 + (-215575367/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8952608077/10000000000 : ℝ)^73 ≤ (21697102565497/25000000000000 : ℝ)^57 := by
    have hnat : (8952608077 : ℕ)^73*25000000000000^57 ≤ 21697102565497^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8952608077 10000000000 21697102565497 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (754697211/5000000000 : ℝ)^73 ≤ (8877511209171/100000000000000 : ℝ)^57 := by
    have hnat : (754697211 : ℕ)^73*100000000000000^57 ≤ 8877511209171^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754697211 5000000000 8877511209171 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215575367/2500000000 : ℝ)^73 ≤ (4334078515861/100000000000000 : ℝ)^57 := by
    have hnat : (215575367 : ℕ)^73*100000000000000^57 ≤ 4334078515861^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215575367 2500000000 4334078515861 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8952608077/10000000000 : ℝ), (-754697211/5000000000 : ℝ), (-215575367/2500000000 : ℝ)] ![(21697102565497/25000000000000 : ℝ), (8877511209171/100000000000000 : ℝ), (4334078515861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8952608077/10000000000 : ℝ)|^73 ≤ (21697102565497/25000000000000 : ℝ)^57
        have hw : |(8952608077/10000000000 : ℝ)|=(8952608077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-754697211/5000000000 : ℝ)|^73 ≤ (8877511209171/100000000000000 : ℝ)^57
        have hw : |(-754697211/5000000000 : ℝ)|=(754697211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-215575367/2500000000 : ℝ)|^73 ≤ (4334078515861/100000000000000 : ℝ)^57
        have hw : |(-215575367/2500000000 : ℝ)|=(215575367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311044_s1_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2355724719/10000000000 : ℝ)*x 0 + (-713018821/1250000000 : ℝ)*x 1 + (-27887507/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2355724719/10000000000 : ℝ)^73 ≤ (7849623017371/50000000000000 : ℝ)^57 := by
    have hnat : (2355724719 : ℕ)^73*50000000000000^57 ≤ 7849623017371^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2355724719 10000000000 7849623017371 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (713018821/1250000000 : ℝ)^73 ≤ (243625849021/500000000000 : ℝ)^57 := by
    have hnat : (713018821 : ℕ)^73*500000000000^57 ≤ 243625849021^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713018821 1250000000 243625849021 500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27887507/62500000 : ℝ)^73 ≤ (17787792072681/50000000000000 : ℝ)^57 := by
    have hnat : (27887507 : ℕ)^73*50000000000000^57 ≤ 17787792072681^57*62500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27887507 62500000 17787792072681 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2355724719/10000000000 : ℝ), (-713018821/1250000000 : ℝ), (-27887507/62500000 : ℝ)] ![(7849623017371/50000000000000 : ℝ), (243625849021/500000000000 : ℝ), (17787792072681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2355724719/10000000000 : ℝ)|^73 ≤ (7849623017371/50000000000000 : ℝ)^57
        have hw : |(-2355724719/10000000000 : ℝ)|=(2355724719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-713018821/1250000000 : ℝ)|^73 ≤ (243625849021/500000000000 : ℝ)^57
        have hw : |(-713018821/1250000000 : ℝ)|=(713018821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27887507/62500000 : ℝ)|^73 ≤ (17787792072681/50000000000000 : ℝ)^57
        have hw : |(-27887507/62500000 : ℝ)|=(27887507/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311044_s1_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (954663853/2000000000 : ℝ)*x 0 + (890339367/2500000000 : ℝ)*x 1 + (-4362371599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (954663853/2000000000 : ℝ)^73 ≤ (9696273078057/25000000000000 : ℝ)^57 := by
    have hnat : (954663853 : ℕ)^73*25000000000000^57 ≤ 9696273078057^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954663853 2000000000 9696273078057 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (890339367/2500000000 : ℝ)^73 ≤ (13326720068693/50000000000000 : ℝ)^57 := by
    have hnat : (890339367 : ℕ)^73*50000000000000^57 ≤ 13326720068693^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890339367 2500000000 13326720068693 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4362371599/10000000000 : ℝ)^73 ≤ (34561467536743/100000000000000 : ℝ)^57 := by
    have hnat : (4362371599 : ℕ)^73*100000000000000^57 ≤ 34561467536743^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362371599 10000000000 34561467536743 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(954663853/2000000000 : ℝ), (890339367/2500000000 : ℝ), (-4362371599/10000000000 : ℝ)] ![(9696273078057/25000000000000 : ℝ), (13326720068693/50000000000000 : ℝ), (34561467536743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(954663853/2000000000 : ℝ)|^73 ≤ (9696273078057/25000000000000 : ℝ)^57
        have hw : |(954663853/2000000000 : ℝ)|=(954663853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(890339367/2500000000 : ℝ)|^73 ≤ (13326720068693/50000000000000 : ℝ)^57
        have hw : |(890339367/2500000000 : ℝ)|=(890339367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4362371599/10000000000 : ℝ)|^73 ≤ (34561467536743/100000000000000 : ℝ)^57
        have hw : |(-4362371599/10000000000 : ℝ)|=(4362371599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311044_s1_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2383454259/5000000000 : ℝ)*x 0 + (-1782193507/5000000000 : ℝ)*x 1 + (873216509/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2383454259/5000000000 : ℝ)^73 ≤ (38718393347761/100000000000000 : ℝ)^57 := by
    have hnat : (2383454259 : ℕ)^73*100000000000000^57 ≤ 38718393347761^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2383454259 5000000000 38718393347761 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1782193507/5000000000 : ℝ)^73 ≤ (1067299254937/4000000000000 : ℝ)^57 := by
    have hnat : (1782193507 : ℕ)^73*4000000000000^57 ≤ 1067299254937^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782193507 5000000000 1067299254937 4000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (873216509/2000000000 : ℝ)^73 ≤ (34599125254393/100000000000000 : ℝ)^57 := by
    have hnat : (873216509 : ℕ)^73*100000000000000^57 ≤ 34599125254393^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873216509 2000000000 34599125254393 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2383454259/5000000000 : ℝ), (-1782193507/5000000000 : ℝ), (873216509/2000000000 : ℝ)] ![(38718393347761/100000000000000 : ℝ), (1067299254937/4000000000000 : ℝ), (34599125254393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2383454259/5000000000 : ℝ)|^73 ≤ (38718393347761/100000000000000 : ℝ)^57
        have hw : |(2383454259/5000000000 : ℝ)|=(2383454259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1782193507/5000000000 : ℝ)|^73 ≤ (1067299254937/4000000000000 : ℝ)^57
        have hw : |(-1782193507/5000000000 : ℝ)|=(1782193507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(873216509/2000000000 : ℝ)|^73 ≤ (34599125254393/100000000000000 : ℝ)^57
        have hw : |(873216509/2000000000 : ℝ)|=(873216509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311044_s1_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5876284307/10000000000 : ℝ)*x 0 + (-469631773/1250000000 : ℝ)*x 1 + (-1469454547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5876284307/10000000000 : ℝ)^73 ≤ (12654050379319/25000000000000 : ℝ)^57 := by
    have hnat : (5876284307 : ℕ)^73*25000000000000^57 ≤ 12654050379319^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5876284307 10000000000 12654050379319 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (469631773/1250000000 : ℝ)^73 ≤ (28543445384609/100000000000000 : ℝ)^57 := by
    have hnat : (469631773 : ℕ)^73*100000000000000^57 ≤ 28543445384609^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469631773 1250000000 28543445384609 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1469454547/5000000000 : ℝ)^73 ≤ (20840353091257/100000000000000 : ℝ)^57 := by
    have hnat : (1469454547 : ℕ)^73*100000000000000^57 ≤ 20840353091257^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1469454547 5000000000 20840353091257 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5876284307/10000000000 : ℝ), (-469631773/1250000000 : ℝ), (-1469454547/5000000000 : ℝ)] ![(12654050379319/25000000000000 : ℝ), (28543445384609/100000000000000 : ℝ), (20840353091257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5876284307/10000000000 : ℝ)|^73 ≤ (12654050379319/25000000000000 : ℝ)^57
        have hw : |(5876284307/10000000000 : ℝ)|=(5876284307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-469631773/1250000000 : ℝ)|^73 ≤ (28543445384609/100000000000000 : ℝ)^57
        have hw : |(-469631773/1250000000 : ℝ)|=(469631773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1469454547/5000000000 : ℝ)|^73 ≤ (20840353091257/100000000000000 : ℝ)^57
        have hw : |(-1469454547/5000000000 : ℝ)|=(1469454547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311044 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19517/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19517/25000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (71/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^71 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^71*1^16 ≤ 1^16*1^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2338125084112429/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2338125084112429/2000000000000000 : ℝ)^71 := by
      have hnat : (2 : ℕ)^16*2000000000000000^71 ≤ 2338125084112429^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2338125084112429 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2338125084112429/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12809149154094097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12809149154094097/10000000000000000 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*10000000000000000^71 ≤ 12809149154094097^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12809149154094097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12809149154094097/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (71/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^71 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^71*1^16 ≤ 1^16*1^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2338125084112429/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2338125084112429/2000000000000000 : ℝ)^71 := by
      have hnat : (2 : ℕ)^16*2000000000000000^71 ≤ 2338125084112429^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2338125084112429 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2338125084112429/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12809149154094097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12809149154094097/10000000000000000 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*10000000000000000^71 ≤ 12809149154094097^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12809149154094097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12809149154094097/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(69907733345747/625000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (71/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^71 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^71*1^16 ≤ 1^16*1^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2338125084112429/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (2338125084112429/2000000000000000 : ℝ)^71 := by
      have hnat : (2 : ℕ)^16*2000000000000000^71 ≤ 2338125084112429^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2338125084112429 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2338125084112429/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12809149154094097/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (12809149154094097/10000000000000000 : ℝ)^71 := by
      have hnat : (3 : ℕ)^16*10000000000000000^71 ≤ 12809149154094097^71*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12809149154094097 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12809149154094097/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(69907733345747/625000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (338125084112429/2000000000000000 : ℝ)) (beta := (69907733345747/625000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(338125084112429/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(69907733345747/625000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-404682067/5000000000 : ℝ)*X 0 0+(-1669853407/2500000000 : ℝ)*X 0 1+(-4538938559/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5088470703/10000000000 : ℝ)*X 2 0+(-49249233/156250000 : ℝ)*X 2 1+(883286887/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((743108091/1000000000 : ℝ)*X 0 0+(-1403527239/5000000000 : ℝ)*X 0 1+(-238438741/1250000000 : ℝ)*X 0 2+(743108091/1000000000 : ℝ)*X 1 0+(-1403527239/5000000000 : ℝ)*X 1 1+(-238438741/1250000000 : ℝ)*X 1 2+(743108091/1000000000 : ℝ)*X 2 0+(-1403527239/5000000000 : ℝ)*X 2 1+(-238438741/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-887705339/10000000000 : ℝ)*X 0 0+(-7084452429/10000000000 : ℝ)*X 0 1+(-100660991/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((958597187/2000000000 : ℝ)*X 1 0+(503453263/1250000000 : ℝ)*X 1 1+(-485798741/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4792986083/10000000000 : ℝ)*X 2 0+(-470975077/2000000000 : ℝ)*X 2 1+(168445607/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((7587167697/10000000000 : ℝ)*X 0 0+(-2071211999/10000000000 : ℝ)*X 0 1+(-2445970159/10000000000 : ℝ)*X 0 2+(7587167697/10000000000 : ℝ)*X 1 0+(-2071211999/10000000000 : ℝ)*X 1 1+(-2445970159/10000000000 : ℝ)*X 1 2+(7587167697/10000000000 : ℝ)*X 2 0+(-2071211999/10000000000 : ℝ)*X 2 1+(-2445970159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-3353419/2000000000 : ℝ)*X 0 0+(-420121247/625000000 : ℝ)*X 0 1+(-1218712143/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4458144351/10000000000 : ℝ)*X 1 0+(3159594923/10000000000 : ℝ)*X 1 1+(-5041588179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1488651439/2500000000 : ℝ)*X 2 0+(-158179123/625000000 : ℝ)*X 2 1+(2019180347/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((1127213903/1250000000 : ℝ)*X 0 0+(-1317591999/10000000000 : ℝ)*X 0 1+(-119442109/1250000000 : ℝ)*X 0 2+(1127213903/1250000000 : ℝ)*X 1 0+(-1317591999/10000000000 : ℝ)*X 1 1+(-119442109/1250000000 : ℝ)*X 1 2+(1127213903/1250000000 : ℝ)*X 2 0+(-1317591999/10000000000 : ℝ)*X 2 1+(-119442109/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-13193293/10000000000 : ℝ)*X 0 0+(-3665056871/5000000000 : ℝ)*X 0 1+(-418761839/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((2979089829/5000000000 : ℝ)*X 1 0+(284321779/1000000000 : ℝ)*X 1 1+(-3752926691/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((897322287/2000000000 : ℝ)*X 2 0+(-3539285159/10000000000 : ℝ)*X 2 1+(4671706047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((8952608077/10000000000 : ℝ)*X 0 0+(-754697211/5000000000 : ℝ)*X 0 1+(-215575367/2500000000 : ℝ)*X 0 2+(8952608077/10000000000 : ℝ)*X 1 0+(-754697211/5000000000 : ℝ)*X 1 1+(-215575367/2500000000 : ℝ)*X 1 2+(8952608077/10000000000 : ℝ)*X 2 0+(-754697211/5000000000 : ℝ)*X 2 1+(-215575367/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((2681/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2681/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (37963455603928594043979/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65783581073/125000000000 : ℝ)*(base39) + (237299865163/500000000000 : ℝ)*(base49) + (2651021742129/1000000000000 : ℝ)*(major_s0_0) + (2651021742129/1000000000000 : ℝ)*(major_s0_1) + (2651021742129/1000000000000 : ℝ)*(major_s0_2) + (278685071/1000000000000 : ℝ)*(sp_s0_0) + (202096029/1000000000000 : ℝ)*(sp_s0_6) + (115272043249/31250000000 : ℝ)*(sp_s0_7) + (3688902377319/1000000000000 : ℝ)*(sp_s0_8) + (3688892958129/1000000000000 : ℝ)*(sp_s0_9) + (100803234651/62500000000 : ℝ)*(sp_s0_13) + (82194697/1000000000000 : ℝ)*(sp_s0_15) + (7859/15625000000 : ℝ)*(sp_s0_20) + (45806943/500000000000 : ℝ)*(sp_s0_22) + (322610770089/200000000000 : ℝ)*(f.failure) + (737796914403/200000000000 : ℝ)*(f.sum) + (198214488978659/1000000000000000000000000000 : ℝ)*base62 + (173472364250363/625000000000000000000000000 : ℝ)*base64 + (54417889437863/625000000000000000000000000 : ℝ)*base67 + (770556968978659/2000000000000000000000000000 : ℝ)*base68 + (1467581977899103/10000000000000000000000000000 : ℝ)*base70 + (322315198562863/625000000000000000000000000 : ℝ)*base73 + (151764990021341/2000000000000000000000000000 : ℝ)*base75 + (212457121178659/2000000000000000000000000000 : ℝ)*base76 + (243182886562863/312500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1743/5000000000000000 : ℝ)*base87 + (1743/5000000000000000 : ℝ)*base89 + (1743/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-23123/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-23123/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23890587177181982258601/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1190773/1000000000000 : ℝ)*(base12) + (129282473403/62500000000 : ℝ)*(base39) + (181457367081/125000000000 : ℝ)*(base40) + (145657305317/200000000000 : ℝ)*(base49) + (2401123750657/500000000000 : ℝ)*(major_s0_0) + (2401123750657/500000000000 : ℝ)*(major_s0_1) + (2401123750657/500000000000 : ℝ)*(major_s0_2) + (12240581/100000000000 : ℝ)*(sp_s0_0) + (66930549/1000000000000 : ℝ)*(sp_s0_9) + (8352961081/1250000000 : ℝ)*(sp_s0_14) + (6682482921727/1000000000000 : ℝ)*(sp_s0_15) + (3341212765417/500000000000 : ℝ)*(sp_s0_16) + (2921999355827/1000000000000 : ℝ)*(sp_s0_19) + (1192457/125000000000 : ℝ)*(sp_s0_21) + (2921999355827/1000000000000 : ℝ)*(f.failure) + (3341246230691/500000000000 : ℝ)*(f.sum) + (168714034784147/500000000000000000000000000 : ℝ)*base62 + (64164014750471/312500000000000000000000000 : ℝ)*base65 + (173909203593279/312500000000000000000000000 : ℝ)*base67 + (494021056684147/1000000000000000000000000000 : ℝ)*base68 + (1703834281413199/5000000000000000000000000000 : ℝ)*base70 + (156882017312029/312500000000000000000000000 : ℝ)*base73 + (479290881284147/1000000000000000000000000000 : ℝ)*base74 + (224965464384147/1000000000000000000000000000 : ℝ)*base76 + (105951039593279/156250000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (13949/25000000000000000 : ℝ)*base87 + (13949/25000000000000000 : ℝ)*base89 + (13949/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-23501/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-23501/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19621640899476281883909/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2253783/200000000000 : ℝ)*(base10) + (2264906769749/1000000000000 : ℝ)*(base39) + (1204223323847/1000000000000 : ℝ)*(base40) + (382647296047/500000000000 : ℝ)*(base49) + (4883454507441/1000000000000 : ℝ)*(major_s0_0) + (4883454507441/1000000000000 : ℝ)*(major_s0_1) + (4883454507441/1000000000000 : ℝ)*(major_s0_2) + (20005453/1000000000000 : ℝ)*(sp_s0_2) + (43922673/1000000000000 : ℝ)*(sp_s0_7) + (9906549/500000000000 : ℝ)*(sp_s0_8) + (424715014571/62500000000 : ℝ)*(sp_s0_20) + (54363804893/8000000000 : ℝ)*(sp_s0_21) + (6795475419271/1000000000000 : ℝ)*(sp_s0_22) + (1485705486967/500000000000 : ℝ)*(sp_s0_25) + (1485705486967/500000000000 : ℝ)*(f.failure) + (6795495424723/1000000000000 : ℝ)*(f.sum) + (19851168784189/1000000000000000000000000000 : ℝ)*base63 + (407524023859073/625000000000000000000000000 : ℝ)*base65 + (74509170796573/625000000000000000000000000 : ℝ)*base66 + (270463701484189/2000000000000000000000000000 : ℝ)*base69 + (3726572116166113/10000000000000000000000000000 : ℝ)*base71 + (470813479609073/625000000000000000000000000 : ℝ)*base72 + (720057591315811/2000000000000000000000000000 : ℝ)*base74 + (1018300535684189/2000000000000000000000000000 : ℝ)*base77 + (388002871546573/312500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (629/12500000000000000 : ℝ)*base87 + (629/12500000000000000 : ℝ)*base89 + (629/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (2681/25000 : ℝ) ^ (71/16 : ℝ) ≤ (1244939745350357/25000000000000000000 : ℝ) := by
    have hpowers : (2681/25000 : ℝ)^71 ≤ (1244939745350357/25000000000000000000 : ℝ)^16 := by
      have hnat : (2681 : ℕ)^71*25000000000000000000^16 ≤ 1244939745350357^16*25000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2681 25000 1244939745350357 25000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2681/25000 : ℝ)) (X := (1244939745350357/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (25001244939745350357/25000000000000000000 : ℝ) ≤ (10000112217756297/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (25001244939745350357/25000000000000000000 : ℝ)^16 ≤ (10000112217756297/10000000000000000 : ℝ)^71 := by
      have hnat : (25001244939745350357 : ℕ)^16*10000000000000000^71 ≤ 10000112217756297^71*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001244939745350357 25000000000000000000 10000112217756297 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000112217756297/10000000000000000 : ℝ)) (X := (25001244939745350357/25000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (12501244939745350357/12500000000000000000 : ℝ) ≤ (400008977247361/400000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (12501244939745350357/12500000000000000000 : ℝ)^16 ≤ (400008977247361/400000000000000 : ℝ)^71 := by
      have hnat : (12501244939745350357 : ℕ)^16*400000000000000^71 ≤ 400008977247361^71*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501244939745350357 12500000000000000000 400008977247361 400000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400008977247361/400000000000000 : ℝ)) (X := (12501244939745350357/12500000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(112217756297/1072400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(7013339233/67025000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (2681/25000 : ℝ)) (alpha := (112217756297/1072400000000000 : ℝ)) (beta := (7013339233/67025000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2681/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(112217756297/1072400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(7013339233/67025000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (23123/50000 : ℝ) ^ (71/16 : ℝ) ≤ (326412401640013949/10000000000000000000 : ℝ) := by
    have hpowers : (23123/50000 : ℝ)^71 ≤ (326412401640013949/10000000000000000000 : ℝ)^16 := by
      have hnat : (23123 : ℕ)^71*10000000000000000000^16 ≤ 326412401640013949^16*50000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23123 50000 326412401640013949 10000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23123/50000 : ℝ)) (X := (326412401640013949/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (10326412401640013949/10000000000000000000 : ℝ) ≤ (10072645313484919/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (10326412401640013949/10000000000000000000 : ℝ)^16 ≤ (10072645313484919/10000000000000000 : ℝ)^71 := by
      have hnat : (10326412401640013949 : ℕ)^16*10000000000000000^71 ≤ 10072645313484919^71*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10326412401640013949 10000000000000000000 10072645313484919 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10072645313484919/10000000000000000 : ℝ)) (X := (10326412401640013949/10000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (5326412401640013949/5000000000000000000 : ℝ) ≤ (1014353301899623/1000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (5326412401640013949/5000000000000000000 : ℝ)^16 ≤ (1014353301899623/1000000000000000 : ℝ)^71 := by
      have hnat : (5326412401640013949 : ℕ)^16*1000000000000000^71 ≤ 1014353301899623^71*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5326412401640013949 5000000000000000000 1014353301899623 1000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1014353301899623/1000000000000000 : ℝ)) (X := (5326412401640013949/5000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(72645313484919/4624600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(70887705511311/4624600000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (23123/50000 : ℝ)) (alpha := (72645313484919/4624600000000000 : ℝ)) (beta := (70887705511311/4624600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (23123/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(72645313484919/4624600000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(70887705511311/4624600000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (23501/50000 : ℝ) ^ (71/16 : ℝ) ≤ (701529997503576241/20000000000000000000 : ℝ) := by
    have hpowers : (23501/50000 : ℝ)^71 ≤ (701529997503576241/20000000000000000000 : ℝ)^16 := by
      have hnat : (23501 : ℕ)^71*20000000000000000000^16 ≤ 701529997503576241^16*50000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23501 50000 701529997503576241 20000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23501/50000 : ℝ)) (X := (701529997503576241/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (20701529997503576241/20000000000000000000 : ℝ) ≤ (5038996738474307/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (20701529997503576241/20000000000000000000 : ℝ)^16 ≤ (5038996738474307/5000000000000000 : ℝ)^71 := by
      have hnat : (20701529997503576241 : ℕ)^16*5000000000000000^71 ≤ 5038996738474307^71*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20701529997503576241 20000000000000000000 5038996738474307 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5038996738474307/5000000000000000 : ℝ)) (X := (20701529997503576241/20000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (10701529997503576241/10000000000000000000 : ℝ) ≤ (2030793129273163/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (10701529997503576241/10000000000000000000 : ℝ)^16 ≤ (2030793129273163/2000000000000000 : ℝ)^71 := by
      have hnat : (10701529997503576241 : ℕ)^16*2000000000000000^71 ≤ 2030793129273163^71*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10701529997503576241 10000000000000000000 2030793129273163 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2030793129273163/2000000000000000 : ℝ)) (X := (10701529997503576241/10000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(38996738474307/2350100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(75972169417201/4700200000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (23501/50000 : ℝ)) (alpha := (38996738474307/2350100000000000 : ℝ)) (beta := (75972169417201/4700200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (23501/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(38996738474307/2350100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(75972169417201/4700200000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2355724719/10000000000 : ℝ)*X 0 0+(-713018821/1250000000 : ℝ)*X 0 1+(-27887507/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((954663853/2000000000 : ℝ)*X 1 0+(890339367/2500000000 : ℝ)*X 1 1+(-4362371599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2383454259/5000000000 : ℝ)*X 2 0+(-1782193507/5000000000 : ℝ)*X 2 1+(873216509/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5876284307/10000000000 : ℝ)*X 0 0+(-469631773/1250000000 : ℝ)*X 0 1+(-1469454547/5000000000 : ℝ)*X 0 2+(5876284307/10000000000 : ℝ)*X 1 0+(-469631773/1250000000 : ℝ)*X 1 1+(-1469454547/5000000000 : ℝ)*X 1 2+(5876284307/10000000000 : ℝ)*X 2 0+(-469631773/1250000000 : ℝ)*X 2 1+(-1469454547/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311044_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-85761/12500 : ℝ) < ((-41087/25000 : ℝ)*P 0+(-41087/25000 : ℝ)*P 1+(-41087/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-85761/12500 : ℝ) < (-14167969761115918810952322402076017/2081274176090000000000000000000000 : ℝ) := by norm_num
    linear_combination (2115463/1000000000000 : ℝ)*(base10) + (832047/1000000000000 : ℝ)*(base12) + (40179/500000000000 : ℝ)*(base25) + (895411/1000000000000 : ℝ)*(base27) + (818345373471/1000000000000 : ℝ)*(base39) + (229400757759/500000000000 : ℝ)*(base40) + (1559586417/5000000000 : ℝ)*(base49) + (91659/1000000000000 : ℝ)*(ratio_s0_2) + (41087/25000 : ℝ)*(major_s1_0) + (41087/25000 : ℝ)*(major_s1_1) + (41087/25000 : ℝ)*(major_s1_2) + (2269115000181/1000000000000 : ℝ)*(sp_s1_0) + (2269117947691/1000000000000 : ℝ)*(sp_s1_1) + (2269117867333/1000000000000 : ℝ)*(sp_s1_2) + (999999104589/1000000000000 : ℝ)*(sp_s1_6) + (2269117947691/1000000000000 : ℝ)*(f.sum) + (558426389451187033/1358534057500000000000000000000 : ℝ)*base62 + (2338826367051/14688125000000000000000000 : ℝ)*base64 + (32585328046789/115615000000000000000000000 : ℝ)*base67 + (80420319747469/117505000000000000000000000 : ℝ)*base68 + (79229635273827543/157515452500000000000000000000 : ℝ)*base70 + (356417319891/1072400000000000000000000 : ℝ)*base73 + (95134597650991/231230000000000000000000000 : ℝ)*base74 + (2699916657061/13405000000000000000000000 : ℝ)*base76 + (241221100936351203/619927630000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem rawFrame_weaken_k {p k k' A : ℝ} {X : Fin 3 → Fin 3 → ℝ}
    (hp : 1 ≤ p) (hX : RawFrame p k A X) (hk : k' ≤ k) : RawFrame p k' A X := by
  have f := raw_linear_data hp X hX
  have hs : (∑ i, lpNorm p (pair X i)) ≤ 6 := by
    rw [Fin.sum_univ_three]
    have hh := f.sum
    linarith only [f.Ptriangle 0,f.Ptriangle 1,f.Ptriangle 2,hh]
  refine ⟨hX.sum,hX.row_total,hX.total_one,hX.total_cap,?_⟩
  have hh := mul_le_mul_of_nonneg_right hk (sub_nonneg.mpr hs)
  linarith only [hh,hX.linear_failure]
theorem orderedChart_weaken {p k k' A A' d d' : ℝ}
    {X : Fin 3 → Fin 3 → ℝ} {orders : Fin 3 → Fin 3 → Fin 3}
    {signs : Fin 3 → Fin 3 → Bool} (hp : 1 ≤ p)
    (hX : OrderedChart p k A d X orders signs)
    (hk : k' ≤ k) (hA : A ≤ A') (hd : d' ≤ d) :
    OrderedChart p k' A' d' X orders signs := by
  have hr := rawFrame_weaken_k hp hX.raw hk
  refine ⟨⟨hr.sum,hr.row_total,hr.total_one,hr.total_cap.trans hA,hr.linear_failure⟩,
    hX.permutation,?_,hX.ordered⟩
  intro i
  exact (mul_le_mul_of_nonneg_right hd (lpNorm_nonneg p (pair X i))).trans (hX.main i)
end HlawkaSchatten.DiagonalCutoff4

namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p011_b024 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 43 ≤ c.val) (hhi : c.val < 46)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=43 ∨ c=44 ∨ c=45 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c311043 p hpa (by linarith only [hpb]) X hX
  · exact collision_c311044 p hpa (by linarith only [hpb]) X hX
  · exact collision_c310045 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (c : Fin 88) (hlo : 43 ≤ c.val) (hhi : c.val < 46)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p011_b024 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

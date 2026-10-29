-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p012_b015
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:23:12.600028+00:00
-- url     : https://prove2.me/submissions/de9e8b96-21ed-4372-aa77-987303296837

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312031_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312031_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c312031_s2
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c312031 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  have h0 := collision_c312031_s0 p hpa hpb X hX
  have h1 := collision_c312031_s1 p hpa hpb X hX h0
  exact collision_c312031_s2 p hpa hpb X hX h1

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
theorem collision_support_c312030_s0_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6969639833/10000000000 : ℝ)*x 0 + (-1096603921/10000000000 : ℝ)*x 1 + (-1994176781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6969639833/10000000000 : ℝ)^37 ≤ (12617926995551/20000000000000 : ℝ)^29 := by
    have hnat : (6969639833 : ℕ)^37*20000000000000^29 ≤ 12617926995551^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6969639833 10000000000 12617926995551 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096603921/10000000000 : ℝ)^37 ≤ (5959858442649/100000000000000 : ℝ)^29 := by
    have hnat : (1096603921 : ℕ)^37*100000000000000^29 ≤ 5959858442649^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096603921 10000000000 5959858442649 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1994176781/5000000000 : ℝ)^37 ≤ (30950506569989/100000000000000 : ℝ)^29 := by
    have hnat : (1994176781 : ℕ)^37*100000000000000^29 ≤ 30950506569989^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994176781 5000000000 30950506569989 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6969639833/10000000000 : ℝ), (-1096603921/10000000000 : ℝ), (-1994176781/5000000000 : ℝ)] ![(12617926995551/20000000000000 : ℝ), (5959858442649/100000000000000 : ℝ), (30950506569989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6969639833/10000000000 : ℝ)|^37 ≤ (12617926995551/20000000000000 : ℝ)^29
        have hw : |(6969639833/10000000000 : ℝ)|=(6969639833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1096603921/10000000000 : ℝ)|^37 ≤ (5959858442649/100000000000000 : ℝ)^29
        have hw : |(-1096603921/10000000000 : ℝ)|=(1096603921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1994176781/5000000000 : ℝ)|^37 ≤ (30950506569989/100000000000000 : ℝ)^29
        have hw : |(-1994176781/5000000000 : ℝ)|=(1994176781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312030_s0_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2655264319/10000000000 : ℝ)*x 0 + (2748094603/5000000000 : ℝ)*x 1 + (4390421347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655264319/10000000000 : ℝ)^37 ≤ (18417934942117/100000000000000 : ℝ)^29 := by
    have hnat : (2655264319 : ℕ)^37*100000000000000^29 ≤ 18417934942117^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655264319 10000000000 18417934942117 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2748094603/5000000000 : ℝ)^37 ≤ (5824579317003/12500000000000 : ℝ)^29 := by
    have hnat : (2748094603 : ℕ)^37*12500000000000^29 ≤ 5824579317003^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748094603 5000000000 5824579317003 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4390421347/10000000000 : ℝ)^37 ≤ (34985430502873/100000000000000 : ℝ)^29 := by
    have hnat : (4390421347 : ℕ)^37*100000000000000^29 ≤ 34985430502873^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4390421347 10000000000 34985430502873 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655264319/10000000000 : ℝ), (2748094603/5000000000 : ℝ), (4390421347/10000000000 : ℝ)] ![(18417934942117/100000000000000 : ℝ), (5824579317003/12500000000000 : ℝ), (34985430502873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655264319/10000000000 : ℝ)|^37 ≤ (18417934942117/100000000000000 : ℝ)^29
        have hw : |(2655264319/10000000000 : ℝ)|=(2655264319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2748094603/5000000000 : ℝ)|^37 ≤ (5824579317003/12500000000000 : ℝ)^29
        have hw : |(2748094603/5000000000 : ℝ)|=(2748094603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4390421347/10000000000 : ℝ)|^37 ≤ (34985430502873/100000000000000 : ℝ)^29
        have hw : |(4390421347/10000000000 : ℝ)|=(4390421347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312030_s0_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2744156443/10000000000 : ℝ)*x 0 + (3733262643/10000000000 : ℝ)*x 1 + (-6020801223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2744156443/10000000000 : ℝ)^37 ≤ (19208222364347/100000000000000 : ℝ)^29 := by
    have hnat : (2744156443 : ℕ)^37*100000000000000^29 ≤ 19208222364347^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744156443 10000000000 19208222364347 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3733262643/10000000000 : ℝ)^37 ≤ (5689498677043/20000000000000 : ℝ)^29 := by
    have hnat : (3733262643 : ℕ)^37*20000000000000^29 ≤ 5689498677043^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3733262643 10000000000 5689498677043 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6020801223/10000000000 : ℝ)^37 ≤ (5234428423033/10000000000000 : ℝ)^29 := by
    have hnat : (6020801223 : ℕ)^37*10000000000000^29 ≤ 5234428423033^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6020801223 10000000000 5234428423033 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2744156443/10000000000 : ℝ), (3733262643/10000000000 : ℝ), (-6020801223/10000000000 : ℝ)] ![(19208222364347/100000000000000 : ℝ), (5689498677043/20000000000000 : ℝ), (5234428423033/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2744156443/10000000000 : ℝ)|^37 ≤ (19208222364347/100000000000000 : ℝ)^29
        have hw : |(-2744156443/10000000000 : ℝ)|=(2744156443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3733262643/10000000000 : ℝ)|^37 ≤ (5689498677043/20000000000000 : ℝ)^29
        have hw : |(3733262643/10000000000 : ℝ)|=(3733262643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6020801223/10000000000 : ℝ)|^37 ≤ (5234428423033/10000000000000 : ℝ)^29
        have hw : |(-6020801223/10000000000 : ℝ)|=(6020801223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312030_s0_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (294868763/400000000 : ℝ)*x 0 + (-39700871/1250000000 : ℝ)*x 1 + (-1996870983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (294868763/400000000 : ℝ)^37 ≤ (16942443028669/25000000000000 : ℝ)^29 := by
    have hnat : (294868763 : ℕ)^37*25000000000000^29 ≤ 16942443028669^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294868763 400000000 16942443028669 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39700871/1250000000 : ℝ)^37 ≤ (153295115427/12500000000000 : ℝ)^29 := by
    have hnat : (39700871 : ℕ)^37*12500000000000^29 ≤ 153295115427^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39700871 1250000000 153295115427 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1996870983/5000000000 : ℝ)^37 ≤ (31003866946257/100000000000000 : ℝ)^29 := by
    have hnat : (1996870983 : ℕ)^37*100000000000000^29 ≤ 31003866946257^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996870983 5000000000 31003866946257 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(294868763/400000000 : ℝ), (-39700871/1250000000 : ℝ), (-1996870983/5000000000 : ℝ)] ![(16942443028669/25000000000000 : ℝ), (153295115427/12500000000000 : ℝ), (31003866946257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(294868763/400000000 : ℝ)|^37 ≤ (16942443028669/25000000000000 : ℝ)^29
        have hw : |(294868763/400000000 : ℝ)|=(294868763/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-39700871/1250000000 : ℝ)|^37 ≤ (153295115427/12500000000000 : ℝ)^29
        have hw : |(-39700871/1250000000 : ℝ)|=(39700871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1996870983/5000000000 : ℝ)|^37 ≤ (31003866946257/100000000000000 : ℝ)^29
        have hw : |(-1996870983/5000000000 : ℝ)|=(1996870983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312030_s0_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1652157147/10000000000 : ℝ)*x 0 + (6922667789/10000000000 : ℝ)*x 1 + (226556639/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1652157147/10000000000 : ℝ)^37 ≤ (5027028949969/50000000000000 : ℝ)^29 := by
    have hnat : (1652157147 : ℕ)^37*50000000000000^29 ≤ 5027028949969^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1652157147 10000000000 5027028949969 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6922667789/10000000000 : ℝ)^37 ≤ (62547651182863/100000000000000 : ℝ)^29 := by
    have hnat : (6922667789 : ℕ)^37*100000000000000^29 ≤ 62547651182863^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6922667789 10000000000 62547651182863 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226556639/625000000 : ℝ)^37 ≤ (1712393182157/6250000000000 : ℝ)^29 := by
    have hnat : (226556639 : ℕ)^37*6250000000000^29 ≤ 1712393182157^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226556639 625000000 1712393182157 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1652157147/10000000000 : ℝ), (6922667789/10000000000 : ℝ), (226556639/625000000 : ℝ)] ![(5027028949969/50000000000000 : ℝ), (62547651182863/100000000000000 : ℝ), (1712393182157/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1652157147/10000000000 : ℝ)|^37 ≤ (5027028949969/50000000000000 : ℝ)^29
        have hw : |(1652157147/10000000000 : ℝ)|=(1652157147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6922667789/10000000000 : ℝ)|^37 ≤ (62547651182863/100000000000000 : ℝ)^29
        have hw : |(6922667789/10000000000 : ℝ)|=(6922667789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226556639/625000000 : ℝ)|^37 ≤ (1712393182157/6250000000000 : ℝ)^29
        have hw : |(226556639/625000000 : ℝ)|=(226556639/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312030_s0_12 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1375155117/5000000000 : ℝ)*x 0 + (7723614623/10000000000 : ℝ)*x 1 + (-1490022787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1375155117/5000000000 : ℝ)^37 ≤ (1203949786041/6250000000000 : ℝ)^29 := by
    have hnat : (1375155117 : ℕ)^37*6250000000000^29 ≤ 1203949786041^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375155117 5000000000 1203949786041 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7723614623/10000000000 : ℝ)^37 ≤ (3596205972803/5000000000000 : ℝ)^29 := by
    have hnat : (7723614623 : ℕ)^37*5000000000000^29 ≤ 3596205972803^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7723614623 10000000000 3596205972803 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1490022787/10000000000 : ℝ)^37 ≤ (8812683959101/100000000000000 : ℝ)^29 := by
    have hnat : (1490022787 : ℕ)^37*100000000000000^29 ≤ 8812683959101^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1490022787 10000000000 8812683959101 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1375155117/5000000000 : ℝ), (7723614623/10000000000 : ℝ), (-1490022787/10000000000 : ℝ)] ![(1203949786041/6250000000000 : ℝ), (3596205972803/5000000000000 : ℝ), (8812683959101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1375155117/5000000000 : ℝ)|^37 ≤ (1203949786041/6250000000000 : ℝ)^29
        have hw : |(1375155117/5000000000 : ℝ)|=(1375155117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7723614623/10000000000 : ℝ)|^37 ≤ (3596205972803/5000000000000 : ℝ)^29
        have hw : |(7723614623/10000000000 : ℝ)|=(7723614623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1490022787/10000000000 : ℝ)|^37 ≤ (8812683959101/100000000000000 : ℝ)^29
        have hw : |(-1490022787/10000000000 : ℝ)|=(1490022787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312030_s0_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1800090443/5000000000 : ℝ)*x 0 + (917547451/2000000000 : ℝ)*x 1 + (-2236938049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1800090443/5000000000 : ℝ)^37 ≤ (6790019788513/25000000000000 : ℝ)^29 := by
    have hnat : (1800090443 : ℕ)^37*25000000000000^29 ≤ 6790019788513^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800090443 5000000000 6790019788513 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (917547451/2000000000 : ℝ)^37 ≤ (37003807224247/100000000000000 : ℝ)^29 := by
    have hnat : (917547451 : ℕ)^37*100000000000000^29 ≤ 37003807224247^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917547451 2000000000 37003807224247 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2236938049/5000000000 : ℝ)^37 ≤ (35836113606209/100000000000000 : ℝ)^29 := by
    have hnat : (2236938049 : ℕ)^37*100000000000000^29 ≤ 35836113606209^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236938049 5000000000 35836113606209 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1800090443/5000000000 : ℝ), (917547451/2000000000 : ℝ), (-2236938049/5000000000 : ℝ)] ![(6790019788513/25000000000000 : ℝ), (37003807224247/100000000000000 : ℝ), (35836113606209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1800090443/5000000000 : ℝ)|^37 ≤ (6790019788513/25000000000000 : ℝ)^29
        have hw : |(-1800090443/5000000000 : ℝ)|=(1800090443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(917547451/2000000000 : ℝ)|^37 ≤ (37003807224247/100000000000000 : ℝ)^29
        have hw : |(917547451/2000000000 : ℝ)|=(917547451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2236938049/5000000000 : ℝ)|^37 ≤ (35836113606209/100000000000000 : ℝ)^29
        have hw : |(-2236938049/5000000000 : ℝ)|=(2236938049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312030_s0_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3641990527/5000000000 : ℝ)*x 0 + (-288046467/2500000000 : ℝ)*x 1 + (-223383911/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3641990527/5000000000 : ℝ)^37 ≤ (13348472700997/20000000000000 : ℝ)^29 := by
    have hnat : (3641990527 : ℕ)^37*20000000000000^29 ≤ 13348472700997^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3641990527 5000000000 13348472700997 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (288046467/2500000000 : ℝ)^37 ≤ (3173965602449/50000000000000 : ℝ)^29 := by
    have hnat : (288046467 : ℕ)^37*50000000000000^29 ≤ 3173965602449^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288046467 2500000000 3173965602449 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223383911/625000000 : ℝ)^37 ≤ (13454852640677/50000000000000 : ℝ)^29 := by
    have hnat : (223383911 : ℕ)^37*50000000000000^29 ≤ 13454852640677^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223383911 625000000 13454852640677 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3641990527/5000000000 : ℝ), (-288046467/2500000000 : ℝ), (-223383911/625000000 : ℝ)] ![(13348472700997/20000000000000 : ℝ), (3173965602449/50000000000000 : ℝ), (13454852640677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3641990527/5000000000 : ℝ)|^37 ≤ (13348472700997/20000000000000 : ℝ)^29
        have hw : |(3641990527/5000000000 : ℝ)|=(3641990527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-288046467/2500000000 : ℝ)|^37 ≤ (3173965602449/50000000000000 : ℝ)^29
        have hw : |(-288046467/2500000000 : ℝ)|=(288046467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-223383911/625000000 : ℝ)|^37 ≤ (13454852640677/50000000000000 : ℝ)^29
        have hw : |(-223383911/625000000 : ℝ)|=(223383911/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312030_s0_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2036739149/10000000000 : ℝ)*x 0 + (5304020467/10000000000 : ℝ)*x 1 + (2549357799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2036739149/10000000000 : ℝ)^37 ≤ (3282743217081/25000000000000 : ℝ)^29 := by
    have hnat : (2036739149 : ℕ)^37*25000000000000^29 ≤ 3282743217081^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036739149 10000000000 3282743217081 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5304020467/10000000000 : ℝ)^37 ≤ (8905620926847/20000000000000 : ℝ)^29 := by
    have hnat : (5304020467 : ℕ)^37*20000000000000^29 ≤ 8905620926847^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304020467 10000000000 8905620926847 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2549357799/5000000000 : ℝ)^37 ≤ (21170461243297/50000000000000 : ℝ)^29 := by
    have hnat : (2549357799 : ℕ)^37*50000000000000^29 ≤ 21170461243297^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2549357799 5000000000 21170461243297 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2036739149/10000000000 : ℝ), (5304020467/10000000000 : ℝ), (2549357799/5000000000 : ℝ)] ![(3282743217081/25000000000000 : ℝ), (8905620926847/20000000000000 : ℝ), (21170461243297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2036739149/10000000000 : ℝ)|^37 ≤ (3282743217081/25000000000000 : ℝ)^29
        have hw : |(2036739149/10000000000 : ℝ)|=(2036739149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5304020467/10000000000 : ℝ)|^37 ≤ (8905620926847/20000000000000 : ℝ)^29
        have hw : |(5304020467/10000000000 : ℝ)|=(5304020467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2549357799/5000000000 : ℝ)|^37 ≤ (21170461243297/50000000000000 : ℝ)^29
        have hw : |(2549357799/5000000000 : ℝ)|=(2549357799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312030_s0_19 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3170173657/10000000000 : ℝ)*x 0 + (6578426103/10000000000 : ℝ)*x 1 + (-2642117937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3170173657/10000000000 : ℝ)^37 ≤ (23091428027683/100000000000000 : ℝ)^29 := by
    have hnat : (3170173657 : ℕ)^37*100000000000000^29 ≤ 23091428027683^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3170173657 10000000000 23091428027683 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6578426103/10000000000 : ℝ)^37 ≤ (58606901243627/100000000000000 : ℝ)^29 := by
    have hnat : (6578426103 : ℕ)^37*100000000000000^29 ≤ 58606901243627^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6578426103 10000000000 58606901243627 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2642117937/10000000000 : ℝ)^37 ≤ (3660334142939/20000000000000 : ℝ)^29 := by
    have hnat : (2642117937 : ℕ)^37*20000000000000^29 ≤ 3660334142939^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642117937 10000000000 3660334142939 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3170173657/10000000000 : ℝ), (6578426103/10000000000 : ℝ), (-2642117937/10000000000 : ℝ)] ![(23091428027683/100000000000000 : ℝ), (58606901243627/100000000000000 : ℝ), (3660334142939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3170173657/10000000000 : ℝ)|^37 ≤ (23091428027683/100000000000000 : ℝ)^29
        have hw : |(3170173657/10000000000 : ℝ)|=(3170173657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6578426103/10000000000 : ℝ)|^37 ≤ (58606901243627/100000000000000 : ℝ)^29
        have hw : |(6578426103/10000000000 : ℝ)|=(6578426103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2642117937/10000000000 : ℝ)|^37 ≤ (3660334142939/20000000000000 : ℝ)^29
        have hw : |(-2642117937/10000000000 : ℝ)|=(2642117937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312030_s0_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-250081097/1250000000 : ℝ)*x 0 + (5413975667/10000000000 : ℝ)*x 1 + (-5015000089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (250081097/1250000000 : ℝ)^37 ≤ (6417419101933/50000000000000 : ℝ)^29 := by
    have hnat : (250081097 : ℕ)^37*50000000000000^29 ≤ 6417419101933^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250081097 1250000000 6417419101933 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413975667/10000000000 : ℝ)^37 ≤ (45709193073783/100000000000000 : ℝ)^29 := by
    have hnat : (5413975667 : ℕ)^37*100000000000000^29 ≤ 45709193073783^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413975667 10000000000 45709193073783 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5015000089/10000000000 : ℝ)^37 ≤ (161937377771/390625000000 : ℝ)^29 := by
    have hnat : (5015000089 : ℕ)^37*390625000000^29 ≤ 161937377771^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5015000089 10000000000 161937377771 390625000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-250081097/1250000000 : ℝ), (5413975667/10000000000 : ℝ), (-5015000089/10000000000 : ℝ)] ![(6417419101933/50000000000000 : ℝ), (45709193073783/100000000000000 : ℝ), (161937377771/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-250081097/1250000000 : ℝ)|^37 ≤ (6417419101933/50000000000000 : ℝ)^29
        have hw : |(-250081097/1250000000 : ℝ)|=(250081097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413975667/10000000000 : ℝ)|^37 ≤ (45709193073783/100000000000000 : ℝ)^29
        have hw : |(5413975667/10000000000 : ℝ)|=(5413975667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5015000089/10000000000 : ℝ)|^37 ≤ (161937377771/390625000000 : ℝ)^29
        have hw : |(-5015000089/10000000000 : ℝ)|=(5015000089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312030_s0_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2079741039/2500000000 : ℝ)*x 0 + (-535625143/10000000000 : ℝ)*x 1 + (-133450589/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079741039/2500000000 : ℝ)^37 ≤ (9883924170499/12500000000000 : ℝ)^29 := by
    have hnat : (2079741039 : ℕ)^37*12500000000000^29 ≤ 9883924170499^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079741039 2500000000 9883924170499 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535625143/10000000000 : ℝ)^37 ≤ (2388921661261/100000000000000 : ℝ)^29 := by
    have hnat : (535625143 : ℕ)^37*100000000000000^29 ≤ 2388921661261^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535625143 10000000000 2388921661261 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133450589/500000000 : ℝ)^37 ≤ (18539684962531/100000000000000 : ℝ)^29 := by
    have hnat : (133450589 : ℕ)^37*100000000000000^29 ≤ 18539684962531^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133450589 500000000 18539684962531 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2079741039/2500000000 : ℝ), (-535625143/10000000000 : ℝ), (-133450589/500000000 : ℝ)] ![(9883924170499/12500000000000 : ℝ), (2388921661261/100000000000000 : ℝ), (18539684962531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2079741039/2500000000 : ℝ)|^37 ≤ (9883924170499/12500000000000 : ℝ)^29
        have hw : |(2079741039/2500000000 : ℝ)|=(2079741039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-535625143/10000000000 : ℝ)|^37 ≤ (2388921661261/100000000000000 : ℝ)^29
        have hw : |(-535625143/10000000000 : ℝ)|=(535625143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133450589/500000000 : ℝ)|^37 ≤ (18539684962531/100000000000000 : ℝ)^29
        have hw : |(-133450589/500000000 : ℝ)|=(133450589/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312030_s0_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (468165747/2500000000 : ℝ)*x 0 + (5817577999/10000000000 : ℝ)*x 1 + (469417979/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (468165747/2500000000 : ℝ)^37 ≤ (11796653806487/100000000000000 : ℝ)^29 := by
    have hnat : (468165747 : ℕ)^37*100000000000000^29 ≤ 11796653806487^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468165747 2500000000 11796653806487 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5817577999/10000000000 : ℝ)^37 ≤ (25050333942161/50000000000000 : ℝ)^29 := by
    have hnat : (5817577999 : ℕ)^37*50000000000000^29 ≤ 25050333942161^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5817577999 10000000000 25050333942161 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (469417979/1000000000 : ℝ)^37 ≤ (38102678295537/100000000000000 : ℝ)^29 := by
    have hnat : (469417979 : ℕ)^37*100000000000000^29 ≤ 38102678295537^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469417979 1000000000 38102678295537 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(468165747/2500000000 : ℝ), (5817577999/10000000000 : ℝ), (469417979/1000000000 : ℝ)] ![(11796653806487/100000000000000 : ℝ), (25050333942161/50000000000000 : ℝ), (38102678295537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(468165747/2500000000 : ℝ)|^37 ≤ (11796653806487/100000000000000 : ℝ)^29
        have hw : |(468165747/2500000000 : ℝ)|=(468165747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5817577999/10000000000 : ℝ)|^37 ≤ (25050333942161/50000000000000 : ℝ)^29
        have hw : |(5817577999/10000000000 : ℝ)|=(5817577999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(469417979/1000000000 : ℝ)|^37 ≤ (38102678295537/100000000000000 : ℝ)^29
        have hw : |(469417979/1000000000 : ℝ)|=(469417979/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312030_s0_25 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2436944659/5000000000 : ℝ)*x 0 + (1466968977/2500000000 : ℝ)*x 1 + (-195464059/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2436944659/5000000000 : ℝ)^37 ≤ (3997352034947/10000000000000 : ℝ)^29 := by
    have hnat : (2436944659 : ℕ)^37*10000000000000^29 ≤ 3997352034947^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2436944659 5000000000 3997352034947 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1466968977/2500000000 : ℝ)^37 ≤ (50653981660409/100000000000000 : ℝ)^29 := by
    have hnat : (1466968977 : ℕ)^37*100000000000000^29 ≤ 50653981660409^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1466968977 2500000000 50653981660409 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (195464059/1250000000 : ℝ)^37 ≤ (468624898743/5000000000000 : ℝ)^29 := by
    have hnat : (195464059 : ℕ)^37*5000000000000^29 ≤ 468624898743^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195464059 1250000000 468624898743 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2436944659/5000000000 : ℝ), (1466968977/2500000000 : ℝ), (-195464059/1250000000 : ℝ)] ![(3997352034947/10000000000000 : ℝ), (50653981660409/100000000000000 : ℝ), (468624898743/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2436944659/5000000000 : ℝ)|^37 ≤ (3997352034947/10000000000000 : ℝ)^29
        have hw : |(2436944659/5000000000 : ℝ)|=(2436944659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1466968977/2500000000 : ℝ)|^37 ≤ (50653981660409/100000000000000 : ℝ)^29
        have hw : |(1466968977/2500000000 : ℝ)|=(1466968977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-195464059/1250000000 : ℝ)|^37 ≤ (468624898743/5000000000000 : ℝ)^29
        have hw : |(-195464059/1250000000 : ℝ)|=(195464059/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312030_s1_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-884639297/2500000000 : ℝ)*x 0 + (463951537/1000000000 : ℝ)*x 1 + (-2239778453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (884639297/2500000000 : ℝ)^37 ≤ (6642086004539/25000000000000 : ℝ)^29 := by
    have hnat : (884639297 : ℕ)^37*25000000000000^29 ≤ 6642086004539^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884639297 2500000000 6642086004539 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (463951537/1000000000 : ℝ)^37 ≤ (37537475703431/100000000000000 : ℝ)^29 := by
    have hnat : (463951537 : ℕ)^37*100000000000000^29 ≤ 37537475703431^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463951537 1000000000 37537475703431 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239778453/5000000000 : ℝ)^37 ≤ (17947090131537/50000000000000 : ℝ)^29 := by
    have hnat : (2239778453 : ℕ)^37*50000000000000^29 ≤ 17947090131537^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239778453 5000000000 17947090131537 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-884639297/2500000000 : ℝ), (463951537/1000000000 : ℝ), (-2239778453/5000000000 : ℝ)] ![(6642086004539/25000000000000 : ℝ), (37537475703431/100000000000000 : ℝ), (17947090131537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-884639297/2500000000 : ℝ)|^37 ≤ (6642086004539/25000000000000 : ℝ)^29
        have hw : |(-884639297/2500000000 : ℝ)|=(884639297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(463951537/1000000000 : ℝ)|^37 ≤ (37537475703431/100000000000000 : ℝ)^29
        have hw : |(463951537/1000000000 : ℝ)|=(463951537/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2239778453/5000000000 : ℝ)|^37 ≤ (17947090131537/50000000000000 : ℝ)^29
        have hw : |(-2239778453/5000000000 : ℝ)|=(2239778453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312030_s1_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2850240523/5000000000 : ℝ)*x 0 + (-252737263/1000000000 : ℝ)*x 1 + (-2141085987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2850240523/5000000000 : ℝ)^37 ≤ (48817636471487/100000000000000 : ℝ)^29 := by
    have hnat : (2850240523 : ℕ)^37*100000000000000^29 ≤ 48817636471487^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850240523 5000000000 48817636471487 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252737263/1000000000 : ℝ)^37 ≤ (8646859324971/50000000000000 : ℝ)^29 := by
    have hnat : (252737263 : ℕ)^37*50000000000000^29 ≤ 8646859324971^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252737263 1000000000 8646859324971 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2141085987/5000000000 : ℝ)^37 ≤ (16944322431503/50000000000000 : ℝ)^29 := by
    have hnat : (2141085987 : ℕ)^37*50000000000000^29 ≤ 16944322431503^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141085987 5000000000 16944322431503 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2850240523/5000000000 : ℝ), (-252737263/1000000000 : ℝ), (-2141085987/5000000000 : ℝ)] ![(48817636471487/100000000000000 : ℝ), (8646859324971/50000000000000 : ℝ), (16944322431503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2850240523/5000000000 : ℝ)|^37 ≤ (48817636471487/100000000000000 : ℝ)^29
        have hw : |(2850240523/5000000000 : ℝ)|=(2850240523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-252737263/1000000000 : ℝ)|^37 ≤ (8646859324971/50000000000000 : ℝ)^29
        have hw : |(-252737263/1000000000 : ℝ)|=(252737263/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2141085987/5000000000 : ℝ)|^37 ≤ (16944322431503/50000000000000 : ℝ)^29
        have hw : |(-2141085987/5000000000 : ℝ)|=(2141085987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312030_s1_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (428676779/1250000000 : ℝ)*x 0 + (2437493213/5000000000 : ℝ)*x 1 + (868277967/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428676779/1250000000 : ℝ)^37 ≤ (25527292722547/100000000000000 : ℝ)^29 := by
    have hnat : (428676779 : ℕ)^37*100000000000000^29 ≤ 25527292722547^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428676779 1250000000 25527292722547 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2437493213/5000000000 : ℝ)^37 ≤ (19992500458079/50000000000000 : ℝ)^29 := by
    have hnat : (2437493213 : ℕ)^37*50000000000000^29 ≤ 19992500458079^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2437493213 5000000000 19992500458079 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (868277967/2000000000 : ℝ)^37 ≤ (6897541269337/20000000000000 : ℝ)^29 := by
    have hnat : (868277967 : ℕ)^37*20000000000000^29 ≤ 6897541269337^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      868277967 2000000000 6897541269337 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(428676779/1250000000 : ℝ), (2437493213/5000000000 : ℝ), (868277967/2000000000 : ℝ)] ![(25527292722547/100000000000000 : ℝ), (19992500458079/50000000000000 : ℝ), (6897541269337/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(428676779/1250000000 : ℝ)|^37 ≤ (25527292722547/100000000000000 : ℝ)^29
        have hw : |(428676779/1250000000 : ℝ)|=(428676779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2437493213/5000000000 : ℝ)|^37 ≤ (19992500458079/50000000000000 : ℝ)^29
        have hw : |(2437493213/5000000000 : ℝ)|=(2437493213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(868277967/2000000000 : ℝ)|^37 ≤ (6897541269337/20000000000000 : ℝ)^29
        have hw : |(868277967/2000000000 : ℝ)|=(868277967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312030_s1_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2022811709/5000000000 : ℝ)*x 0 + (2748317591/5000000000 : ℝ)*x 1 + (-1519525727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2022811709/5000000000 : ℝ)^37 ≤ (3939831624499/12500000000000 : ℝ)^29 := by
    have hnat : (2022811709 : ℕ)^37*12500000000000^29 ≤ 3939831624499^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022811709 5000000000 3939831624499 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2748317591/5000000000 : ℝ)^37 ≤ (46601458598799/100000000000000 : ℝ)^29 := by
    have hnat : (2748317591 : ℕ)^37*100000000000000^29 ≤ 46601458598799^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748317591 5000000000 46601458598799 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1519525727/5000000000 : ℝ)^37 ≤ (21879888389279/100000000000000 : ℝ)^29 := by
    have hnat : (1519525727 : ℕ)^37*100000000000000^29 ≤ 21879888389279^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1519525727 5000000000 21879888389279 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2022811709/5000000000 : ℝ), (2748317591/5000000000 : ℝ), (-1519525727/5000000000 : ℝ)] ![(3939831624499/12500000000000 : ℝ), (46601458598799/100000000000000 : ℝ), (21879888389279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2022811709/5000000000 : ℝ)|^37 ≤ (3939831624499/12500000000000 : ℝ)^29
        have hw : |(2022811709/5000000000 : ℝ)|=(2022811709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2748317591/5000000000 : ℝ)|^37 ≤ (46601458598799/100000000000000 : ℝ)^29
        have hw : |(2748317591/5000000000 : ℝ)|=(2748317591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1519525727/5000000000 : ℝ)|^37 ≤ (21879888389279/100000000000000 : ℝ)^29
        have hw : |(-1519525727/5000000000 : ℝ)|=(1519525727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312030 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base25 : ((1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(832645197880583/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (9/2 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^9 ≤ (1 : ℝ)^2 := by
      have hnat : (1 : ℕ)^9*1^2 ≤ 1^2*1^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5832645197880583/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2 : ℝ)^2 ≤ (5832645197880583/5000000000000000 : ℝ)^9 := by
      have hnat : (2 : ℕ)^2*5000000000000000^9 ≤ 5832645197880583^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5832645197880583 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5832645197880583/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12765180070092417/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (3 : ℝ)^2 ≤ (12765180070092417/10000000000000000 : ℝ)^9 := by
      have hnat : (3 : ℕ)^2*10000000000000000^9 ≤ 12765180070092417^9*1^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12765180070092417 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12765180070092417/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (1 : ℝ)) (alpha := (832645197880583/5000000000000000 : ℝ)) (beta := (1099889674331251/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(832645197880583/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1099889674331251/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((6969639833/10000000000 : ℝ)*X 1 0+(-1096603921/10000000000 : ℝ)*X 1 1+(-1994176781/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312030_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2655264319/10000000000 : ℝ)*X 2 0+(2748094603/5000000000 : ℝ)*X 2 1+(4390421347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312030_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2744156443/10000000000 : ℝ)*X 0 0+(3733262643/10000000000 : ℝ)*X 0 1+(-6020801223/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312030_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((294868763/400000000 : ℝ)*X 1 0+(-39700871/1250000000 : ℝ)*X 1 1+(-1996870983/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312030_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1652157147/10000000000 : ℝ)*X 2 0+(6922667789/10000000000 : ℝ)*X 2 1+(226556639/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312030_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((1375155117/5000000000 : ℝ)*X 0 0+(7723614623/10000000000 : ℝ)*X 0 1+(-1490022787/10000000000 : ℝ)*X 0 2+(1375155117/5000000000 : ℝ)*X 1 0+(7723614623/10000000000 : ℝ)*X 1 1+(-1490022787/10000000000 : ℝ)*X 1 2+(1375155117/5000000000 : ℝ)*X 2 0+(7723614623/10000000000 : ℝ)*X 2 1+(-1490022787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312030_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-1800090443/5000000000 : ℝ)*X 0 0+(917547451/2000000000 : ℝ)*X 0 1+(-2236938049/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312030_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((3641990527/5000000000 : ℝ)*X 1 0+(-288046467/2500000000 : ℝ)*X 1 1+(-223383911/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312030_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((2036739149/10000000000 : ℝ)*X 2 0+(5304020467/10000000000 : ℝ)*X 2 1+(2549357799/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312030_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((3170173657/10000000000 : ℝ)*X 0 0+(6578426103/10000000000 : ℝ)*X 0 1+(-2642117937/10000000000 : ℝ)*X 0 2+(3170173657/10000000000 : ℝ)*X 1 0+(6578426103/10000000000 : ℝ)*X 1 1+(-2642117937/10000000000 : ℝ)*X 1 2+(3170173657/10000000000 : ℝ)*X 2 0+(6578426103/10000000000 : ℝ)*X 2 1+(-2642117937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312030_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-250081097/1250000000 : ℝ)*X 0 0+(5413975667/10000000000 : ℝ)*X 0 1+(-5015000089/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312030_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((2079741039/2500000000 : ℝ)*X 1 0+(-535625143/10000000000 : ℝ)*X 1 1+(-133450589/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312030_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((468165747/2500000000 : ℝ)*X 2 0+(5817577999/10000000000 : ℝ)*X 2 1+(469417979/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312030_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((2436944659/5000000000 : ℝ)*X 0 0+(1466968977/2500000000 : ℝ)*X 0 1+(-195464059/1250000000 : ℝ)*X 0 2+(2436944659/5000000000 : ℝ)*X 1 0+(1466968977/2500000000 : ℝ)*X 1 1+(-195464059/1250000000 : ℝ)*X 1 2+(2436944659/5000000000 : ℝ)*X 2 0+(1466968977/2500000000 : ℝ)*X 2 1+(-195464059/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312030_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((2193/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2193/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4189808254196177532501/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (90704840761/100000000000 : ℝ)*(base39) + (1132434985047/1000000000000 : ℝ)*(base49) + (258595740813/200000000000 : ℝ)*(base50) + (233596869359/500000000000 : ℝ)*(base60) + (751912362083/200000000000 : ℝ)*(major_s0_0) + (751912362083/200000000000 : ℝ)*(major_s0_1) + (751912362083/200000000000 : ℝ)*(major_s0_2) + (37797707/500000000000 : ℝ)*(sp_s0_1) + (2633347413781/500000000000 : ℝ)*(sp_s0_7) + (2633318602511/500000000000 : ℝ)*(sp_s0_8) + (2633331807683/500000000000 : ℝ)*(sp_s0_9) + (450481605437/200000000000 : ℝ)*(sp_s0_12) + (143783/8000000000 : ℝ)*(sp_s0_20) + (4918507/100000000000 : ℝ)*(sp_s0_22) + (450481605437/200000000000 : ℝ)*(f.failure) + (1316678200109/250000000000 : ℝ)*(f.sum) + (312369581/2500000000000000000000 : ℝ)*base62 + (91567745155833/2000000000000000000000000000 : ℝ)*base65 + (1143304553555833/2000000000000000000000000000 : ℝ)*base67 + (6434289065611/1000000000000000000000000000 : ℝ)*base68 + (382027643624611/2000000000000000000000000000 : ℝ)*base71 + (1013330702644167/2000000000000000000000000000 : ℝ)*base72 + (283608983665611/1000000000000000000000000000 : ℝ)*base75 + (230864195234389/1000000000000000000000000000 : ℝ)*base77 + (237181925455833/1000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (5981/20000000000000000 : ℝ)*base87 + (5981/20000000000000000 : ℝ)*base89 + (5981/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(8201/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(8201/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (77669863686283580848491/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (886269/62500000000 : ℝ)*(base3) + (8061375171/12500000000 : ℝ)*(base39) + (293064907577/1000000000000 : ℝ)*(base49) + (24456107667/200000000000 : ℝ)*(base60) + (2791592218759/1000000000000 : ℝ)*(major_s0_0) + (2791592218759/1000000000000 : ℝ)*(major_s0_1) + (2791592218759/1000000000000 : ℝ)*(major_s0_2) + (83920597/1000000000000 : ℝ)*(sp_s0_1) + (4083353/100000000000 : ℝ)*(sp_s0_2) + (113570611/1000000000000 : ℝ)*(sp_s0_8) + (1955347929367/500000000000 : ℝ)*(sp_s0_13) + (3910512547829/1000000000000 : ℝ)*(sp_s0_14) + (977663756301/250000000000 : ℝ)*(sp_s0_15) + (334493844097/200000000000 : ℝ)*(sp_s0_19) + (1672483400789/1000000000000 : ℝ)*(f.failure) + (1955347929367/500000000000 : ℝ)*(f.sum) + (1368805321/10000000000000000000000 : ℝ)*base62 + (5715653497137509/10000000000000000000000000000 : ℝ)*base65 + (2055612000862491/10000000000000000000000000000 : ℝ)*base66 + (2630781025956497/5000000000000000000000000000 : ℝ)*base69 + (3255550113050503/10000000000000000000000000000 : ℝ)*base71 + (4592406688862491/10000000000000000000000000000 : ℝ)*base72 + (1182653150043503/5000000000000000000000000000 : ℝ)*base75 + (1567277592956497/5000000000000000000000000000 : ℝ)*base77 + (152429893637509/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (5643/100000000000000000 : ℝ)*base86 + (5643/100000000000000000 : ℝ)*base88 + (5643/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5923/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5923/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4616284561123156553001/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (59033/10000000000 : ℝ)*(base11) + (289044928009/250000000000 : ℝ)*(base39) + (30810653269/31250000000 : ℝ)*(base49) + (191931304577/200000000000 : ℝ)*(base50) + (859511077249/250000000000 : ℝ)*(major_s0_0) + (859511077249/250000000000 : ℝ)*(major_s0_1) + (859511077249/250000000000 : ℝ)*(major_s0_2) + (28341141/250000000000 : ℝ)*(sp_s0_2) + (59484603/1000000000000 : ℝ)*(sp_s0_9) + (889433/200000000000 : ℝ)*(sp_s0_14) + (4816295563379/1000000000000 : ℝ)*(sp_s0_20) + (2408148509757/500000000000 : ℝ)*(sp_s0_21) + (602016077189/125000000000 : ℝ)*(sp_s0_22) + (411956445453/200000000000 : ℝ)*(sp_s0_25) + (411956445453/200000000000 : ℝ)*(f.failure) + (4816301466679/1000000000000 : ℝ)*(f.sum) + (2647459417/5000000000000000000000 : ℝ)*base63 + (2296198072558499/2500000000000000000000000000 : ℝ)*base65 + (557603128558499/2500000000000000000000000000 : ℝ)*base67 + (879865069656167/1250000000000000000000000000 : ℝ)*base69 + (961530931620833/2500000000000000000000000000 : ℝ)*base71 + (58714064191501/2500000000000000000000000000 : ℝ)*base72 + (1044083924468833/1250000000000000000000000000 : ℝ)*base75 + (909066107781167/1250000000000000000000000000 : ℝ)*base77 + (1170661903308499/1250000000000000000000000000 : ℝ)*base79 + (23411/20000000000000000 : ℝ)*base86 + (23411/20000000000000000 : ℝ)*base88 + (23411/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (2193/6250 : ℝ) ^ (9/2 : ℝ) ≤ (897870627510910633/100000000000000000000 : ℝ) := by
    have hpowers : (2193/6250 : ℝ)^9 ≤ (897870627510910633/100000000000000000000 : ℝ)^2 := by
      have hnat : (2193 : ℕ)^9*100000000000000000000^2 ≤ 897870627510910633^2*6250^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2193 6250 897870627510910633 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2193/6250 : ℝ)) (X := (897870627510910633/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100897870627510910633/100000000000000000000 : ℝ) ≤ (10019883379849179/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (100897870627510910633/100000000000000000000 : ℝ)^2 ≤ (10019883379849179/10000000000000000 : ℝ)^9 := by
      have hnat : (100897870627510910633 : ℕ)^2*10000000000000000^9 ≤ 10019883379849179^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100897870627510910633 100000000000000000000 10019883379849179 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10019883379849179/10000000000000000 : ℝ)) (X := (100897870627510910633/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50897870627510910633/50000000000000000000 : ℝ) ≤ (5019814806814659/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (50897870627510910633/50000000000000000000 : ℝ)^2 ≤ (5019814806814659/5000000000000000 : ℝ)^9 := by
      have hnat : (50897870627510910633 : ℕ)^2*5000000000000000^9 ≤ 5019814806814659^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50897870627510910633 50000000000000000000 5019814806814659 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5019814806814659/5000000000000000 : ℝ)) (X := (50897870627510910633/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(19883379849179/3508800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(153071579691/27200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (2193/6250 : ℝ)) (alpha := (19883379849179/3508800000000000 : ℝ)) (beta := (153071579691/27200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2193/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(19883379849179/3508800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(153071579691/27200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (8201/100000 : ℝ) ^ (9/2 : ℝ) ≤ (323847584574227/25000000000000000000 : ℝ) := by
    have hpowers : (8201/100000 : ℝ)^9 ≤ (323847584574227/25000000000000000000 : ℝ)^2 := by
      have hnat : (8201 : ℕ)^9*25000000000000000000^2 ≤ 323847584574227^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8201 100000 323847584574227 25000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8201/100000 : ℝ)) (X := (323847584574227/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1a : (25000323847584574227/25000000000000000000 : ℝ) ≤ (2500007196576737/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (25000323847584574227/25000000000000000000 : ℝ)^2 ≤ (2500007196576737/2500000000000000 : ℝ)^9 := by
      have hnat : (25000323847584574227 : ℕ)^2*2500000000000000^9 ≤ 2500007196576737^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000323847584574227 25000000000000000000 2500007196576737 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500007196576737/2500000000000000 : ℝ)) (X := (25000323847584574227/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1b : (12500323847584574227/12500000000000000000 : ℝ) ≤ (312501799135121/312500000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (12500323847584574227/12500000000000000000 : ℝ)^2 ≤ (312501799135121/312500000000000 : ℝ)^9 := by
      have hnat : (12500323847584574227 : ℕ)^2*312500000000000^9 ≤ 312501799135121^9*12500000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500323847584574227 12500000000000000000 312501799135121 312500000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312501799135121/312500000000000 : ℝ)) (X := (12500323847584574227/12500000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(7196576737/205025000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(7196504231/205025000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (8201/100000 : ℝ)) (alpha := (7196576737/205025000000000 : ℝ)) (beta := (7196504231/205025000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (8201/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(7196576737/205025000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(7196504231/205025000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (5923/20000 : ℝ) ^ (9/2 : ℝ) ≤ (209301731293246157/50000000000000000000 : ℝ) := by
    have hpowers : (5923/20000 : ℝ)^9 ≤ (209301731293246157/50000000000000000000 : ℝ)^2 := by
      have hnat : (5923 : ℕ)^9*50000000000000000000^2 ≤ 209301731293246157^2*20000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5923 20000 209301731293246157 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5923/20000 : ℝ)) (X := (209301731293246157/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50209301731293246157/50000000000000000000 : ℝ) ≤ (5004643596694761/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (50209301731293246157/50000000000000000000 : ℝ)^2 ≤ (5004643596694761/5000000000000000 : ℝ)^9 := by
      have hnat : (50209301731293246157 : ℕ)^2*5000000000000000^9 ≤ 5004643596694761^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50209301731293246157 50000000000000000000 5004643596694761 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004643596694761/5000000000000000 : ℝ)) (X := (50209301731293246157/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25209301731293246157/25000000000000000000 : ℝ) ≤ (10018544324178153/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (25209301731293246157/25000000000000000000 : ℝ)^2 ≤ (10018544324178153/10000000000000000 : ℝ)^9 := by
      have hnat : (25209301731293246157 : ℕ)^2*10000000000000000^9 ≤ 10018544324178153^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25209301731293246157 25000000000000000000 10018544324178153 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10018544324178153/10000000000000000 : ℝ)) (X := (25209301731293246157/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(4643596694761/1480750000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(9257130788631/2961500000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (5923/20000 : ℝ)) (alpha := (4643596694761/1480750000000000 : ℝ)) (beta := (9257130788631/2961500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (5923/20000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(4643596694761/1480750000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(9257130788631/2961500000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-884639297/2500000000 : ℝ)*X 0 0+(463951537/1000000000 : ℝ)*X 0 1+(-2239778453/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312030_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2850240523/5000000000 : ℝ)*X 1 0+(-252737263/1000000000 : ℝ)*X 1 1+(-2141085987/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312030_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((428676779/1250000000 : ℝ)*X 2 0+(2437493213/5000000000 : ℝ)*X 2 1+(868277967/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312030_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2022811709/5000000000 : ℝ)*X 0 0+(2748317591/5000000000 : ℝ)*X 0 1+(-1519525727/5000000000 : ℝ)*X 0 2+(2022811709/5000000000 : ℝ)*X 1 0+(2748317591/5000000000 : ℝ)*X 1 1+(-1519525727/5000000000 : ℝ)*X 1 2+(2022811709/5000000000 : ℝ)*X 2 0+(2748317591/5000000000 : ℝ)*X 2 1+(-1519525727/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312030_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-350739/50000 : ℝ) < ((-166913/100000 : ℝ)*P 0+(-166913/100000 : ℝ)*P 1+(-166913/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-350739/50000 : ℝ) < (-49336565501719542826032951593537/7101595262600000000000000000000 : ℝ) := by norm_num
    linear_combination (129607/62500000000 : ℝ)*(base15) + (1037811/1000000000000 : ℝ)*(base25) + (364188382749/1000000000000 : ℝ)*(base39) + (199538885891/250000000000 : ℝ)*(base49) + (470342810433/1000000000000 : ℝ)*(base50) + (50287948149/1000000000000 : ℝ)*(base60) + (79057/250000000000 : ℝ)*(ratio_s0_0) + (35151/500000000000 : ℝ)*(ratio_s0_2) + (166913/100000 : ℝ)*(major_s1_0) + (166913/100000 : ℝ)*(major_s1_1) + (166913/100000 : ℝ)*(major_s1_2) + (2315750366749/1000000000000 : ℝ)*(sp_s1_0) + (1157874146519/500000000000 : ℝ)*(sp_s1_1) + (1157874664469/500000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2315750366749/1000000000000 : ℝ)*(f.sum) + (51680462228636081/121436307500000000000000000000 : ℝ)*base62 + (3291305509401/5923000000000000000000000 : ℝ)*base65 + (1829523594697/41005000000000000000000000 : ℝ)*base67 + (9831304935351/14807500000000000000000000 : ℝ)*base68 + (278472251518013/405910593750000000000000000 : ℝ)*base71 + (3349102397/5312500000000000000000 : ℝ)*base73 + (1903197393551/5125625000000000000000000 : ℝ)*base74 + (373203045377/2741250000000000000000000 : ℝ)*base77 + (108929050185659/139417000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p012_b015 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 30 ≤ c.val) (hhi : c.val < 32)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=30 ∨ c=31 := by omega
  rcases hc with rfl|rfl
  · exact collision_c312030 p hpa (by linarith only [hpb]) X hX
  · exact collision_c312031 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (c : Fin 88) (hlo : 30 ≤ c.val) (hhi : c.val < 32)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p012_b015 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

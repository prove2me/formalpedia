-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p016_b015
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:10:02.318377+00:00
-- url     : https://prove2.me/submissions/9aac1740-4509-473c-8ad3-ab7d468486d6

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316031_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316031_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c316031_s2
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c316031 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  have h0 := collision_c316031_s0 p hpa hpb X hX
  have h1 := collision_c316031_s1 p hpa hpb X hX h0
  exact collision_c316031_s2 p hpa hpb X hX h1

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
theorem collision_support_c316030_s0_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (86660999/125000000 : ℝ)*x 0 + (-270186901/2500000000 : ℝ)*x 1 + (-490684497/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86660999/125000000 : ℝ)^39 ≤ (63075273661963/100000000000000 : ℝ)^31 := by
    have hnat : (86660999 : ℕ)^39*100000000000000^31 ≤ 63075273661963^31*125000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86660999 125000000 63075273661963 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270186901/2500000000 : ℝ)^39 ≤ (1217286487839/20000000000000 : ℝ)^31 := by
    have hnat : (270186901 : ℕ)^39*20000000000000^31 ≤ 1217286487839^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270186901 2500000000 1217286487839 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (490684497/1250000000 : ℝ)^39 ≤ (15419146941331/50000000000000 : ℝ)^31 := by
    have hnat : (490684497 : ℕ)^39*50000000000000^31 ≤ 15419146941331^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490684497 1250000000 15419146941331 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86660999/125000000 : ℝ), (-270186901/2500000000 : ℝ), (-490684497/1250000000 : ℝ)] ![(63075273661963/100000000000000 : ℝ), (1217286487839/20000000000000 : ℝ), (15419146941331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86660999/125000000 : ℝ)|^39 ≤ (63075273661963/100000000000000 : ℝ)^31
        have hw : |(86660999/125000000 : ℝ)|=(86660999/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-270186901/2500000000 : ℝ)|^39 ≤ (1217286487839/20000000000000 : ℝ)^31
        have hw : |(-270186901/2500000000 : ℝ)|=(270186901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-490684497/1250000000 : ℝ)|^39 ≤ (15419146941331/50000000000000 : ℝ)^31
        have hw : |(-490684497/1250000000 : ℝ)|=(490684497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316030_s0_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (520092133/2000000000 : ℝ)*x 0 + (10694469/19531250 : ℝ)*x 1 + (4317064953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520092133/2000000000 : ℝ)^39 ≤ (9184711708653/50000000000000 : ℝ)^31 := by
    have hnat : (520092133 : ℕ)^39*50000000000000^31 ≤ 9184711708653^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520092133 2000000000 9184711708653 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10694469/19531250 : ℝ)^39 ≤ (2343673157067/5000000000000 : ℝ)^31 := by
    have hnat : (10694469 : ℕ)^39*5000000000000^31 ≤ 2343673157067^31*19531250^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10694469 19531250 2343673157067 5000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4317064953/10000000000 : ℝ)^39 ≤ (8689278355527/25000000000000 : ℝ)^31 := by
    have hnat : (4317064953 : ℕ)^39*25000000000000^31 ≤ 8689278355527^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317064953 10000000000 8689278355527 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520092133/2000000000 : ℝ), (10694469/19531250 : ℝ), (4317064953/10000000000 : ℝ)] ![(9184711708653/50000000000000 : ℝ), (2343673157067/5000000000000 : ℝ), (8689278355527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520092133/2000000000 : ℝ)|^39 ≤ (9184711708653/50000000000000 : ℝ)^31
        have hw : |(520092133/2000000000 : ℝ)|=(520092133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10694469/19531250 : ℝ)|^39 ≤ (2343673157067/5000000000000 : ℝ)^31
        have hw : |(10694469/19531250 : ℝ)|=(10694469/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4317064953/10000000000 : ℝ)|^39 ≤ (8689278355527/25000000000000 : ℝ)^31
        have hw : |(4317064953/10000000000 : ℝ)|=(4317064953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316030_s0_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (912198477/2500000000 : ℝ)*x 0 + (3248094733/5000000000 : ℝ)*x 1 + (-2065988881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (912198477/2500000000 : ℝ)^39 ≤ (5625817110323/20000000000000 : ℝ)^31 := by
    have hnat : (912198477 : ℕ)^39*20000000000000^31 ≤ 5625817110323^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912198477 2500000000 5625817110323 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3248094733/5000000000 : ℝ)^39 ≤ (58118251045573/100000000000000 : ℝ)^31 := by
    have hnat : (3248094733 : ℕ)^39*100000000000000^31 ≤ 58118251045573^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3248094733 5000000000 58118251045573 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2065988881/10000000000 : ℝ)^39 ≤ (2750532678149/20000000000000 : ℝ)^31 := by
    have hnat : (2065988881 : ℕ)^39*20000000000000^31 ≤ 2750532678149^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065988881 10000000000 2750532678149 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(912198477/2500000000 : ℝ), (3248094733/5000000000 : ℝ), (-2065988881/10000000000 : ℝ)] ![(5625817110323/20000000000000 : ℝ), (58118251045573/100000000000000 : ℝ), (2750532678149/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(912198477/2500000000 : ℝ)|^39 ≤ (5625817110323/20000000000000 : ℝ)^31
        have hw : |(912198477/2500000000 : ℝ)|=(912198477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3248094733/5000000000 : ℝ)|^39 ≤ (58118251045573/100000000000000 : ℝ)^31
        have hw : |(3248094733/5000000000 : ℝ)|=(3248094733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2065988881/10000000000 : ℝ)|^39 ≤ (2750532678149/20000000000000 : ℝ)^31
        have hw : |(-2065988881/10000000000 : ℝ)|=(2065988881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316030_s0_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2783771423/10000000000 : ℝ)*x 0 + (3909374097/10000000000 : ℝ)*x 1 + (-5700417893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2783771423/10000000000 : ℝ)^39 ≤ (20013046469639/100000000000000 : ℝ)^31 := by
    have hnat : (2783771423 : ℕ)^39*100000000000000^31 ≤ 20013046469639^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2783771423 10000000000 20013046469639 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3909374097/10000000000 : ℝ)^39 ≤ (15339619439757/50000000000000 : ℝ)^31 := by
    have hnat : (3909374097 : ℕ)^39*50000000000000^31 ≤ 15339619439757^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3909374097 10000000000 15339619439757 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5700417893/10000000000 : ℝ)^39 ≤ (49307714635329/100000000000000 : ℝ)^31 := by
    have hnat : (5700417893 : ℕ)^39*100000000000000^31 ≤ 49307714635329^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5700417893 10000000000 49307714635329 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2783771423/10000000000 : ℝ), (3909374097/10000000000 : ℝ), (-5700417893/10000000000 : ℝ)] ![(20013046469639/100000000000000 : ℝ), (15339619439757/50000000000000 : ℝ), (49307714635329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2783771423/10000000000 : ℝ)|^39 ≤ (20013046469639/100000000000000 : ℝ)^31
        have hw : |(-2783771423/10000000000 : ℝ)|=(2783771423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3909374097/10000000000 : ℝ)|^39 ≤ (15339619439757/50000000000000 : ℝ)^31
        have hw : |(3909374097/10000000000 : ℝ)|=(3909374097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5700417893/10000000000 : ℝ)|^39 ≤ (49307714635329/100000000000000 : ℝ)^31
        have hw : |(-5700417893/10000000000 : ℝ)|=(5700417893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316030_s0_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (456146617/625000000 : ℝ)*x 0 + (-10707263/250000000 : ℝ)*x 1 + (-3923024479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (456146617/625000000 : ℝ)^39 ≤ (67286435548009/100000000000000 : ℝ)^31 := by
    have hnat : (456146617 : ℕ)^39*100000000000000^31 ≤ 67286435548009^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456146617 625000000 67286435548009 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10707263/250000000 : ℝ)^39 ≤ (949748713841/50000000000000 : ℝ)^31 := by
    have hnat : (10707263 : ℕ)^39*50000000000000^31 ≤ 949748713841^31*250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10707263 250000000 949748713841 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3923024479/10000000000 : ℝ)^39 ≤ (30814067013423/100000000000000 : ℝ)^31 := by
    have hnat : (3923024479 : ℕ)^39*100000000000000^31 ≤ 30814067013423^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3923024479 10000000000 30814067013423 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(456146617/625000000 : ℝ), (-10707263/250000000 : ℝ), (-3923024479/10000000000 : ℝ)] ![(67286435548009/100000000000000 : ℝ), (949748713841/50000000000000 : ℝ), (30814067013423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(456146617/625000000 : ℝ)|^39 ≤ (67286435548009/100000000000000 : ℝ)^31
        have hw : |(456146617/625000000 : ℝ)|=(456146617/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10707263/250000000 : ℝ)|^39 ≤ (949748713841/50000000000000 : ℝ)^31
        have hw : |(-10707263/250000000 : ℝ)|=(10707263/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3923024479/10000000000 : ℝ)|^39 ≤ (30814067013423/100000000000000 : ℝ)^31
        have hw : |(-3923024479/10000000000 : ℝ)|=(3923024479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316030_s0_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (361460789/2000000000 : ℝ)*x 0 + (6640085041/10000000000 : ℝ)*x 1 + (3700874167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (361460789/2000000000 : ℝ)^39 ≤ (145280499657/1250000000000 : ℝ)^31 := by
    have hnat : (361460789 : ℕ)^39*1250000000000^31 ≤ 145280499657^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361460789 2000000000 145280499657 1250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6640085041/10000000000 : ℝ)^39 ≤ (29871220843727/50000000000000 : ℝ)^31 := by
    have hnat : (6640085041 : ℕ)^39*50000000000000^31 ≤ 29871220843727^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6640085041 10000000000 29871220843727 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3700874167/10000000000 : ℝ)^39 ≤ (5727023663347/20000000000000 : ℝ)^31 := by
    have hnat : (3700874167 : ℕ)^39*20000000000000^31 ≤ 5727023663347^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3700874167 10000000000 5727023663347 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(361460789/2000000000 : ℝ), (6640085041/10000000000 : ℝ), (3700874167/10000000000 : ℝ)] ![(145280499657/1250000000000 : ℝ), (29871220843727/50000000000000 : ℝ), (5727023663347/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(361460789/2000000000 : ℝ)|^39 ≤ (145280499657/1250000000000 : ℝ)^31
        have hw : |(361460789/2000000000 : ℝ)|=(361460789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6640085041/10000000000 : ℝ)|^39 ≤ (29871220843727/50000000000000 : ℝ)^31
        have hw : |(6640085041/10000000000 : ℝ)|=(6640085041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3700874167/10000000000 : ℝ)|^39 ≤ (5727023663347/20000000000000 : ℝ)^31
        have hw : |(3700874167/10000000000 : ℝ)|=(3700874167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316030_s0_12 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2863413613/10000000000 : ℝ)*x 0 + (7511490161/10000000000 : ℝ)*x 1 + (-24049203/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2863413613/10000000000 : ℝ)^39 ≤ (20736007419727/100000000000000 : ℝ)^31 := by
    have hnat : (2863413613 : ℕ)^39*100000000000000^31 ≤ 20736007419727^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2863413613 10000000000 20736007419727 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7511490161/10000000000 : ℝ)^39 ≤ (34883931409107/50000000000000 : ℝ)^31 := by
    have hnat : (7511490161 : ℕ)^39*50000000000000^31 ≤ 34883931409107^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7511490161 10000000000 34883931409107 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24049203/156250000 : ℝ)^39 ≤ (9496129742201/100000000000000 : ℝ)^31 := by
    have hnat : (24049203 : ℕ)^39*100000000000000^31 ≤ 9496129742201^31*156250000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24049203 156250000 9496129742201 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2863413613/10000000000 : ℝ), (7511490161/10000000000 : ℝ), (-24049203/156250000 : ℝ)] ![(20736007419727/100000000000000 : ℝ), (34883931409107/50000000000000 : ℝ), (9496129742201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2863413613/10000000000 : ℝ)|^39 ≤ (20736007419727/100000000000000 : ℝ)^31
        have hw : |(2863413613/10000000000 : ℝ)|=(2863413613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7511490161/10000000000 : ℝ)|^39 ≤ (34883931409107/50000000000000 : ℝ)^31
        have hw : |(7511490161/10000000000 : ℝ)|=(7511490161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-24049203/156250000 : ℝ)|^39 ≤ (9496129742201/100000000000000 : ℝ)^31
        have hw : |(-24049203/156250000 : ℝ)|=(24049203/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316030_s0_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3299130253/10000000000 : ℝ)*x 0 + (1157682497/2500000000 : ℝ)*x 1 + (-912396827/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3299130253/10000000000 : ℝ)^39 ≤ (3097600926597/12500000000000 : ℝ)^31 := by
    have hnat : (3299130253 : ℕ)^39*12500000000000^31 ≤ 3097600926597^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3299130253 10000000000 3097600926597 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1157682497/2500000000 : ℝ)^39 ≤ (3796343033203/10000000000000 : ℝ)^31 := by
    have hnat : (1157682497 : ℕ)^39*10000000000000^31 ≤ 3796343033203^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157682497 2500000000 3796343033203 10000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (912396827/2000000000 : ℝ)^39 ≤ (1164242570049/3125000000000 : ℝ)^31 := by
    have hnat : (912396827 : ℕ)^39*3125000000000^31 ≤ 1164242570049^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      912396827 2000000000 1164242570049 3125000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3299130253/10000000000 : ℝ), (1157682497/2500000000 : ℝ), (-912396827/2000000000 : ℝ)] ![(3097600926597/12500000000000 : ℝ), (3796343033203/10000000000000 : ℝ), (1164242570049/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3299130253/10000000000 : ℝ)|^39 ≤ (3097600926597/12500000000000 : ℝ)^31
        have hw : |(-3299130253/10000000000 : ℝ)|=(3299130253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1157682497/2500000000 : ℝ)|^39 ≤ (3796343033203/10000000000000 : ℝ)^31
        have hw : |(1157682497/2500000000 : ℝ)|=(1157682497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-912396827/2000000000 : ℝ)|^39 ≤ (1164242570049/3125000000000 : ℝ)^31
        have hw : |(-912396827/2000000000 : ℝ)|=(912396827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316030_s0_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (28497199/40000000 : ℝ)*x 0 + (-112410513/1000000000 : ℝ)*x 1 + (-917394567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28497199/40000000 : ℝ)^39 ≤ (65273990921623/100000000000000 : ℝ)^31 := by
    have hnat : (28497199 : ℕ)^39*100000000000000^31 ≤ 65273990921623^31*40000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28497199 40000000 65273990921623 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112410513/1000000000 : ℝ)^39 ≤ (1279039259253/20000000000000 : ℝ)^31 := by
    have hnat : (112410513 : ℕ)^39*20000000000000^31 ≤ 1279039259253^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112410513 1000000000 1279039259253 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (917394567/2500000000 : ℝ)^39 ≤ (442668949449/1562500000000 : ℝ)^31 := by
    have hnat : (917394567 : ℕ)^39*1562500000000^31 ≤ 442668949449^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      917394567 2500000000 442668949449 1562500000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(28497199/40000000 : ℝ), (-112410513/1000000000 : ℝ), (-917394567/2500000000 : ℝ)] ![(65273990921623/100000000000000 : ℝ), (1279039259253/20000000000000 : ℝ), (442668949449/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(28497199/40000000 : ℝ)|^39 ≤ (65273990921623/100000000000000 : ℝ)^31
        have hw : |(28497199/40000000 : ℝ)|=(28497199/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-112410513/1000000000 : ℝ)|^39 ≤ (1279039259253/20000000000000 : ℝ)^31
        have hw : |(-112410513/1000000000 : ℝ)|=(112410513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-917394567/2500000000 : ℝ)|^39 ≤ (442668949449/1562500000000 : ℝ)^31
        have hw : |(-917394567/2500000000 : ℝ)|=(917394567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316030_s0_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (442085341/2000000000 : ℝ)*x 0 + (1341896483/2500000000 : ℝ)*x 1 + (2380579107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442085341/2000000000 : ℝ)^39 ≤ (14972994518953/100000000000000 : ℝ)^31 := by
    have hnat : (442085341 : ℕ)^39*100000000000000^31 ≤ 14972994518953^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442085341 2000000000 14972994518953 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1341896483/2500000000 : ℝ)^39 ≤ (45713508641243/100000000000000 : ℝ)^31 := by
    have hnat : (1341896483 : ℕ)^39*100000000000000^31 ≤ 45713508641243^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341896483 2500000000 45713508641243 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2380579107/5000000000 : ℝ)^39 ≤ (4914187104171/12500000000000 : ℝ)^31 := by
    have hnat : (2380579107 : ℕ)^39*12500000000000^31 ≤ 4914187104171^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2380579107 5000000000 4914187104171 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(442085341/2000000000 : ℝ), (1341896483/2500000000 : ℝ), (2380579107/5000000000 : ℝ)] ![(14972994518953/100000000000000 : ℝ), (45713508641243/100000000000000 : ℝ), (4914187104171/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(442085341/2000000000 : ℝ)|^39 ≤ (14972994518953/100000000000000 : ℝ)^31
        have hw : |(442085341/2000000000 : ℝ)|=(442085341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1341896483/2500000000 : ℝ)|^39 ≤ (45713508641243/100000000000000 : ℝ)^31
        have hw : |(1341896483/2500000000 : ℝ)|=(1341896483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2380579107/5000000000 : ℝ)|^39 ≤ (4914187104171/12500000000000 : ℝ)^31
        have hw : |(2380579107/5000000000 : ℝ)|=(2380579107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316030_s0_19 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (206029153/625000000 : ℝ)*x 0 + (6555380539/10000000000 : ℝ)*x 1 + (-2383107589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206029153/625000000 : ℝ)^39 ≤ (6188909456649/25000000000000 : ℝ)^31 := by
    have hnat : (206029153 : ℕ)^39*25000000000000^31 ≤ 6188909456649^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206029153 625000000 6188909456649 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6555380539/10000000000 : ℝ)^39 ≤ (1469631134089/2500000000000 : ℝ)^31 := by
    have hnat : (6555380539 : ℕ)^39*2500000000000^31 ≤ 1469631134089^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6555380539 10000000000 1469631134089 2500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2383107589/10000000000 : ℝ)^39 ≤ (16459116794159/100000000000000 : ℝ)^31 := by
    have hnat : (2383107589 : ℕ)^39*100000000000000^31 ≤ 16459116794159^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2383107589 10000000000 16459116794159 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(206029153/625000000 : ℝ), (6555380539/10000000000 : ℝ), (-2383107589/10000000000 : ℝ)] ![(6188909456649/25000000000000 : ℝ), (1469631134089/2500000000000 : ℝ), (16459116794159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(206029153/625000000 : ℝ)|^39 ≤ (6188909456649/25000000000000 : ℝ)^31
        have hw : |(206029153/625000000 : ℝ)|=(206029153/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6555380539/10000000000 : ℝ)|^39 ≤ (1469631134089/2500000000000 : ℝ)^31
        have hw : |(6555380539/10000000000 : ℝ)|=(6555380539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2383107589/10000000000 : ℝ)|^39 ≤ (16459116794159/100000000000000 : ℝ)^31
        have hw : |(-2383107589/10000000000 : ℝ)|=(2383107589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316030_s0_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-535317371/2500000000 : ℝ)*x 0 + (1319534681/2500000000 : ℝ)*x 1 + (-490913081/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535317371/2500000000 : ℝ)^39 ≤ (3596510698211/25000000000000 : ℝ)^31 := by
    have hnat : (535317371 : ℕ)^39*25000000000000^31 ≤ 3596510698211^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535317371 2500000000 3596510698211 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319534681/2500000000 : ℝ)^39 ≤ (44757203421909/100000000000000 : ℝ)^31 := by
    have hnat : (1319534681 : ℕ)^39*100000000000000^31 ≤ 44757203421909^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319534681 2500000000 44757203421909 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (490913081/1000000000 : ℝ)^39 ≤ (20428376890387/50000000000000 : ℝ)^31 := by
    have hnat : (490913081 : ℕ)^39*50000000000000^31 ≤ 20428376890387^31*1000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490913081 1000000000 20428376890387 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-535317371/2500000000 : ℝ), (1319534681/2500000000 : ℝ), (-490913081/1000000000 : ℝ)] ![(3596510698211/25000000000000 : ℝ), (44757203421909/100000000000000 : ℝ), (20428376890387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-535317371/2500000000 : ℝ)|^39 ≤ (3596510698211/25000000000000 : ℝ)^31
        have hw : |(-535317371/2500000000 : ℝ)|=(535317371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1319534681/2500000000 : ℝ)|^39 ≤ (44757203421909/100000000000000 : ℝ)^31
        have hw : |(1319534681/2500000000 : ℝ)|=(1319534681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-490913081/1000000000 : ℝ)|^39 ≤ (20428376890387/50000000000000 : ℝ)^31
        have hw : |(-490913081/1000000000 : ℝ)|=(490913081/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316030_s0_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (8028405601/10000000000 : ℝ)*x 0 + (-592191397/10000000000 : ℝ)*x 1 + (-730842487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8028405601/10000000000 : ℝ)^39 ≤ (15172163310271/20000000000000 : ℝ)^31 := by
    have hnat : (8028405601 : ℕ)^39*20000000000000^31 ≤ 15172163310271^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8028405601 10000000000 15172163310271 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (592191397/10000000000 : ℝ)^39 ≤ (1427736697687/50000000000000 : ℝ)^31 := by
    have hnat : (592191397 : ℕ)^39*50000000000000^31 ≤ 1427736697687^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592191397 10000000000 1427736697687 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (730842487/2500000000 : ℝ)^39 ≤ (21283710046513/100000000000000 : ℝ)^31 := by
    have hnat : (730842487 : ℕ)^39*100000000000000^31 ≤ 21283710046513^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730842487 2500000000 21283710046513 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8028405601/10000000000 : ℝ), (-592191397/10000000000 : ℝ), (-730842487/2500000000 : ℝ)] ![(15172163310271/20000000000000 : ℝ), (1427736697687/50000000000000 : ℝ), (21283710046513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8028405601/10000000000 : ℝ)|^39 ≤ (15172163310271/20000000000000 : ℝ)^31
        have hw : |(8028405601/10000000000 : ℝ)|=(8028405601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-592191397/10000000000 : ℝ)|^39 ≤ (1427736697687/50000000000000 : ℝ)^31
        have hw : |(-592191397/10000000000 : ℝ)|=(592191397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-730842487/2500000000 : ℝ)|^39 ≤ (21283710046513/100000000000000 : ℝ)^31
        have hw : |(-730842487/2500000000 : ℝ)|=(730842487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316030_s0_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (251946727/1250000000 : ℝ)*x 0 + (5654222049/10000000000 : ℝ)*x 1 + (4620957611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (251946727/1250000000 : ℝ)^39 ≤ (6665898574501/50000000000000 : ℝ)^31 := by
    have hnat : (251946727 : ℕ)^39*50000000000000^31 ≤ 6665898574501^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251946727 1250000000 6665898574501 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5654222049/10000000000 : ℝ)^39 ≤ (48805535438183/100000000000000 : ℝ)^31 := by
    have hnat : (5654222049 : ℕ)^39*100000000000000^31 ≤ 48805535438183^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5654222049 10000000000 48805535438183 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4620957611/10000000000 : ℝ)^39 ≤ (7572533480813/20000000000000 : ℝ)^31 := by
    have hnat : (4620957611 : ℕ)^39*20000000000000^31 ≤ 7572533480813^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4620957611 10000000000 7572533480813 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(251946727/1250000000 : ℝ), (5654222049/10000000000 : ℝ), (4620957611/10000000000 : ℝ)] ![(6665898574501/50000000000000 : ℝ), (48805535438183/100000000000000 : ℝ), (7572533480813/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(251946727/1250000000 : ℝ)|^39 ≤ (6665898574501/50000000000000 : ℝ)^31
        have hw : |(251946727/1250000000 : ℝ)|=(251946727/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5654222049/10000000000 : ℝ)|^39 ≤ (48805535438183/100000000000000 : ℝ)^31
        have hw : |(5654222049/10000000000 : ℝ)|=(5654222049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4620957611/10000000000 : ℝ)|^39 ≤ (7572533480813/20000000000000 : ℝ)^31
        have hw : |(4620957611/10000000000 : ℝ)|=(4620957611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316030_s0_25 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4438235719/10000000000 : ℝ)*x 0 + (3059900827/5000000000 : ℝ)*x 1 + (-1616087373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4438235719/10000000000 : ℝ)^39 ≤ (7197768481853/20000000000000 : ℝ)^31 := by
    have hnat : (4438235719 : ℕ)^39*20000000000000^31 ≤ 7197768481853^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4438235719 10000000000 7197768481853 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3059900827/5000000000 : ℝ)^39 ≤ (53914033383783/100000000000000 : ℝ)^31 := by
    have hnat : (3059900827 : ℕ)^39*100000000000000^31 ≤ 53914033383783^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3059900827 5000000000 53914033383783 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1616087373/10000000000 : ℝ)^39 ≤ (1262140524461/12500000000000 : ℝ)^31 := by
    have hnat : (1616087373 : ℕ)^39*12500000000000^31 ≤ 1262140524461^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616087373 10000000000 1262140524461 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4438235719/10000000000 : ℝ), (3059900827/5000000000 : ℝ), (-1616087373/10000000000 : ℝ)] ![(7197768481853/20000000000000 : ℝ), (53914033383783/100000000000000 : ℝ), (1262140524461/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4438235719/10000000000 : ℝ)|^39 ≤ (7197768481853/20000000000000 : ℝ)^31
        have hw : |(4438235719/10000000000 : ℝ)|=(4438235719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3059900827/5000000000 : ℝ)|^39 ≤ (53914033383783/100000000000000 : ℝ)^31
        have hw : |(3059900827/5000000000 : ℝ)|=(3059900827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1616087373/10000000000 : ℝ)|^39 ≤ (1262140524461/12500000000000 : ℝ)^31
        have hw : |(-1616087373/10000000000 : ℝ)|=(1616087373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316030_s1_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-215976283/625000000 : ℝ)*x 0 + (922995541/2000000000 : ℝ)*x 1 + (-4432507951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215976283/625000000 : ℝ)^39 ≤ (3283567930617/12500000000000 : ℝ)^31 := by
    have hnat : (215976283 : ℕ)^39*12500000000000^31 ≤ 3283567930617^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215976283 625000000 3283567930617 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922995541/2000000000 : ℝ)^39 ≤ (37801035732731/100000000000000 : ℝ)^31 := by
    have hnat : (922995541 : ℕ)^39*100000000000000^31 ≤ 37801035732731^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922995541 2000000000 37801035732731 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4432507951/10000000000 : ℝ)^39 ≤ (2245651300163/6250000000000 : ℝ)^31 := by
    have hnat : (4432507951 : ℕ)^39*6250000000000^31 ≤ 2245651300163^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4432507951 10000000000 2245651300163 6250000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215976283/625000000 : ℝ), (922995541/2000000000 : ℝ), (-4432507951/10000000000 : ℝ)] ![(3283567930617/12500000000000 : ℝ), (37801035732731/100000000000000 : ℝ), (2245651300163/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215976283/625000000 : ℝ)|^39 ≤ (3283567930617/12500000000000 : ℝ)^31
        have hw : |(-215976283/625000000 : ℝ)|=(215976283/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(922995541/2000000000 : ℝ)|^39 ≤ (37801035732731/100000000000000 : ℝ)^31
        have hw : |(922995541/2000000000 : ℝ)|=(922995541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4432507951/10000000000 : ℝ)|^39 ≤ (2245651300163/6250000000000 : ℝ)^31
        have hw : |(-4432507951/10000000000 : ℝ)|=(4432507951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316030_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1144044321/2000000000 : ℝ)*x 0 + (-2416451377/10000000000 : ℝ)*x 1 + (-2107541421/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1144044321/2000000000 : ℝ)^39 ≤ (9904663265417/20000000000000 : ℝ)^31 := by
    have hnat : (1144044321 : ℕ)^39*20000000000000^31 ≤ 9904663265417^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144044321 2000000000 9904663265417 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2416451377/10000000000 : ℝ)^39 ≤ (16749359554729/100000000000000 : ℝ)^31 := by
    have hnat : (2416451377 : ℕ)^39*100000000000000^31 ≤ 16749359554729^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2416451377 10000000000 16749359554729 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107541421/5000000000 : ℝ)^39 ≤ (6745464821087/20000000000000 : ℝ)^31 := by
    have hnat : (2107541421 : ℕ)^39*20000000000000^31 ≤ 6745464821087^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107541421 5000000000 6745464821087 20000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1144044321/2000000000 : ℝ), (-2416451377/10000000000 : ℝ), (-2107541421/5000000000 : ℝ)] ![(9904663265417/20000000000000 : ℝ), (16749359554729/100000000000000 : ℝ), (6745464821087/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1144044321/2000000000 : ℝ)|^39 ≤ (9904663265417/20000000000000 : ℝ)^31
        have hw : |(1144044321/2000000000 : ℝ)|=(1144044321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2416451377/10000000000 : ℝ)|^39 ≤ (16749359554729/100000000000000 : ℝ)^31
        have hw : |(-2416451377/10000000000 : ℝ)|=(2416451377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2107541421/5000000000 : ℝ)|^39 ≤ (6745464821087/20000000000000 : ℝ)^31
        have hw : |(-2107541421/5000000000 : ℝ)|=(2107541421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316030_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5342451/16000000 : ℝ)*x 0 + (4868282833/10000000000 : ℝ)*x 1 + (2141480121/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5342451/16000000 : ℝ)^39 ≤ (25158453220787/100000000000000 : ℝ)^31 := by
    have hnat : (5342451 : ℕ)^39*100000000000000^31 ≤ 25158453220787^31*16000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5342451 16000000 25158453220787 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4868282833/10000000000 : ℝ)^39 ≤ (40429520356087/100000000000000 : ℝ)^31 := by
    have hnat : (4868282833 : ℕ)^39*100000000000000^31 ≤ 40429520356087^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4868282833 10000000000 40429520356087 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2141480121/5000000000 : ℝ)^39 ≤ (34412026412067/100000000000000 : ℝ)^31 := by
    have hnat : (2141480121 : ℕ)^39*100000000000000^31 ≤ 34412026412067^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2141480121 5000000000 34412026412067 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5342451/16000000 : ℝ), (4868282833/10000000000 : ℝ), (2141480121/5000000000 : ℝ)] ![(25158453220787/100000000000000 : ℝ), (40429520356087/100000000000000 : ℝ), (34412026412067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5342451/16000000 : ℝ)|^39 ≤ (25158453220787/100000000000000 : ℝ)^31
        have hw : |(5342451/16000000 : ℝ)|=(5342451/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4868282833/10000000000 : ℝ)|^39 ≤ (40429520356087/100000000000000 : ℝ)^31
        have hw : |(4868282833/10000000000 : ℝ)|=(4868282833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2141480121/5000000000 : ℝ)|^39 ≤ (34412026412067/100000000000000 : ℝ)^31
        have hw : |(2141480121/5000000000 : ℝ)|=(2141480121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316030_s1_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3973484637/10000000000 : ℝ)*x 0 + (5520765283/10000000000 : ℝ)*x 1 + (-365994713/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3973484637/10000000000 : ℝ)^39 ≤ (31313523252329/100000000000000 : ℝ)^31 := by
    have hnat : (3973484637 : ℕ)^39*100000000000000^31 ≤ 31313523252329^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3973484637 10000000000 31313523252329 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5520765283/10000000000 : ℝ)^39 ≤ (23680368569297/50000000000000 : ℝ)^31 := by
    have hnat : (5520765283 : ℕ)^39*50000000000000^31 ≤ 23680368569297^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520765283 10000000000 23680368569297 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (365994713/1250000000 : ℝ)^39 ≤ (21325739590719/100000000000000 : ℝ)^31 := by
    have hnat : (365994713 : ℕ)^39*100000000000000^31 ≤ 21325739590719^31*1250000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365994713 1250000000 21325739590719 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3973484637/10000000000 : ℝ), (5520765283/10000000000 : ℝ), (-365994713/1250000000 : ℝ)] ![(31313523252329/100000000000000 : ℝ), (23680368569297/50000000000000 : ℝ), (21325739590719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3973484637/10000000000 : ℝ)|^39 ≤ (31313523252329/100000000000000 : ℝ)^31
        have hw : |(3973484637/10000000000 : ℝ)|=(3973484637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5520765283/10000000000 : ℝ)|^39 ≤ (23680368569297/50000000000000 : ℝ)^31
        have hw : |(5520765283/10000000000 : ℝ)|=(5520765283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-365994713/1250000000 : ℝ)|^39 ≤ (21325739590719/100000000000000 : ℝ)^31
        have hw : |(-365994713/1250000000 : ℝ)|=(365994713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316030 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]]) : False := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1571102372827199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1571102372827199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(515551893046311/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((86660999/125000000 : ℝ)*X 1 0+(-270186901/2500000000 : ℝ)*X 1 1+(-490684497/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((520092133/2000000000 : ℝ)*X 2 0+(10694469/19531250 : ℝ)*X 2 1+(4317064953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((912198477/2500000000 : ℝ)*X 0 0+(3248094733/5000000000 : ℝ)*X 0 1+(-2065988881/10000000000 : ℝ)*X 0 2+(912198477/2500000000 : ℝ)*X 1 0+(3248094733/5000000000 : ℝ)*X 1 1+(-2065988881/10000000000 : ℝ)*X 1 2+(912198477/2500000000 : ℝ)*X 2 0+(3248094733/5000000000 : ℝ)*X 2 1+(-2065988881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2783771423/10000000000 : ℝ)*X 0 0+(3909374097/10000000000 : ℝ)*X 0 1+(-5700417893/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((456146617/625000000 : ℝ)*X 1 0+(-10707263/250000000 : ℝ)*X 1 1+(-3923024479/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((361460789/2000000000 : ℝ)*X 2 0+(6640085041/10000000000 : ℝ)*X 2 1+(3700874167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((2863413613/10000000000 : ℝ)*X 0 0+(7511490161/10000000000 : ℝ)*X 0 1+(-24049203/156250000 : ℝ)*X 0 2+(2863413613/10000000000 : ℝ)*X 1 0+(7511490161/10000000000 : ℝ)*X 1 1+(-24049203/156250000 : ℝ)*X 1 2+(2863413613/10000000000 : ℝ)*X 2 0+(7511490161/10000000000 : ℝ)*X 2 1+(-24049203/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-3299130253/10000000000 : ℝ)*X 0 0+(1157682497/2500000000 : ℝ)*X 0 1+(-912396827/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((28497199/40000000 : ℝ)*X 1 0+(-112410513/1000000000 : ℝ)*X 1 1+(-917394567/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((442085341/2000000000 : ℝ)*X 2 0+(1341896483/2500000000 : ℝ)*X 2 1+(2380579107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((206029153/625000000 : ℝ)*X 0 0+(6555380539/10000000000 : ℝ)*X 0 1+(-2383107589/10000000000 : ℝ)*X 0 2+(206029153/625000000 : ℝ)*X 1 0+(6555380539/10000000000 : ℝ)*X 1 1+(-2383107589/10000000000 : ℝ)*X 1 2+(206029153/625000000 : ℝ)*X 2 0+(6555380539/10000000000 : ℝ)*X 2 1+(-2383107589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-535317371/2500000000 : ℝ)*X 0 0+(1319534681/2500000000 : ℝ)*X 0 1+(-490913081/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((8028405601/10000000000 : ℝ)*X 1 0+(-592191397/10000000000 : ℝ)*X 1 1+(-730842487/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((251946727/1250000000 : ℝ)*X 2 0+(5654222049/10000000000 : ℝ)*X 2 1+(4620957611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((4438235719/10000000000 : ℝ)*X 0 0+(3059900827/5000000000 : ℝ)*X 0 1+(-1616087373/10000000000 : ℝ)*X 0 2+(4438235719/10000000000 : ℝ)*X 1 0+(3059900827/5000000000 : ℝ)*X 1 1+(-1616087373/10000000000 : ℝ)*X 1 2+(4438235719/10000000000 : ℝ)*X 2 0+(3059900827/5000000000 : ℝ)*X 2 1+(-1616087373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((29837/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29837/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5507765960532098886651/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1121356555501/1000000000000 : ℝ)*(base39) + (1580224877351/1000000000000 : ℝ)*(base49) + (323710065469/200000000000 : ℝ)*(base50) + (53629838351/100000000000 : ℝ)*(base60) + (568012608923/125000000000 : ℝ)*(major_s0_0) + (568012608923/125000000000 : ℝ)*(major_s0_1) + (568012608923/125000000000 : ℝ)*(major_s0_2) + (11887009/125000000000 : ℝ)*(sp_s0_1) + (815576145547/125000000000 : ℝ)*(sp_s0_7) + (1631134330443/250000000000 : ℝ)*(sp_s0_8) + (3262285050011/500000000000 : ℝ)*(sp_s0_9) + (2563566387439/1000000000000 : ℝ)*(sp_s0_12) + (23253467/1000000000000 : ℝ)*(sp_s0_20) + (62317821/1000000000000 : ℝ)*(sp_s0_22) + (2563566387439/1000000000000 : ℝ)*(f.failure) + (6524632417843/1000000000000 : ℝ)*(f.sum) + (1037920969/10000000000000000000000 : ℝ)*base63 + (467072404645553/625000000000000000000000000 : ℝ)*base65 + (333682483791947/625000000000000000000000000 : ℝ)*base66 + (353576628121677/1250000000000000000000000000 : ℝ)*base69 + (388589442287783/1250000000000000000000000000 : ℝ)*base71 + (40805919916947/625000000000000000000000000 : ℝ)*base72 + (413401451378323/1250000000000000000000000000 : ℝ)*base75 + (1210340718246677/1250000000000000000000000000 : ℝ)*base77 + (68494864051803/312500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (125177/100000000000000000 : ℝ)*base86 + (125177/100000000000000000 : ℝ)*base88 + (125177/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(977/20000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(977/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16747154468138289/1250000000000000000000 : ℝ) := by norm_num
    linear_combination (693755992783/1000000000000 : ℝ)*(base39) + (316389918943/1000000000000 : ℝ)*(base49) + (152570053661/1000000000000 : ℝ)*(base60) + (2945281655941/1000000000000 : ℝ)*(major_s0_0) + (2945281655941/1000000000000 : ℝ)*(major_s0_1) + (2945281655941/1000000000000 : ℝ)*(major_s0_2) + (11619737/10000000000 : ℝ)*(sp_s0_1) + (14861401/250000000000 : ℝ)*(sp_s0_2) + (132538039/250000000000 : ℝ)*(sp_s0_6) + (2114485249569/500000000000 : ℝ)*(sp_s0_13) + (2113904262719/500000000000 : ℝ)*(sp_s0_14) + (2114455526767/500000000000 : ℝ)*(sp_s0_15) + (332199722957/200000000000 : ℝ)*(sp_s0_19) + (59579889/1000000000000 : ℝ)*(sp_s0_25) + (1661588346831/1000000000000 : ℝ)*(f.failure) + (2114485249569/500000000000 : ℝ)*(f.sum) + (232546521/2000000000000000000000 : ℝ)*base62 + (1134612800783651/5000000000000000000000000000 : ℝ)*base65 + (523765904716349/5000000000000000000000000000 : ℝ)*base66 + (6632066454260741/10000000000000000000000000000 : ℝ)*base68 + (6038320250306561/10000000000000000000000000000 : ℝ)*base71 + (2434552572283651/5000000000000000000000000000 : ℝ)*base73 + (1323379213739259/10000000000000000000000000000 : ℝ)*base74 + (1660754652260741/10000000000000000000000000000 : ℝ)*base76 + (1039620541216349/2500000000000000000000000000 : ℝ)*base78 + (122567/100000000000000000 : ℝ)*base87 + (122567/100000000000000000 : ℝ)*base89 + (122567/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2453/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2453/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3400629533615052897507/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1323477632451/1000000000000 : ℝ)*(base39) + (27930731409/20000000000 : ℝ)*(base49) + (1231961600809/1000000000000 : ℝ)*(base50) + (4064546097987/1000000000000 : ℝ)*(major_s0_0) + (4064546097987/1000000000000 : ℝ)*(major_s0_1) + (4064546097987/1000000000000 : ℝ)*(major_s0_2) + (25904243/500000000000 : ℝ)*(sp_s0_2) + (2234503/200000000000 : ℝ)*(sp_s0_9) + (4286117/1000000000000 : ℝ)*(sp_s0_12) + (84701/10000000000 : ℝ)*(sp_s0_14) + (233442670169/40000000000 : ℝ)*(sp_s0_20) + (46688466273/8000000000 : ℝ)*(sp_s0_21) + (729500471653/125000000000 : ℝ)*(sp_s0_22) + (2293020022083/1000000000000 : ℝ)*(sp_s0_25) + (2293024308201/1000000000000 : ℝ)*(f.failure) + (233442670169/40000000000 : ℝ)*(f.sum) + (1108238251/5000000000000000000000 : ℝ)*base63 + (2045819225375957/5000000000000000000000000000 : ℝ)*base65 + (1105920871375957/5000000000000000000000000000 : ℝ)*base67 + (3292640349748413/10000000000000000000000000000 : ℝ)*base69 + (3231625848500327/10000000000000000000000000000 : ℝ)*base71 + (962465896375957/5000000000000000000000000000 : ℝ)*base73 + (2499736080251587/10000000000000000000000000000 : ℝ)*base75 + (3814274454748413/10000000000000000000000000000 : ℝ)*base77 + (1618104483875957/2500000000000000000000000000 : ℝ)*base79 + (84657/100000000000000000 : ℝ)*base87 + (84657/100000000000000000 : ℝ)*base89 + (84657/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (29837/100000 : ℝ) ^ (19/4 : ℝ) ≤ (319953586615245461/100000000000000000000 : ℝ) := by
    have hpowers : (29837/100000 : ℝ)^19 ≤ (319953586615245461/100000000000000000000 : ℝ)^4 := by
      have hnat : (29837 : ℕ)^19*100000000000000000000^4 ≤ 319953586615245461^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29837 100000 319953586615245461 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29837/100000 : ℝ)) (X := (319953586615245461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100319953586615245461/100000000000000000000 : ℝ) ≤ (10006727373954289/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (100319953586615245461/100000000000000000000 : ℝ)^4 ≤ (10006727373954289/10000000000000000 : ℝ)^19 := by
      have hnat : (100319953586615245461 : ℕ)^4*10000000000000000^19 ≤ 10006727373954289^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100319953586615245461 100000000000000000000 10006727373954289 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006727373954289/10000000000000000 : ℝ)) (X := (100319953586615245461/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50319953586615245461/50000000000000000000 : ℝ) ≤ (5006718915183069/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (50319953586615245461/50000000000000000000 : ℝ)^4 ≤ (5006718915183069/5000000000000000 : ℝ)^19 := by
      have hnat : (50319953586615245461 : ℕ)^4*5000000000000000^19 ≤ 5006718915183069^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50319953586615245461 50000000000000000000 5006718915183069 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006718915183069/5000000000000000 : ℝ)) (X := (50319953586615245461/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(6727373954289/2983700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(6710456411849/2983700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (29837/100000 : ℝ)) (alpha := (6727373954289/2983700000000000 : ℝ)) (beta := (6710456411849/2983700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (29837/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(6727373954289/2983700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(6710456411849/2983700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (977/20000 : ℝ) ^ (19/4 : ℝ) ≤ (11834139759423/20000000000000000000 : ℝ) := by
    have hpowers : (977/20000 : ℝ)^19 ≤ (11834139759423/20000000000000000000 : ℝ)^4 := by
      have hnat : (977 : ℕ)^19*20000000000000000000^4 ≤ 11834139759423^4*20000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        977 20000 11834139759423 20000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (977/20000 : ℝ)) (X := (11834139759423/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (20000011834139759423/20000000000000000000 : ℝ) ≤ (1250000155712329/1250000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (20000011834139759423/20000000000000000000 : ℝ)^4 ≤ (1250000155712329/1250000000000000 : ℝ)^19 := by
      have hnat : (20000011834139759423 : ℕ)^4*1250000000000000^19 ≤ 1250000155712329^19*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20000011834139759423 20000000000000000000 1250000155712329 1250000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000155712329/1250000000000000 : ℝ)) (X := (20000011834139759423/20000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (10000011834139759423/10000000000000000000 : ℝ) ≤ (10000002491396681/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (10000011834139759423/10000000000000000000 : ℝ)^4 ≤ (10000002491396681/10000000000000000 : ℝ)^19 := by
      have hnat : (10000011834139759423 : ℕ)^4*10000000000000000^19 ≤ 10000002491396681^19*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000011834139759423 10000000000000000000 10000002491396681 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002491396681/10000000000000000 : ℝ)) (X := (10000011834139759423/10000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(155712329/61062500000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1245698049/488500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (977/20000 : ℝ)) (alpha := (155712329/61062500000000 : ℝ)) (beta := (1245698049/488500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (977/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(155712329/61062500000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1245698049/488500000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (2453/10000 : ℝ) ^ (19/4 : ℝ) ≤ (25240232416140839/20000000000000000000 : ℝ) := by
    have hpowers : (2453/10000 : ℝ)^19 ≤ (25240232416140839/20000000000000000000 : ℝ)^4 := by
      have hnat : (2453 : ℕ)^19*20000000000000000000^4 ≤ 25240232416140839^4*10000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2453 10000 25240232416140839 20000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2453/10000 : ℝ)) (X := (25240232416140839/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (20025240232416140839/20000000000000000000 : ℝ) ≤ (10002655544014341/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (20025240232416140839/20000000000000000000 : ℝ)^4 ≤ (10002655544014341/10000000000000000 : ℝ)^19 := by
      have hnat : (20025240232416140839 : ℕ)^4*10000000000000000^19 ≤ 10002655544014341^19*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20025240232416140839 20000000000000000000 10002655544014341 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002655544014341/10000000000000000 : ℝ)) (X := (20025240232416140839/20000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (10025240232416140839/10000000000000000000 : ℝ) ≤ (1000530844689199/1000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (10025240232416140839/10000000000000000000 : ℝ)^4 ≤ (1000530844689199/1000000000000000 : ℝ)^19 := by
      have hnat : (10025240232416140839 : ℕ)^4*1000000000000000^19 ≤ 1000530844689199^19*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10025240232416140839 10000000000000000000 1000530844689199 1000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000530844689199/1000000000000000 : ℝ)) (X := (10025240232416140839/10000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(2655544014341/2453000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(2652902877649/2453000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (2453/10000 : ℝ)) (alpha := (2655544014341/2453000000000000 : ℝ)) (beta := (2652902877649/2453000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (2453/10000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(2655544014341/2453000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(2652902877649/2453000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-215976283/625000000 : ℝ)*X 0 0+(922995541/2000000000 : ℝ)*X 0 1+(-4432507951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1144044321/2000000000 : ℝ)*X 1 0+(-2416451377/10000000000 : ℝ)*X 1 1+(-2107541421/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5342451/16000000 : ℝ)*X 2 0+(4868282833/10000000000 : ℝ)*X 2 1+(2141480121/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3973484637/10000000000 : ℝ)*X 0 0+(5520765283/10000000000 : ℝ)*X 0 1+(-365994713/1250000000 : ℝ)*X 0 2+(3973484637/10000000000 : ℝ)*X 1 0+(5520765283/10000000000 : ℝ)*X 1 1+(-365994713/1250000000 : ℝ)*X 1 2+(3973484637/10000000000 : ℝ)*X 2 0+(5520765283/10000000000 : ℝ)*X 2 1+(-365994713/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316030_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-381771/50000 : ℝ) < ((-177257/100000 : ℝ)*P 0+(-177257/100000 : ℝ)*P 1+(-177257/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-381771/50000 : ℝ) < (-674462818188392087191817756216037/89383484121250000000000000000000 : ℝ) := by norm_num
    linear_combination (83773/1000000000000 : ℝ)*(base15) + (5839/200000000000 : ℝ)*(base16) + (41559309109/100000000000 : ℝ)*(base39) + (2933/500000000000 : ℝ)*(base40) + (7033263491/7812500000 : ℝ)*(base49) + (535370270209/1000000000000 : ℝ)*(base50) + (1569/100000000000 : ℝ)*(base59) + (61632729543/1000000000000 : ℝ)*(base60) + (177257/100000 : ℝ)*(major_s1_0) + (177257/100000 : ℝ)*(major_s1_1) + (177257/100000 : ℝ)*(major_s1_2) + (2515240277397/1000000000000 : ℝ)*(sp_s1_0) + (2515240164429/1000000000000 : ℝ)*(sp_s1_1) + (2515240277397/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2515240277397/1000000000000 : ℝ)*(f.sum) + (1216230110956181/1497863125000000000000000000 : ℝ)*base63 + (226039003981/4906000000000000000000000 : ℝ)*base64 + (973503774581/9770000000000000000000000 : ℝ)*base66 + (2268580379823/4906000000000000000000000 : ℝ)*base69 + (120158172770163987/731901610000000000000000000000 : ℝ)*base70 + (65357330348267/149185000000000000000000000 : ℝ)*base72 + (7917218401/15632000000000000000000 : ℝ)*base75 + (45116105159263/298370000000000000000000000 : ℝ)*base77 + (78187277156602713/145753745000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c316032_s0_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2634210699/10000000000 : ℝ)*x 0 + (-2212361667/5000000000 : ℝ)*x 1 + (-5345695877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2634210699/10000000000 : ℝ)^39 ≤ (18669855788973/100000000000000 : ℝ)^31 := by
    have hnat : (2634210699 : ℕ)^39*100000000000000^31 ≤ 18669855788973^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2634210699 10000000000 18669855788973 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2212361667/5000000000 : ℝ)^39 ≤ (35851051151229/100000000000000 : ℝ)^31 := by
    have hnat : (2212361667 : ℕ)^39*100000000000000^31 ≤ 35851051151229^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212361667 5000000000 35851051151229 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5345695877/10000000000 : ℝ)^39 ≤ (11369773262881/25000000000000 : ℝ)^31 := by
    have hnat : (5345695877 : ℕ)^39*25000000000000^31 ≤ 11369773262881^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345695877 10000000000 11369773262881 25000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2634210699/10000000000 : ℝ), (-2212361667/5000000000 : ℝ), (-5345695877/10000000000 : ℝ)] ![(18669855788973/100000000000000 : ℝ), (35851051151229/100000000000000 : ℝ), (11369773262881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2634210699/10000000000 : ℝ)|^39 ≤ (18669855788973/100000000000000 : ℝ)^31
        have hw : |(-2634210699/10000000000 : ℝ)|=(2634210699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2212361667/5000000000 : ℝ)|^39 ≤ (35851051151229/100000000000000 : ℝ)^31
        have hw : |(-2212361667/5000000000 : ℝ)|=(2212361667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5345695877/10000000000 : ℝ)|^39 ≤ (11369773262881/25000000000000 : ℝ)^31
        have hw : |(-5345695877/10000000000 : ℝ)|=(5345695877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316032_s0_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2832085541/10000000000 : ℝ)*x 0 + (325847893/625000000 : ℝ)*x 1 + (-4388241299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2832085541/10000000000 : ℝ)^39 ≤ (10225497944031/50000000000000 : ℝ)^31 := by
    have hnat : (2832085541 : ℕ)^39*50000000000000^31 ≤ 10225497944031^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2832085541 10000000000 10225497944031 50000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325847893/625000000 : ℝ)^39 ≤ (44069432152513/100000000000000 : ℝ)^31 := by
    have hnat : (325847893 : ℕ)^39*100000000000000^31 ≤ 44069432152513^31*625000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325847893 625000000 44069432152513 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4388241299/10000000000 : ℝ)^39 ≤ (35479571940867/100000000000000 : ℝ)^31 := by
    have hnat : (4388241299 : ℕ)^39*100000000000000^31 ≤ 35479571940867^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4388241299 10000000000 35479571940867 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2832085541/10000000000 : ℝ), (325847893/625000000 : ℝ), (-4388241299/10000000000 : ℝ)] ![(10225497944031/50000000000000 : ℝ), (44069432152513/100000000000000 : ℝ), (35479571940867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2832085541/10000000000 : ℝ)|^39 ≤ (10225497944031/50000000000000 : ℝ)^31
        have hw : |(2832085541/10000000000 : ℝ)|=(2832085541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(325847893/625000000 : ℝ)|^39 ≤ (44069432152513/100000000000000 : ℝ)^31
        have hw : |(325847893/625000000 : ℝ)|=(325847893/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4388241299/10000000000 : ℝ)|^39 ≤ (35479571940867/100000000000000 : ℝ)^31
        have hw : |(-4388241299/10000000000 : ℝ)|=(4388241299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316032_s0_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1421122949/2000000000 : ℝ)*x 0 + (-1355503813/5000000000 : ℝ)*x 1 + (2281846047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1421122949/2000000000 : ℝ)^39 ≤ (65058689438013/100000000000000 : ℝ)^31 := by
    have hnat : (1421122949 : ℕ)^39*100000000000000^31 ≤ 65058689438013^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1421122949 2000000000 65058689438013 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355503813/5000000000 : ℝ)^39 ≤ (19357171497017/100000000000000 : ℝ)^31 := by
    have hnat : (1355503813 : ℕ)^39*100000000000000^31 ≤ 19357171497017^31*5000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355503813 5000000000 19357171497017 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2281846047/10000000000 : ℝ)^39 ≤ (15584139052007/100000000000000 : ℝ)^31 := by
    have hnat : (2281846047 : ℕ)^39*100000000000000^31 ≤ 15584139052007^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2281846047 10000000000 15584139052007 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1421122949/2000000000 : ℝ), (-1355503813/5000000000 : ℝ), (2281846047/10000000000 : ℝ)] ![(65058689438013/100000000000000 : ℝ), (19357171497017/100000000000000 : ℝ), (15584139052007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1421122949/2000000000 : ℝ)|^39 ≤ (65058689438013/100000000000000 : ℝ)^31
        have hw : |(1421122949/2000000000 : ℝ)|=(1421122949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1355503813/5000000000 : ℝ)|^39 ≤ (19357171497017/100000000000000 : ℝ)^31
        have hw : |(-1355503813/5000000000 : ℝ)|=(1355503813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2281846047/10000000000 : ℝ)|^39 ≤ (15584139052007/100000000000000 : ℝ)^31
        have hw : |(2281846047/10000000000 : ℝ)|=(2281846047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316032_s0_6 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3505908383/10000000000 : ℝ)*x 0 + (-814314753/2000000000 : ℝ)*x 1 + (-1229760227/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3505908383/10000000000 : ℝ)^39 ≤ (26750366734091/100000000000000 : ℝ)^31 := by
    have hnat : (3505908383 : ℕ)^39*100000000000000^31 ≤ 26750366734091^31*10000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3505908383 10000000000 26750366734091 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (814314753/2000000000 : ℝ)^39 ≤ (4036136254651/12500000000000 : ℝ)^31 := by
    have hnat : (814314753 : ℕ)^39*12500000000000^31 ≤ 4036136254651^31*2000000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814314753 2000000000 4036136254651 12500000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1229760227/2500000000 : ℝ)^39 ≤ (40960543220691/100000000000000 : ℝ)^31 := by
    have hnat : (1229760227 : ℕ)^39*100000000000000^31 ≤ 40960543220691^31*2500000000^39 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229760227 2500000000 40960543220691 100000000000000 39 31 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (39/8 : ℝ)) 39 31 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3505908383/10000000000 : ℝ), (-814314753/2000000000 : ℝ), (-1229760227/2500000000 : ℝ)] ![(26750366734091/100000000000000 : ℝ), (4036136254651/12500000000000 : ℝ), (40960543220691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3505908383/10000000000 : ℝ)|^39 ≤ (26750366734091/100000000000000 : ℝ)^31
        have hw : |(3505908383/10000000000 : ℝ)|=(3505908383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-814314753/2000000000 : ℝ)|^39 ≤ (4036136254651/12500000000000 : ℝ)^31
        have hw : |(-814314753/2000000000 : ℝ)|=(814314753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1229760227/2500000000 : ℝ)|^39 ≤ (40960543220691/100000000000000 : ℝ)^31
        have hw : |(-1229760227/2500000000 : ℝ)|=(1229760227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316032 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]]) : False := by
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
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1571102372827199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1571102372827199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1571102372827199/10000000000000000 : ℝ)) (beta := (515551893046311/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1571102372827199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(515551893046311/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2634210699/10000000000 : ℝ)*X 0 0+(-2212361667/5000000000 : ℝ)*X 0 1+(-5345695877/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316032_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2832085541/10000000000 : ℝ)*X 1 0+(325847893/625000000 : ℝ)*X 1 1+(-4388241299/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316032_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((1421122949/2000000000 : ℝ)*X 2 0+(-1355503813/5000000000 : ℝ)*X 2 1+(2281846047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316032_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((3505908383/10000000000 : ℝ)*X 0 0+(-814314753/2000000000 : ℝ)*X 0 1+(-1229760227/2500000000 : ℝ)*X 0 2+(3505908383/10000000000 : ℝ)*X 1 0+(-814314753/2000000000 : ℝ)*X 1 1+(-1229760227/2500000000 : ℝ)*X 1 2+(3505908383/10000000000 : ℝ)*X 2 0+(-814314753/2000000000 : ℝ)*X 2 1+(-1229760227/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316032_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-381771/50000 : ℝ) < ((-177257/100000 : ℝ)*P 0+(-177257/100000 : ℝ)*P 1+(-177257/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-381771/50000 : ℝ) < (-9528829380649703521282404501/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38919/500000000000 : ℝ)*(base1) + (1313/200000000000 : ℝ)*(base5) + (27319/1000000000000 : ℝ)*(base10) + (380885180917/1000000000000 : ℝ)*(base39) + (199025483613/500000000000 : ℝ)*(base40) + (16097/500000000000 : ℝ)*(base44) + (21016732367/200000000000 : ℝ)*(base50) + (21192569371/50000000000 : ℝ)*(base60) + (177257/100000 : ℝ)*(major_s0_0) + (886284983903/500000000000 : ℝ)*(major_s0_1) + (177257/100000 : ℝ)*(major_s0_2) + (19851728271/7812500000 : ℝ)*(sp_s0_0) + (317627641997/125000000000 : ℝ)*(sp_s0_1) + (1270510587367/500000000000 : ℝ)*(sp_s0_2) + (249999970851/250000000000 : ℝ)*(sp_s0_6) + (2541021168169/1000000000000 : ℝ)*(f.sum) + (613811809422303/5000000000000000000000000000 : ℝ)*base62 + (281048957/625000000000000000000 : ℝ)*base65 + (154887783468167/2500000000000000000000000000 : ℝ)*base67 + (219415089/5000000000000000000000 : ℝ)*base68 + (521564069/5000000000000000000000 : ℝ)*base70 + (1370785549/2500000000000000000000 : ℝ)*base73 + (156034577697/5000000000000000000000000000 : ℝ)*base75 + (2222974487/5000000000000000000000 : ℝ)*base77 + (1196850949968167/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p016_b015 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 30 ≤ c.val) (hhi : c.val < 33)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=30 ∨ c=31 ∨ c=32 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c316030 p hpa (by linarith only [hpb]) X hX
  · exact collision_c316031 p hpa (by linarith only [hpb]) X hX
  · exact collision_c316032 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (39/8 : ℝ))
    (c : Fin 88) (hlo : 30 ≤ c.val) (hhi : c.val < 33)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p016_b015 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

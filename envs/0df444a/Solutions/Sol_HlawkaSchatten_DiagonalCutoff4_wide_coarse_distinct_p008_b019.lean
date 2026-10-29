-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p008_b019
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:43:08.476517+00:00
-- url     : https://prove2.me/submissions/f680422b-4afb-4fec-ad94-36fd72d38e98

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308031_s0
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308031_s1
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308031_s2
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c308031_s3
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
theorem HlawkaSchatten.DiagonalCutoff4.collision_c308031 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]]) : False := by
  have h0 := collision_c308031_s0 p hpa hpb X hX
  have h1 := collision_c308031_s1 p hpa hpb X hX h0
  have h2 := collision_c308031_s2 p hpa hpb X hX h1
  exact collision_c308031_s3 p hpa hpb X hX h2

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
theorem collision_support_c308030_s0_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3504757821/5000000000 : ℝ)*x 0 + (-557637329/5000000000 : ℝ)*x 1 + (-4060275797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3504757821/5000000000 : ℝ)^35 ≤ (6309078598571/10000000000000 : ℝ)^27 := by
    have hnat : (3504757821 : ℕ)^35*10000000000000^27 ≤ 6309078598571^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3504757821 5000000000 6309078598571 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (557637329/5000000000 : ℝ)^35 ≤ (2911351239263/50000000000000 : ℝ)^27 := by
    have hnat : (557637329 : ℕ)^35*50000000000000^27 ≤ 2911351239263^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557637329 5000000000 2911351239263 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4060275797/10000000000 : ℝ)^35 ≤ (31086511521253/100000000000000 : ℝ)^27 := by
    have hnat : (4060275797 : ℕ)^35*100000000000000^27 ≤ 31086511521253^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4060275797 10000000000 31086511521253 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3504757821/5000000000 : ℝ), (-557637329/5000000000 : ℝ), (-4060275797/10000000000 : ℝ)] ![(6309078598571/10000000000000 : ℝ), (2911351239263/50000000000000 : ℝ), (31086511521253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3504757821/5000000000 : ℝ)|^35 ≤ (6309078598571/10000000000000 : ℝ)^27
        have hw : |(3504757821/5000000000 : ℝ)|=(3504757821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-557637329/5000000000 : ℝ)|^35 ≤ (2911351239263/50000000000000 : ℝ)^27
        have hw : |(-557637329/5000000000 : ℝ)|=(557637329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4060275797/10000000000 : ℝ)|^35 ≤ (31086511521253/100000000000000 : ℝ)^27
        have hw : |(-4060275797/10000000000 : ℝ)|=(4060275797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308030_s0_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (271745909/1000000000 : ℝ)*x 0 + (1379901271/2500000000 : ℝ)*x 1 + (4473069411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271745909/1000000000 : ℝ)^35 ≤ (18471731691531/100000000000000 : ℝ)^27 := by
    have hnat : (271745909 : ℕ)^35*100000000000000^27 ≤ 18471731691531^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271745909 1000000000 18471731691531 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379901271/2500000000 : ℝ)^35 ≤ (46284577538217/100000000000000 : ℝ)^27 := by
    have hnat : (1379901271 : ℕ)^35*100000000000000^27 ≤ 46284577538217^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379901271 2500000000 46284577538217 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4473069411/10000000000 : ℝ)^35 ≤ (2202730671883/6250000000000 : ℝ)^27 := by
    have hnat : (4473069411 : ℕ)^35*6250000000000^27 ≤ 2202730671883^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473069411 10000000000 2202730671883 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271745909/1000000000 : ℝ), (1379901271/2500000000 : ℝ), (4473069411/10000000000 : ℝ)] ![(18471731691531/100000000000000 : ℝ), (46284577538217/100000000000000 : ℝ), (2202730671883/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271745909/1000000000 : ℝ)|^35 ≤ (18471731691531/100000000000000 : ℝ)^27
        have hw : |(271745909/1000000000 : ℝ)|=(271745909/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1379901271/2500000000 : ℝ)|^35 ≤ (46284577538217/100000000000000 : ℝ)^27
        have hw : |(1379901271/2500000000 : ℝ)|=(1379901271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4473069411/10000000000 : ℝ)|^35 ≤ (2202730671883/6250000000000 : ℝ)^27
        have hw : |(4473069411/10000000000 : ℝ)|=(4473069411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308030_s0_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-538780179/2000000000 : ℝ)*x 0 + (3584792701/10000000000 : ℝ)*x 1 + (-6330430353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538780179/2000000000 : ℝ)^35 ≤ (18264416266987/100000000000000 : ℝ)^27 := by
    have hnat : (538780179 : ℕ)^35*100000000000000^27 ≤ 18264416266987^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538780179 2000000000 18264416266987 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3584792701/10000000000 : ℝ)^35 ≤ (26451688138277/100000000000000 : ℝ)^27 := by
    have hnat : (3584792701 : ℕ)^35*100000000000000^27 ≤ 26451688138277^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3584792701 10000000000 26451688138277 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6330430353/10000000000 : ℝ)^35 ≤ (55283895585813/100000000000000 : ℝ)^27 := by
    have hnat : (6330430353 : ℕ)^35*100000000000000^27 ≤ 55283895585813^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6330430353 10000000000 55283895585813 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-538780179/2000000000 : ℝ), (3584792701/10000000000 : ℝ), (-6330430353/10000000000 : ℝ)] ![(18264416266987/100000000000000 : ℝ), (26451688138277/100000000000000 : ℝ), (55283895585813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-538780179/2000000000 : ℝ)|^35 ≤ (18264416266987/100000000000000 : ℝ)^27
        have hw : |(-538780179/2000000000 : ℝ)|=(538780179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3584792701/10000000000 : ℝ)|^35 ≤ (26451688138277/100000000000000 : ℝ)^27
        have hw : |(3584792701/10000000000 : ℝ)|=(3584792701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6330430353/10000000000 : ℝ)|^35 ≤ (55283895585813/100000000000000 : ℝ)^27
        have hw : |(-6330430353/10000000000 : ℝ)|=(6330430353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308030_s0_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7413676221/10000000000 : ℝ)*x 0 + (-11717549/500000000 : ℝ)*x 1 + (-4090138141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7413676221/10000000000 : ℝ)^35 ≤ (67846126312867/100000000000000 : ℝ)^27 := by
    have hnat : (7413676221 : ℕ)^35*100000000000000^27 ≤ 67846126312867^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7413676221 10000000000 67846126312867 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11717549/500000000 : ℝ)^35 ≤ (12041604603/1562500000000 : ℝ)^27 := by
    have hnat : (11717549 : ℕ)^35*1562500000000^27 ≤ 12041604603^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11717549 500000000 12041604603 1562500000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4090138141/10000000000 : ℝ)^35 ≤ (31383210985983/100000000000000 : ℝ)^27 := by
    have hnat : (4090138141 : ℕ)^35*100000000000000^27 ≤ 31383210985983^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4090138141 10000000000 31383210985983 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7413676221/10000000000 : ℝ), (-11717549/500000000 : ℝ), (-4090138141/10000000000 : ℝ)] ![(67846126312867/100000000000000 : ℝ), (12041604603/1562500000000 : ℝ), (31383210985983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7413676221/10000000000 : ℝ)|^35 ≤ (67846126312867/100000000000000 : ℝ)^27
        have hw : |(7413676221/10000000000 : ℝ)|=(7413676221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11717549/500000000 : ℝ)|^35 ≤ (12041604603/1562500000000 : ℝ)^27
        have hw : |(-11717549/500000000 : ℝ)|=(11717549/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4090138141/10000000000 : ℝ)|^35 ≤ (31383210985983/100000000000000 : ℝ)^27
        have hw : |(-4090138141/10000000000 : ℝ)|=(4090138141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308030_s0_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (760771379/5000000000 : ℝ)*x 0 + (7166430369/10000000000 : ℝ)*x 1 + (893872941/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (760771379/5000000000 : ℝ)^35 ≤ (87095955269/1000000000000 : ℝ)^27 := by
    have hnat : (760771379 : ℕ)^35*1000000000000^27 ≤ 87095955269^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760771379 5000000000 87095955269 1000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7166430369/10000000000 : ℝ)^35 ≤ (8115955916389/12500000000000 : ℝ)^27 := by
    have hnat : (7166430369 : ℕ)^35*12500000000000^27 ≤ 8115955916389^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7166430369 10000000000 8115955916389 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (893872941/2500000000 : ℝ)^35 ≤ (6590689280117/25000000000000 : ℝ)^27 := by
    have hnat : (893872941 : ℕ)^35*25000000000000^27 ≤ 6590689280117^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893872941 2500000000 6590689280117 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(760771379/5000000000 : ℝ), (7166430369/10000000000 : ℝ), (893872941/2500000000 : ℝ)] ![(87095955269/1000000000000 : ℝ), (8115955916389/12500000000000 : ℝ), (6590689280117/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(760771379/5000000000 : ℝ)|^35 ≤ (87095955269/1000000000000 : ℝ)^27
        have hw : |(760771379/5000000000 : ℝ)|=(760771379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7166430369/10000000000 : ℝ)|^35 ≤ (8115955916389/12500000000000 : ℝ)^27
        have hw : |(7166430369/10000000000 : ℝ)|=(7166430369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(893872941/2500000000 : ℝ)|^35 ≤ (6590689280117/25000000000000 : ℝ)^27
        have hw : |(893872941/2500000000 : ℝ)|=(893872941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308030_s0_12 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (133362661/500000000 : ℝ)*x 0 + (987070989/1250000000 : ℝ)*x 1 + (-367882067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133362661/500000000 : ℝ)^35 ≤ (9015279897871/50000000000000 : ℝ)^27 := by
    have hnat : (133362661 : ℕ)^35*50000000000000^27 ≤ 9015279897871^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133362661 500000000 9015279897871 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (987070989/1250000000 : ℝ)^35 ≤ (18407285727109/25000000000000 : ℝ)^27 := by
    have hnat : (987070989 : ℕ)^35*25000000000000^27 ≤ 18407285727109^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987070989 1250000000 18407285727109 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (367882067/2500000000 : ℝ)^35 ≤ (8340297275071/100000000000000 : ℝ)^27 := by
    have hnat : (367882067 : ℕ)^35*100000000000000^27 ≤ 8340297275071^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367882067 2500000000 8340297275071 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133362661/500000000 : ℝ), (987070989/1250000000 : ℝ), (-367882067/2500000000 : ℝ)] ![(9015279897871/50000000000000 : ℝ), (18407285727109/25000000000000 : ℝ), (8340297275071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133362661/500000000 : ℝ)|^35 ≤ (9015279897871/50000000000000 : ℝ)^27
        have hw : |(133362661/500000000 : ℝ)|=(133362661/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(987070989/1250000000 : ℝ)|^35 ≤ (18407285727109/25000000000000 : ℝ)^27
        have hw : |(987070989/1250000000 : ℝ)|=(987070989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-367882067/2500000000 : ℝ)|^35 ≤ (8340297275071/100000000000000 : ℝ)^27
        have hw : |(-367882067/2500000000 : ℝ)|=(367882067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308030_s0_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3946657223/10000000000 : ℝ)*x 0 + (1132589909/2500000000 : ℝ)*x 1 + (-2185586149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3946657223/10000000000 : ℝ)^35 ≤ (29963578394297/100000000000000 : ℝ)^27 := by
    have hnat : (3946657223 : ℕ)^35*100000000000000^27 ≤ 29963578394297^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3946657223 10000000000 29963578394297 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132589909/2500000000 : ℝ)^35 ≤ (8957484685327/25000000000000 : ℝ)^27 := by
    have hnat : (1132589909 : ℕ)^35*25000000000000^27 ≤ 8957484685327^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132589909 2500000000 8957484685327 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2185586149/5000000000 : ℝ)^35 ≤ (855162071143/2500000000000 : ℝ)^27 := by
    have hnat : (2185586149 : ℕ)^35*2500000000000^27 ≤ 855162071143^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185586149 5000000000 855162071143 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3946657223/10000000000 : ℝ), (1132589909/2500000000 : ℝ), (-2185586149/5000000000 : ℝ)] ![(29963578394297/100000000000000 : ℝ), (8957484685327/25000000000000 : ℝ), (855162071143/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3946657223/10000000000 : ℝ)|^35 ≤ (29963578394297/100000000000000 : ℝ)^27
        have hw : |(-3946657223/10000000000 : ℝ)|=(3946657223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1132589909/2500000000 : ℝ)|^35 ≤ (8957484685327/25000000000000 : ℝ)^27
        have hw : |(1132589909/2500000000 : ℝ)|=(1132589909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2185586149/5000000000 : ℝ)|^35 ≤ (855162071143/2500000000000 : ℝ)^27
        have hw : |(-2185586149/5000000000 : ℝ)|=(2185586149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308030_s0_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7468711317/10000000000 : ℝ)*x 0 + (-1170848087/10000000000 : ℝ)*x 1 + (-1731821521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7468711317/10000000000 : ℝ)^35 ≤ (34249863111657/50000000000000 : ℝ)^27 := by
    have hnat : (7468711317 : ℕ)^35*50000000000000^27 ≤ 34249863111657^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7468711317 10000000000 34249863111657 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1170848087/10000000000 : ℝ)^35 ≤ (6201556630363/100000000000000 : ℝ)^27 := by
    have hnat : (1170848087 : ℕ)^35*100000000000000^27 ≤ 6201556630363^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170848087 10000000000 6201556630363 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1731821521/5000000000 : ℝ)^35 ≤ (25298717129023/100000000000000 : ℝ)^27 := by
    have hnat : (1731821521 : ℕ)^35*100000000000000^27 ≤ 25298717129023^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1731821521 5000000000 25298717129023 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7468711317/10000000000 : ℝ), (-1170848087/10000000000 : ℝ), (-1731821521/5000000000 : ℝ)] ![(34249863111657/50000000000000 : ℝ), (6201556630363/100000000000000 : ℝ), (25298717129023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7468711317/10000000000 : ℝ)|^35 ≤ (34249863111657/50000000000000 : ℝ)^27
        have hw : |(7468711317/10000000000 : ℝ)|=(7468711317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1170848087/10000000000 : ℝ)|^35 ≤ (6201556630363/100000000000000 : ℝ)^27
        have hw : |(-1170848087/10000000000 : ℝ)|=(1170848087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1731821521/5000000000 : ℝ)|^35 ≤ (25298717129023/100000000000000 : ℝ)^27
        have hw : |(-1731821521/5000000000 : ℝ)|=(1731821521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308030_s0_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1847389349/10000000000 : ℝ)*x 0 + (2606924497/5000000000 : ℝ)*x 1 + (5475963493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1847389349/10000000000 : ℝ)^35 ≤ (11200629102731/100000000000000 : ℝ)^27 := by
    have hnat : (1847389349 : ℕ)^35*100000000000000^27 ≤ 11200629102731^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1847389349 10000000000 11200629102731 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606924497/5000000000 : ℝ)^35 ≤ (42988624045743/100000000000000 : ℝ)^27 := by
    have hnat : (2606924497 : ℕ)^35*100000000000000^27 ≤ 42988624045743^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606924497 5000000000 42988624045743 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5475963493/10000000000 : ℝ)^35 ≤ (45810746840239/100000000000000 : ℝ)^27 := by
    have hnat : (5475963493 : ℕ)^35*100000000000000^27 ≤ 45810746840239^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475963493 10000000000 45810746840239 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1847389349/10000000000 : ℝ), (2606924497/5000000000 : ℝ), (5475963493/10000000000 : ℝ)] ![(11200629102731/100000000000000 : ℝ), (42988624045743/100000000000000 : ℝ), (45810746840239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1847389349/10000000000 : ℝ)|^35 ≤ (11200629102731/100000000000000 : ℝ)^27
        have hw : |(1847389349/10000000000 : ℝ)|=(1847389349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606924497/5000000000 : ℝ)|^35 ≤ (42988624045743/100000000000000 : ℝ)^27
        have hw : |(2606924497/5000000000 : ℝ)|=(2606924497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5475963493/10000000000 : ℝ)|^35 ≤ (45810746840239/100000000000000 : ℝ)^27
        have hw : |(5475963493/10000000000 : ℝ)|=(5475963493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308030_s0_19 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3036556709/10000000000 : ℝ)*x 0 + (6592297851/10000000000 : ℝ)*x 1 + (-2934070151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3036556709/10000000000 : ℝ)^35 ≤ (853243350247/4000000000000 : ℝ)^27 := by
    have hnat : (3036556709 : ℕ)^35*4000000000000^27 ≤ 853243350247^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3036556709 10000000000 853243350247 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6592297851/10000000000 : ℝ)^35 ≤ (58266388690519/100000000000000 : ℝ)^27 := by
    have hnat : (6592297851 : ℕ)^35*100000000000000^27 ≤ 58266388690519^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6592297851 10000000000 58266388690519 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2934070151/10000000000 : ℝ)^35 ≤ (20402527537457/100000000000000 : ℝ)^27 := by
    have hnat : (2934070151 : ℕ)^35*100000000000000^27 ≤ 20402527537457^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2934070151 10000000000 20402527537457 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3036556709/10000000000 : ℝ), (6592297851/10000000000 : ℝ), (-2934070151/10000000000 : ℝ)] ![(853243350247/4000000000000 : ℝ), (58266388690519/100000000000000 : ℝ), (20402527537457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3036556709/10000000000 : ℝ)|^35 ≤ (853243350247/4000000000000 : ℝ)^27
        have hw : |(3036556709/10000000000 : ℝ)|=(3036556709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6592297851/10000000000 : ℝ)|^35 ≤ (58266388690519/100000000000000 : ℝ)^27
        have hw : |(6592297851/10000000000 : ℝ)|=(6592297851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2934070151/10000000000 : ℝ)|^35 ≤ (20402527537457/100000000000000 : ℝ)^27
        have hw : |(-2934070151/10000000000 : ℝ)|=(2934070151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308030_s0_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-94461187/500000000 : ℝ)*x 0 + (5557869883/10000000000 : ℝ)*x 1 + (-5099320173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94461187/500000000 : ℝ)^35 ≤ (1441314837463/12500000000000 : ℝ)^27 := by
    have hnat : (94461187 : ℕ)^35*12500000000000^27 ≤ 1441314837463^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94461187 500000000 1441314837463 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5557869883/10000000000 : ℝ)^35 ≤ (46700945305279/100000000000000 : ℝ)^27 := by
    have hnat : (5557869883 : ℕ)^35*100000000000000^27 ≤ 46700945305279^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5557869883 10000000000 46700945305279 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5099320173/10000000000 : ℝ)^35 ≤ (8353707196599/20000000000000 : ℝ)^27 := by
    have hnat : (5099320173 : ℕ)^35*20000000000000^27 ≤ 8353707196599^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5099320173 10000000000 8353707196599 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-94461187/500000000 : ℝ), (5557869883/10000000000 : ℝ), (-5099320173/10000000000 : ℝ)] ![(1441314837463/12500000000000 : ℝ), (46700945305279/100000000000000 : ℝ), (8353707196599/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-94461187/500000000 : ℝ)|^35 ≤ (1441314837463/12500000000000 : ℝ)^27
        have hw : |(-94461187/500000000 : ℝ)|=(94461187/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5557869883/10000000000 : ℝ)|^35 ≤ (46700945305279/100000000000000 : ℝ)^27
        have hw : |(5557869883/10000000000 : ℝ)|=(5557869883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5099320173/10000000000 : ℝ)|^35 ≤ (8353707196599/20000000000000 : ℝ)^27
        have hw : |(-5099320173/10000000000 : ℝ)|=(5099320173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308030_s0_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (342772387/400000000 : ℝ)*x 0 + (-242079127/5000000000 : ℝ)*x 1 + (-2451706981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (342772387/400000000 : ℝ)^35 ≤ (20465292029273/25000000000000 : ℝ)^27 := by
    have hnat : (342772387 : ℕ)^35*25000000000000^27 ≤ 20465292029273^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342772387 400000000 20465292029273 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (242079127/5000000000 : ℝ)^35 ≤ (1974030958951/100000000000000 : ℝ)^27 := by
    have hnat : (242079127 : ℕ)^35*100000000000000^27 ≤ 1974030958951^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242079127 5000000000 1974030958951 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2451706981/10000000000 : ℝ)^35 ≤ (3232960183621/20000000000000 : ℝ)^27 := by
    have hnat : (2451706981 : ℕ)^35*20000000000000^27 ≤ 3232960183621^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2451706981 10000000000 3232960183621 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(342772387/400000000 : ℝ), (-242079127/5000000000 : ℝ), (-2451706981/10000000000 : ℝ)] ![(20465292029273/25000000000000 : ℝ), (1974030958951/100000000000000 : ℝ), (3232960183621/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(342772387/400000000 : ℝ)|^35 ≤ (20465292029273/25000000000000 : ℝ)^27
        have hw : |(342772387/400000000 : ℝ)|=(342772387/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-242079127/5000000000 : ℝ)|^35 ≤ (1974030958951/100000000000000 : ℝ)^27
        have hw : |(-242079127/5000000000 : ℝ)|=(242079127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2451706981/10000000000 : ℝ)|^35 ≤ (3232960183621/20000000000000 : ℝ)^27
        have hw : |(-2451706981/10000000000 : ℝ)|=(2451706981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308030_s0_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (878315647/5000000000 : ℝ)*x 0 + (5993378749/10000000000 : ℝ)*x 1 + (2370715867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (878315647/5000000000 : ℝ)^35 ≤ (10492579758529/100000000000000 : ℝ)^27 := by
    have hnat : (878315647 : ℕ)^35*100000000000000^27 ≤ 10492579758529^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878315647 5000000000 10492579758529 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5993378749/10000000000 : ℝ)^35 ≤ (402333976017/781250000000 : ℝ)^27 := by
    have hnat : (5993378749 : ℕ)^35*781250000000^27 ≤ 402333976017^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5993378749 10000000000 402333976017 781250000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2370715867/5000000000 : ℝ)^35 ≤ (296942744523/781250000000 : ℝ)^27 := by
    have hnat : (2370715867 : ℕ)^35*781250000000^27 ≤ 296942744523^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2370715867 5000000000 296942744523 781250000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(878315647/5000000000 : ℝ), (5993378749/10000000000 : ℝ), (2370715867/5000000000 : ℝ)] ![(10492579758529/100000000000000 : ℝ), (402333976017/781250000000 : ℝ), (296942744523/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(878315647/5000000000 : ℝ)|^35 ≤ (10492579758529/100000000000000 : ℝ)^27
        have hw : |(878315647/5000000000 : ℝ)|=(878315647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5993378749/10000000000 : ℝ)|^35 ≤ (402333976017/781250000000 : ℝ)^27
        have hw : |(5993378749/10000000000 : ℝ)|=(5993378749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2370715867/5000000000 : ℝ)|^35 ≤ (296942744523/781250000000 : ℝ)^27
        have hw : |(2370715867/5000000000 : ℝ)|=(2370715867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308030_s0_25 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5272355507/10000000000 : ℝ)*x 0 + (2827997353/5000000000 : ℝ)*x 1 + (-1508437819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5272355507/10000000000 : ℝ)^35 ≤ (21807491352043/50000000000000 : ℝ)^27 := by
    have hnat : (5272355507 : ℕ)^35*50000000000000^27 ≤ 21807491352043^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272355507 10000000000 21807491352043 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2827997353/5000000000 : ℝ)^35 ≤ (1492891851613/3125000000000 : ℝ)^27 := by
    have hnat : (2827997353 : ℕ)^35*3125000000000^27 ≤ 1492891851613^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2827997353 5000000000 1492891851613 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1508437819/10000000000 : ℝ)^35 ≤ (8612478031121/100000000000000 : ℝ)^27 := by
    have hnat : (1508437819 : ℕ)^35*100000000000000^27 ≤ 8612478031121^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1508437819 10000000000 8612478031121 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5272355507/10000000000 : ℝ), (2827997353/5000000000 : ℝ), (-1508437819/10000000000 : ℝ)] ![(21807491352043/50000000000000 : ℝ), (1492891851613/3125000000000 : ℝ), (8612478031121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5272355507/10000000000 : ℝ)|^35 ≤ (21807491352043/50000000000000 : ℝ)^27
        have hw : |(5272355507/10000000000 : ℝ)|=(5272355507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2827997353/5000000000 : ℝ)|^35 ≤ (1492891851613/3125000000000 : ℝ)^27
        have hw : |(2827997353/5000000000 : ℝ)|=(2827997353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1508437819/10000000000 : ℝ)|^35 ≤ (8612478031121/100000000000000 : ℝ)^27
        have hw : |(-1508437819/10000000000 : ℝ)|=(1508437819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308030_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1812191879/5000000000 : ℝ)*x 0 + (4669426101/10000000000 : ℝ)*x 1 + (-4537862859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1812191879/5000000000 : ℝ)^35 ≤ (13415501079111/50000000000000 : ℝ)^27 := by
    have hnat : (1812191879 : ℕ)^35*50000000000000^27 ≤ 13415501079111^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1812191879 5000000000 13415501079111 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4669426101/10000000000 : ℝ)^35 ≤ (2328882223407/6250000000000 : ℝ)^27 := by
    have hnat : (4669426101 : ℕ)^35*6250000000000^27 ≤ 2328882223407^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4669426101 10000000000 2328882223407 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4537862859/10000000000 : ℝ)^35 ≤ (7181376451419/20000000000000 : ℝ)^27 := by
    have hnat : (4537862859 : ℕ)^35*20000000000000^27 ≤ 7181376451419^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4537862859 10000000000 7181376451419 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1812191879/5000000000 : ℝ), (4669426101/10000000000 : ℝ), (-4537862859/10000000000 : ℝ)] ![(13415501079111/50000000000000 : ℝ), (2328882223407/6250000000000 : ℝ), (7181376451419/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1812191879/5000000000 : ℝ)|^35 ≤ (13415501079111/50000000000000 : ℝ)^27
        have hw : |(-1812191879/5000000000 : ℝ)|=(1812191879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4669426101/10000000000 : ℝ)|^35 ≤ (2328882223407/6250000000000 : ℝ)^27
        have hw : |(4669426101/10000000000 : ℝ)|=(4669426101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4537862859/10000000000 : ℝ)|^35 ≤ (7181376451419/20000000000000 : ℝ)^27
        have hw : |(-4537862859/10000000000 : ℝ)|=(4537862859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308030_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1139679279/2000000000 : ℝ)*x 0 + (-1315376421/5000000000 : ℝ)*x 1 + (-217793479/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1139679279/2000000000 : ℝ)^35 ≤ (48237309155407/100000000000000 : ℝ)^27 := by
    have hnat : (1139679279 : ℕ)^35*100000000000000^27 ≤ 48237309155407^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139679279 2000000000 48237309155407 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315376421/5000000000 : ℝ)^35 ≤ (17711360154829/100000000000000 : ℝ)^27 := by
    have hnat : (1315376421 : ℕ)^35*100000000000000^27 ≤ 17711360154829^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315376421 5000000000 17711360154829 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217793479/500000000 : ℝ)^35 ≤ (34051330671837/100000000000000 : ℝ)^27 := by
    have hnat : (217793479 : ℕ)^35*100000000000000^27 ≤ 34051330671837^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217793479 500000000 34051330671837 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1139679279/2000000000 : ℝ), (-1315376421/5000000000 : ℝ), (-217793479/500000000 : ℝ)] ![(48237309155407/100000000000000 : ℝ), (17711360154829/100000000000000 : ℝ), (34051330671837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1139679279/2000000000 : ℝ)|^35 ≤ (48237309155407/100000000000000 : ℝ)^27
        have hw : |(1139679279/2000000000 : ℝ)|=(1139679279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1315376421/5000000000 : ℝ)|^35 ≤ (17711360154829/100000000000000 : ℝ)^27
        have hw : |(-1315376421/5000000000 : ℝ)|=(1315376421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-217793479/500000000 : ℝ)|^35 ≤ (34051330671837/100000000000000 : ℝ)^27
        have hw : |(-217793479/500000000 : ℝ)|=(217793479/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308030_s1_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (439876793/1250000000 : ℝ)*x 0 + (1223849/2500000 : ℝ)*x 1 + (2202968223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (439876793/1250000000 : ℝ)^35 ≤ (25824223414571/100000000000000 : ℝ)^27 := by
    have hnat : (439876793 : ℕ)^35*100000000000000^27 ≤ 25824223414571^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439876793 1250000000 25824223414571 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1223849/2500000 : ℝ)^35 ≤ (19808113486773/50000000000000 : ℝ)^27 := by
    have hnat : (1223849 : ℕ)^35*50000000000000^27 ≤ 19808113486773^27*2500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1223849 2500000 19808113486773 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2202968223/5000000000 : ℝ)^35 ≤ (17279774795413/50000000000000 : ℝ)^27 := by
    have hnat : (2202968223 : ℕ)^35*50000000000000^27 ≤ 17279774795413^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202968223 5000000000 17279774795413 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(439876793/1250000000 : ℝ), (1223849/2500000 : ℝ), (2202968223/5000000000 : ℝ)] ![(25824223414571/100000000000000 : ℝ), (19808113486773/50000000000000 : ℝ), (17279774795413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(439876793/1250000000 : ℝ)|^35 ≤ (25824223414571/100000000000000 : ℝ)^27
        have hw : |(439876793/1250000000 : ℝ)|=(439876793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1223849/2500000 : ℝ)|^35 ≤ (19808113486773/50000000000000 : ℝ)^27
        have hw : |(1223849/2500000 : ℝ)|=(1223849/2500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2202968223/5000000000 : ℝ)|^35 ≤ (17279774795413/50000000000000 : ℝ)^27
        have hw : |(2202968223/5000000000 : ℝ)|=(2202968223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308030_s1_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4119786493/10000000000 : ℝ)*x 0 + (5489664227/10000000000 : ℝ)*x 1 + (-3149175911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4119786493/10000000000 : ℝ)^35 ≤ (7919604994551/25000000000000 : ℝ)^27 := by
    have hnat : (4119786493 : ℕ)^35*25000000000000^27 ≤ 7919604994551^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4119786493 10000000000 7919604994551 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5489664227/10000000000 : ℝ)^35 ≤ (22979690014549/50000000000000 : ℝ)^27 := by
    have hnat : (5489664227 : ℕ)^35*50000000000000^27 ≤ 22979690014549^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489664227 10000000000 22979690014549 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3149175911/10000000000 : ℝ)^35 ≤ (22362199976161/100000000000000 : ℝ)^27 := by
    have hnat : (3149175911 : ℕ)^35*100000000000000^27 ≤ 22362199976161^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3149175911 10000000000 22362199976161 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4119786493/10000000000 : ℝ), (5489664227/10000000000 : ℝ), (-3149175911/10000000000 : ℝ)] ![(7919604994551/25000000000000 : ℝ), (22979690014549/50000000000000 : ℝ), (22362199976161/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4119786493/10000000000 : ℝ)|^35 ≤ (7919604994551/25000000000000 : ℝ)^27
        have hw : |(4119786493/10000000000 : ℝ)|=(4119786493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5489664227/10000000000 : ℝ)|^35 ≤ (22979690014549/50000000000000 : ℝ)^27
        have hw : |(5489664227/10000000000 : ℝ)|=(5489664227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3149175911/10000000000 : ℝ)|^35 ≤ (22362199976161/100000000000000 : ℝ)^27
        have hw : |(-3149175911/10000000000 : ℝ)|=(3149175911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308030 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
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
  have s0_pow0 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1771466939089177/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (17/4 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^17 ≤ (1 : ℝ)^4 := by
      have hnat : (1 : ℕ)^17*1^4 ≤ 1^4*1^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11771466939089177/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2 : ℝ)^4 ≤ (11771466939089177/10000000000000000 : ℝ)^17 := by
      have hnat : (2 : ℕ)^4*10000000000000000^17 ≤ 11771466939089177^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11771466939089177 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11771466939089177/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (12949822766824881/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (3 : ℝ)^4 ≤ (12949822766824881/10000000000000000 : ℝ)^17 := by
      have hnat : (3 : ℕ)^4*10000000000000000^17 ≤ 12949822766824881^17*1^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 12949822766824881 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12949822766824881/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1 : ℝ)) (alpha := (1771466939089177/10000000000000000 : ℝ)) (beta := (147294478466963/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1771466939089177/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(147294478466963/1250000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_1 : ((3504757821/5000000000 : ℝ)*X 1 0+(-557637329/5000000000 : ℝ)*X 1 1+(-4060275797/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308030_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((271745909/1000000000 : ℝ)*X 2 0+(1379901271/2500000000 : ℝ)*X 2 1+(4473069411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308030_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-538780179/2000000000 : ℝ)*X 0 0+(3584792701/10000000000 : ℝ)*X 0 1+(-6330430353/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308030_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((7413676221/10000000000 : ℝ)*X 1 0+(-11717549/500000000 : ℝ)*X 1 1+(-4090138141/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308030_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((760771379/5000000000 : ℝ)*X 2 0+(7166430369/10000000000 : ℝ)*X 2 1+(893872941/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308030_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((133362661/500000000 : ℝ)*X 0 0+(987070989/1250000000 : ℝ)*X 0 1+(-367882067/2500000000 : ℝ)*X 0 2+(133362661/500000000 : ℝ)*X 1 0+(987070989/1250000000 : ℝ)*X 1 1+(-367882067/2500000000 : ℝ)*X 1 2+(133362661/500000000 : ℝ)*X 2 0+(987070989/1250000000 : ℝ)*X 2 1+(-367882067/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308030_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-3946657223/10000000000 : ℝ)*X 0 0+(1132589909/2500000000 : ℝ)*X 0 1+(-2185586149/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308030_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((7468711317/10000000000 : ℝ)*X 1 0+(-1170848087/10000000000 : ℝ)*X 1 1+(-1731821521/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308030_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1847389349/10000000000 : ℝ)*X 2 0+(2606924497/5000000000 : ℝ)*X 2 1+(5475963493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308030_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((3036556709/10000000000 : ℝ)*X 0 0+(6592297851/10000000000 : ℝ)*X 0 1+(-2934070151/10000000000 : ℝ)*X 0 2+(3036556709/10000000000 : ℝ)*X 1 0+(6592297851/10000000000 : ℝ)*X 1 1+(-2934070151/10000000000 : ℝ)*X 1 2+(3036556709/10000000000 : ℝ)*X 2 0+(6592297851/10000000000 : ℝ)*X 2 1+(-2934070151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308030_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-94461187/500000000 : ℝ)*X 0 0+(5557869883/10000000000 : ℝ)*X 0 1+(-5099320173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308030_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((342772387/400000000 : ℝ)*X 1 0+(-242079127/5000000000 : ℝ)*X 1 1+(-2451706981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308030_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((878315647/5000000000 : ℝ)*X 2 0+(5993378749/10000000000 : ℝ)*X 2 1+(2370715867/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308030_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((5272355507/10000000000 : ℝ)*X 0 0+(2827997353/5000000000 : ℝ)*X 0 1+(-1508437819/10000000000 : ℝ)*X 0 2+(5272355507/10000000000 : ℝ)*X 1 0+(2827997353/5000000000 : ℝ)*X 1 1+(-1508437819/10000000000 : ℝ)*X 1 2+(5272355507/10000000000 : ℝ)*X 2 0+(2827997353/5000000000 : ℝ)*X 2 1+(-1508437819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308030_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((40639/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40639/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11567397349948708576791/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (381920140999/500000000000 : ℝ)*(base39) + (205254022433/250000000000 : ℝ)*(base49) + (1065015206487/1000000000000 : ℝ)*(base50) + (207669384741/500000000000 : ℝ)*(base60) + (3303301953559/1000000000000 : ℝ)*(major_s0_0) + (3303301953559/1000000000000 : ℝ)*(major_s0_1) + (3303301953559/1000000000000 : ℝ)*(major_s0_2) + (1936793/20000000000 : ℝ)*(sp_s0_1) + (4498685813817/1000000000000 : ℝ)*(sp_s0_7) + (140581534131/31250000000 : ℝ)*(sp_s0_8) + (4498635908761/1000000000000 : ℝ)*(sp_s0_9) + (2107894119467/1000000000000 : ℝ)*(sp_s0_12) + (804721/40000000000 : ℝ)*(sp_s0_20) + (70023081/1000000000000 : ℝ)*(sp_s0_22) + (2107894119467/1000000000000 : ℝ)*(f.failure) + (2249352965921/500000000000 : ℝ)*(f.sum) + (62754161/400000000000000000000 : ℝ)*base62 + (1462158129771317/1250000000000000000000000000 : ℝ)*base65 + (251262202021317/1250000000000000000000000000 : ℝ)*base67 + (1372038741530943/10000000000000000000000000000 : ℝ)*base69 + (8477337903701479/10000000000000000000000000000 : ℝ)*base71 + (673432748478683/1250000000000000000000000000 : ℝ)*base72 + (4683922394469057/10000000000000000000000000000 : ℝ)*base75 + (7505232831530943/10000000000000000000000000000 : ℝ)*base77 + (165612110396317/625000000000000000000000000 : ℝ)*base79 + (106963/100000000000000000 : ℝ)*base86 + (106963/100000000000000000 : ℝ)*base88 + (106963/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(1537/12500 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(1537/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (14888282518024613916699/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17497/6250000000 : ℝ)*(base3) + (591344302431/1000000000000 : ℝ)*(base39) + (263937221863/1000000000000 : ℝ)*(base49) + (44732189901/500000000000 : ℝ)*(base60) + (2649057025879/1000000000000 : ℝ)*(major_s0_0) + (2649057025879/1000000000000 : ℝ)*(major_s0_1) + (2649057025879/1000000000000 : ℝ)*(major_s0_2) + (5884149/1000000000000 : ℝ)*(sp_s0_1) + (2781609/500000000000 : ℝ)*(sp_s0_2) + (10267279/500000000000 : ℝ)*(sp_s0_8) + (3607703945683/1000000000000 : ℝ)*(sp_s0_13) + (721536065299/200000000000 : ℝ)*(sp_s0_14) + (721539676493/200000000000 : ℝ)*(sp_s0_15) + (1690406313993/1000000000000 : ℝ)*(sp_s0_19) + (845204556757/500000000000 : ℝ)*(f.failure) + (3607703945683/1000000000000 : ℝ)*(f.sum) + (500861159/1250000000000000000000 : ℝ)*base63 + (705814583660477/1250000000000000000000000000 : ℝ)*base65 + (955936302839523/1250000000000000000000000000 : ℝ)*base66 + (14875995849811583/10000000000000000000000000000 : ℝ)*base69 + (2657968782095399/10000000000000000000000000000 : ℝ)*base71 + (1390470466964523/1250000000000000000000000000 : ℝ)*base72 + (4351281280188417/10000000000000000000000000000 : ℝ)*base75 + (6742053212811583/10000000000000000000000000000 : ℝ)*base77 + (468522356214523/625000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (3773/50000000000000000 : ℝ)*base86 + (3773/50000000000000000 : ℝ)*base88 + (3773/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8797/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8797/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4623140388597025692273/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (186347/62500000000 : ℝ)*(base11) + (516633081779/500000000000 : ℝ)*(base39) + (342895960879/500000000000 : ℝ)*(base49) + (378729805353/500000000000 : ℝ)*(base50) + (3064381938043/1000000000000 : ℝ)*(major_s0_0) + (3064381938043/1000000000000 : ℝ)*(major_s0_1) + (3064381938043/1000000000000 : ℝ)*(major_s0_2) + (38576741/1000000000000 : ℝ)*(sp_s0_2) + (25488877/1000000000000 : ℝ)*(sp_s0_9) + (728073/500000000000 : ℝ)*(sp_s0_12) + (4173323304301/1000000000000 : ℝ)*(sp_s0_20) + (4173326285853/1000000000000 : ℝ)*(sp_s0_21) + (834652444047/200000000000 : ℝ)*(sp_s0_22) + (195543366841/100000000000 : ℝ)*(sp_s0_25) + (488858781139/250000000000 : ℝ)*(f.failure) + (4173326285853/1000000000000 : ℝ)*(f.sum) + (16357673/40000000000000000000 : ℝ)*base62 + (308801936001591/1250000000000000000000000000 : ℝ)*base64 + (42753387751591/1250000000000000000000000000 : ℝ)*base66 + (1518003299139389/10000000000000000000000000000 : ℝ)*base68 + (188480422847883/10000000000000000000000000000 : ℝ)*base71 + (394081077248409/1250000000000000000000000000 : ℝ)*base73 + (4398935001860611/10000000000000000000000000000 : ℝ)*base74 + (664019018139389/10000000000000000000000000000 : ℝ)*base76 + (130929291435909/625000000000000000000000000 : ℝ)*base79 + (1171/25000000000000000 : ℝ)*base86 + (1171/25000000000000000 : ℝ)*base88 + (1171/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (40639/100000 : ℝ) ^ (17/4 : ℝ) ≤ (2177748906033701409/100000000000000000000 : ℝ) := by
    have hpowers : (40639/100000 : ℝ)^17 ≤ (2177748906033701409/100000000000000000000 : ℝ)^4 := by
      have hnat : (40639 : ℕ)^17*100000000000000000000^4 ≤ 2177748906033701409^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40639 100000 2177748906033701409 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40639/100000 : ℝ)) (X := (2177748906033701409/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (102177748906033701409/100000000000000000000 : ℝ) ≤ (314088120828591/312500000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (102177748906033701409/100000000000000000000 : ℝ)^4 ≤ (314088120828591/312500000000000 : ℝ)^17 := by
      have hnat : (102177748906033701409 : ℕ)^4*312500000000000^17 ≤ 314088120828591^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102177748906033701409 100000000000000000000 314088120828591 312500000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (314088120828591/312500000000000 : ℝ)) (X := (102177748906033701409/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (52177748906033701409/50000000000000000000 : ℝ) ≤ (1262602259597699/1250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (52177748906033701409/50000000000000000000 : ℝ)^4 ≤ (1262602259597699/1250000000000000 : ℝ)^17 := by
      have hnat : (52177748906033701409 : ℕ)^4*1250000000000000^17 ≤ 1262602259597699^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52177748906033701409 50000000000000000000 1262602259597699 1250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1262602259597699/1250000000000000 : ℝ)) (X := (52177748906033701409/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1588120828591/126996875000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1249955256667/101597500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (40639/100000 : ℝ)) (alpha := (1588120828591/126996875000000 : ℝ)) (beta := (1249955256667/101597500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (40639/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1588120828591/126996875000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1249955256667/101597500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (1537/12500 : ℝ) ^ (17/4 : ℝ) ≤ (13536188126817651/100000000000000000000 : ℝ) := by
    have hpowers : (1537/12500 : ℝ)^17 ≤ (13536188126817651/100000000000000000000 : ℝ)^4 := by
      have hnat : (1537 : ℕ)^17*100000000000000000000^4 ≤ 13536188126817651^4*12500^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1537 12500 13536188126817651 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1537/12500 : ℝ)) (X := (13536188126817651/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100013536188126817651/100000000000000000000 : ℝ) ≤ (5000159241030629/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (100013536188126817651/100000000000000000000 : ℝ)^4 ≤ (5000159241030629/5000000000000000 : ℝ)^17 := by
      have hnat : (100013536188126817651 : ℕ)^4*5000000000000000^17 ≤ 5000159241030629^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100013536188126817651 100000000000000000000 5000159241030629 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000159241030629/5000000000000000 : ℝ)) (X := (100013536188126817651/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50013536188126817651/50000000000000000000 : ℝ) ≤ (250015923279049/250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (50013536188126817651/50000000000000000000 : ℝ)^4 ≤ (250015923279049/250000000000000 : ℝ)^17 := by
      have hnat : (50013536188126817651 : ℕ)^4*250000000000000^17 ≤ 250015923279049^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013536188126817651 50000000000000000000 250015923279049 250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250015923279049/250000000000000 : ℝ)) (X := (50013536188126817651/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(159241030629/614800000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(159224550351/614800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1537/12500 : ℝ)) (alpha := (159241030629/614800000000000 : ℝ)) (beta := (159224550351/614800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1537/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(159241030629/614800000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(159224550351/614800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (8797/25000 : ℝ) ^ (17/4 : ℝ) ≤ (1180801725249190281/100000000000000000000 : ℝ) := by
    have hpowers : (8797/25000 : ℝ)^17 ≤ (1180801725249190281/100000000000000000000 : ℝ)^4 := by
      have hnat : (8797 : ℕ)^17*100000000000000000000^4 ≤ 1180801725249190281^4*25000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8797 25000 1180801725249190281 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8797/25000 : ℝ)) (X := (1180801725249190281/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (101180801725249190281/100000000000000000000 : ℝ) ≤ (10027658996138297/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (101180801725249190281/100000000000000000000 : ℝ)^4 ≤ (10027658996138297/10000000000000000 : ℝ)^17 := by
      have hnat : (101180801725249190281 : ℕ)^4*10000000000000000^17 ≤ 10027658996138297^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101180801725249190281 100000000000000000000 10027658996138297 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027658996138297/10000000000000000 : ℝ)) (X := (101180801725249190281/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (51180801725249190281/50000000000000000000 : ℝ) ≤ (2513768061516101/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (51180801725249190281/50000000000000000000 : ℝ)^4 ≤ (2513768061516101/2500000000000000 : ℝ)^17 := by
      have hnat : (51180801725249190281 : ℕ)^4*2500000000000000^17 ≤ 2513768061516101^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51180801725249190281 50000000000000000000 2513768061516101 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2513768061516101/2500000000000000 : ℝ)) (X := (51180801725249190281/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(27658996138297/3518800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(27413249926107/3518800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (8797/25000 : ℝ)) (alpha := (27658996138297/3518800000000000 : ℝ)) (beta := (27413249926107/3518800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (8797/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(27658996138297/3518800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(27413249926107/3518800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1812191879/5000000000 : ℝ)*X 0 0+(4669426101/10000000000 : ℝ)*X 0 1+(-4537862859/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308030_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1139679279/2000000000 : ℝ)*X 1 0+(-1315376421/5000000000 : ℝ)*X 1 1+(-217793479/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308030_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((439876793/1250000000 : ℝ)*X 2 0+(1223849/2500000 : ℝ)*X 2 1+(2202968223/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308030_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4119786493/10000000000 : ℝ)*X 0 0+(5489664227/10000000000 : ℝ)*X 0 1+(-3149175911/10000000000 : ℝ)*X 0 2+(4119786493/10000000000 : ℝ)*X 1 0+(5489664227/10000000000 : ℝ)*X 1 1+(-3149175911/10000000000 : ℝ)*X 1 2+(4119786493/10000000000 : ℝ)*X 2 0+(5489664227/10000000000 : ℝ)*X 2 1+(-3149175911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308030_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-320133/50000 : ℝ) < ((-156711/100000 : ℝ)*P 0+(-156711/100000 : ℝ)*P 1+(-156711/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-320133/50000 : ℝ) < (-17472040182284083901290651555514613/2747397359855000000000000000000000 : ℝ) := by norm_num
    linear_combination (14347/200000000000 : ℝ)*(base8) + (150011/250000000000 : ℝ)*(base15) + (140393/1000000000000 : ℝ)*(base23) + (309542505399/1000000000000 : ℝ)*(base39) + (698591710033/1000000000000 : ℝ)*(base49) + (204377294087/500000000000 : ℝ)*(base50) + (5064197109/125000000000 : ℝ)*(base60) + (140941/1000000000000 : ℝ)*(ratio_s0_0) + (156711/100000 : ℝ)*(major_s1_0) + (156711/100000 : ℝ)*(major_s1_1) + (156711/100000 : ℝ)*(major_s1_2) + (423965843609/200000000000 : ℝ)*(sp_s1_0) + (264978586217/125000000000 : ℝ)*(sp_s1_1) + (2119829149387/1000000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (105991464489/50000000000 : ℝ)*(f.sum) + (3509397577066579/13520989000000000000000000000 : ℝ)*base63 + (9912730886327/17594000000000000000000000 : ℝ)*base65 + (615899117347/3074000000000000000000000 : ℝ)*base67 + (398458134521/2199250000000000000000000 : ℝ)*base68 + (6642054807295953/111719150937500000000000000000 : ℝ)*base71 + (966030114577/2539937500000000000000000 : ℝ)*base73 + (1375785499283/1921250000000000000000000 : ℝ)*base75 + (55099341757/101597500000000000000000 : ℝ)*base76 + (210071340942922957/312310715000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p008_b019 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 30 ≤ c.val) (hhi : c.val < 32)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=30 ∨ c=31 := by omega
  rcases hc with rfl|rfl
  · exact collision_c308030 p hpa (by linarith only [hpb]) X hX
  · exact collision_c308031 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (c : Fin 88) (hlo : 30 ≤ c.val) (hhi : c.val < 32)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p008_b019 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

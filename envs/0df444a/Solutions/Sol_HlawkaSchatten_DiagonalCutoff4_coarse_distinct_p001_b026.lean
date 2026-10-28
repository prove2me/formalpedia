-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b026
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:30:17.722137+00:00
-- url     : https://prove2.me/submissions/015c9cde-2ce3-4e80-80d9-c459d299c338

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301047
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301048
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301049
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301050
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301051
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301052
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301053
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
theorem collision_support_c301046_s0_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-701140483/5000000000 : ℝ)*x 0 + (-5597041817/10000000000 : ℝ)*x 1 + (-5597041817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (701140483/5000000000 : ℝ)^65 ≤ (1476660159743/20000000000000 : ℝ)^49 := by
    have hnat : (701140483 : ℕ)^65*20000000000000^49 ≤ 1476660159743^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701140483 5000000000 1476660159743 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5597041817/10000000000 : ℝ)^65 ≤ (723567962361/1562500000000 : ℝ)^49 := by
    have hnat : (5597041817 : ℕ)^65*1562500000000^49 ≤ 723567962361^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5597041817 10000000000 723567962361 1562500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5597041817/10000000000 : ℝ)^65 ≤ (723567962361/1562500000000 : ℝ)^49 := by
    have hnat : (5597041817 : ℕ)^65*1562500000000^49 ≤ 723567962361^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5597041817 10000000000 723567962361 1562500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-701140483/5000000000 : ℝ), (-5597041817/10000000000 : ℝ), (-5597041817/10000000000 : ℝ)] ![(1476660159743/20000000000000 : ℝ), (723567962361/1562500000000 : ℝ), (723567962361/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-701140483/5000000000 : ℝ)|^65 ≤ (1476660159743/20000000000000 : ℝ)^49
        have hw : |(-701140483/5000000000 : ℝ)|=(701140483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5597041817/10000000000 : ℝ)|^65 ≤ (723567962361/1562500000000 : ℝ)^49
        have hw : |(-5597041817/10000000000 : ℝ)|=(5597041817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5597041817/10000000000 : ℝ)|^65 ≤ (723567962361/1562500000000 : ℝ)^49
        have hw : |(-5597041817/10000000000 : ℝ)|=(5597041817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s0_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4676712079/10000000000 : ℝ)*x 0 + (2105796149/5000000000 : ℝ)*x 1 + (-2105796149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4676712079/10000000000 : ℝ)^65 ≤ (9122337904703/25000000000000 : ℝ)^49 := by
    have hnat : (4676712079 : ℕ)^65*25000000000000^49 ≤ 9122337904703^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4676712079 10000000000 9122337904703 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105796149/5000000000 : ℝ)^65 ≤ (31755324178029/100000000000000 : ℝ)^49 := by
    have hnat : (2105796149 : ℕ)^65*100000000000000^49 ≤ 31755324178029^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105796149 5000000000 31755324178029 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2105796149/5000000000 : ℝ)^65 ≤ (31755324178029/100000000000000 : ℝ)^49 := by
    have hnat : (2105796149 : ℕ)^65*100000000000000^49 ≤ 31755324178029^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105796149 5000000000 31755324178029 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4676712079/10000000000 : ℝ), (2105796149/5000000000 : ℝ), (-2105796149/5000000000 : ℝ)] ![(9122337904703/25000000000000 : ℝ), (31755324178029/100000000000000 : ℝ), (31755324178029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4676712079/10000000000 : ℝ)|^65 ≤ (9122337904703/25000000000000 : ℝ)^49
        have hw : |(4676712079/10000000000 : ℝ)|=(4676712079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2105796149/5000000000 : ℝ)|^65 ≤ (31755324178029/100000000000000 : ℝ)^49
        have hw : |(2105796149/5000000000 : ℝ)|=(2105796149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2105796149/5000000000 : ℝ)|^65 ≤ (31755324178029/100000000000000 : ℝ)^49
        have hw : |(-2105796149/5000000000 : ℝ)|=(2105796149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s0_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4676712079/10000000000 : ℝ)*x 0 + (-2105796149/5000000000 : ℝ)*x 1 + (2105796149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4676712079/10000000000 : ℝ)^65 ≤ (9122337904703/25000000000000 : ℝ)^49 := by
    have hnat : (4676712079 : ℕ)^65*25000000000000^49 ≤ 9122337904703^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4676712079 10000000000 9122337904703 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105796149/5000000000 : ℝ)^65 ≤ (31755324178029/100000000000000 : ℝ)^49 := by
    have hnat : (2105796149 : ℕ)^65*100000000000000^49 ≤ 31755324178029^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105796149 5000000000 31755324178029 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2105796149/5000000000 : ℝ)^65 ≤ (31755324178029/100000000000000 : ℝ)^49 := by
    have hnat : (2105796149 : ℕ)^65*100000000000000^49 ≤ 31755324178029^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105796149 5000000000 31755324178029 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4676712079/10000000000 : ℝ), (-2105796149/5000000000 : ℝ), (2105796149/5000000000 : ℝ)] ![(9122337904703/25000000000000 : ℝ), (31755324178029/100000000000000 : ℝ), (31755324178029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4676712079/10000000000 : ℝ)|^65 ≤ (9122337904703/25000000000000 : ℝ)^49
        have hw : |(4676712079/10000000000 : ℝ)|=(4676712079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2105796149/5000000000 : ℝ)|^65 ≤ (31755324178029/100000000000000 : ℝ)^49
        have hw : |(-2105796149/5000000000 : ℝ)|=(2105796149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2105796149/5000000000 : ℝ)|^65 ≤ (31755324178029/100000000000000 : ℝ)^49
        have hw : |(2105796149/5000000000 : ℝ)|=(2105796149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s0_3 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1 : ℝ)*x 0 + (0 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1 : ℝ)^65 ≤ (1 : ℝ)^49 := by
    have hnat : (1 : ℕ)^65*1^49 ≤ 1^49*1^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^65 ≤ (0 : ℝ)^49 := by
    have hnat : (0 : ℕ)^65*1^49 ≤ 0^49*1^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^65 ≤ (0 : ℝ)^49 := by
    have hnat : (0 : ℕ)^65*1^49 ≤ 0^49*1^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] ![(1 : ℝ), (0 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1 : ℝ)|^65 ≤ (1 : ℝ)^49
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^65 ≤ (0 : ℝ)^49
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^65 ≤ (0 : ℝ)^49
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s0_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1345101779/10000000000 : ℝ)*x 0 + (-1189782273/2000000000 : ℝ)*x 1 + (-5274682013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345101779/10000000000 : ℝ)^65 ≤ (1746654634331/25000000000000 : ℝ)^49 := by
    have hnat : (1345101779 : ℕ)^65*25000000000000^49 ≤ 1746654634331^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345101779 10000000000 1746654634331 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1189782273/2000000000 : ℝ)^65 ≤ (12552332798843/25000000000000 : ℝ)^49 := by
    have hnat : (1189782273 : ℕ)^65*25000000000000^49 ≤ 12552332798843^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1189782273 2000000000 12552332798843 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274682013/10000000000 : ℝ)^65 ≤ (21402025129431/50000000000000 : ℝ)^49 := by
    have hnat : (5274682013 : ℕ)^65*50000000000000^49 ≤ 21402025129431^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274682013 10000000000 21402025129431 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1345101779/10000000000 : ℝ), (-1189782273/2000000000 : ℝ), (-5274682013/10000000000 : ℝ)] ![(1746654634331/25000000000000 : ℝ), (12552332798843/25000000000000 : ℝ), (21402025129431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1345101779/10000000000 : ℝ)|^65 ≤ (1746654634331/25000000000000 : ℝ)^49
        have hw : |(-1345101779/10000000000 : ℝ)|=(1345101779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1189782273/2000000000 : ℝ)|^65 ≤ (12552332798843/25000000000000 : ℝ)^49
        have hw : |(-1189782273/2000000000 : ℝ)|=(1189782273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5274682013/10000000000 : ℝ)|^65 ≤ (21402025129431/50000000000000 : ℝ)^49
        have hw : |(-5274682013/10000000000 : ℝ)|=(5274682013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s0_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4554494913/10000000000 : ℝ)*x 0 + (251480931/500000000 : ℝ)*x 1 + (-1736261807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4554494913/10000000000 : ℝ)^65 ≤ (7045965191697/20000000000000 : ℝ)^49 := by
    have hnat : (4554494913 : ℕ)^65*20000000000000^49 ≤ 7045965191697^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4554494913 10000000000 7045965191697 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (251480931/500000000 : ℝ)^65 ≤ (2009310798687/5000000000000 : ℝ)^49 := by
    have hnat : (251480931 : ℕ)^65*5000000000000^49 ≤ 2009310798687^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251480931 500000000 2009310798687 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1736261807/5000000000 : ℝ)^65 ≤ (983358321997/4000000000000 : ℝ)^49 := by
    have hnat : (1736261807 : ℕ)^65*4000000000000^49 ≤ 983358321997^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1736261807 5000000000 983358321997 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4554494913/10000000000 : ℝ), (251480931/500000000 : ℝ), (-1736261807/5000000000 : ℝ)] ![(7045965191697/20000000000000 : ℝ), (2009310798687/5000000000000 : ℝ), (983358321997/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4554494913/10000000000 : ℝ)|^65 ≤ (7045965191697/20000000000000 : ℝ)^49
        have hw : |(4554494913/10000000000 : ℝ)|=(4554494913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(251480931/500000000 : ℝ)|^65 ≤ (2009310798687/5000000000000 : ℝ)^49
        have hw : |(251480931/500000000 : ℝ)|=(251480931/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1736261807/5000000000 : ℝ)|^65 ≤ (983358321997/4000000000000 : ℝ)^49
        have hw : |(-1736261807/5000000000 : ℝ)|=(1736261807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s0_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (284655927/625000000 : ℝ)*x 0 + (-173626189/500000000 : ℝ)*x 1 + (628702319/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (284655927/625000000 : ℝ)^65 ≤ (8807456281837/25000000000000 : ℝ)^49 := by
    have hnat : (284655927 : ℕ)^65*25000000000000^49 ≤ 8807456281837^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284655927 625000000 8807456281837 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173626189/500000000 : ℝ)^65 ≤ (12291979804437/50000000000000 : ℝ)^49 := by
    have hnat : (173626189 : ℕ)^65*50000000000000^49 ≤ 12291979804437^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173626189 500000000 12291979804437 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (628702319/1250000000 : ℝ)^65 ≤ (40186215253017/100000000000000 : ℝ)^49 := by
    have hnat : (628702319 : ℕ)^65*100000000000000^49 ≤ 40186215253017^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628702319 1250000000 40186215253017 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(284655927/625000000 : ℝ), (-173626189/500000000 : ℝ), (628702319/1250000000 : ℝ)] ![(8807456281837/25000000000000 : ℝ), (12291979804437/50000000000000 : ℝ), (40186215253017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(284655927/625000000 : ℝ)|^65 ≤ (8807456281837/25000000000000 : ℝ)^49
        have hw : |(284655927/625000000 : ℝ)|=(284655927/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-173626189/500000000 : ℝ)|^65 ≤ (12291979804437/50000000000000 : ℝ)^49
        have hw : |(-173626189/500000000 : ℝ)|=(173626189/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(628702319/1250000000 : ℝ)|^65 ≤ (40186215253017/100000000000000 : ℝ)^49
        have hw : |(628702319/1250000000 : ℝ)|=(628702319/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s0_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8184780839/10000000000 : ℝ)*x 0 + (-641350267/5000000000 : ℝ)*x 1 + (-325395651/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8184780839/10000000000 : ℝ)^65 ≤ (15333143176443/20000000000000 : ℝ)^49 := by
    have hnat : (8184780839 : ℕ)^65*20000000000000^49 ≤ 15333143176443^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8184780839 10000000000 15333143176443 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641350267/5000000000 : ℝ)^65 ≤ (6559955234191/100000000000000 : ℝ)^49 := by
    have hnat : (641350267 : ℕ)^65*100000000000000^49 ≤ 6559955234191^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641350267 5000000000 6559955234191 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325395651/1250000000 : ℝ)^65 ≤ (16774328879413/100000000000000 : ℝ)^49 := by
    have hnat : (325395651 : ℕ)^65*100000000000000^49 ≤ 16774328879413^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325395651 1250000000 16774328879413 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8184780839/10000000000 : ℝ), (-641350267/5000000000 : ℝ), (-325395651/1250000000 : ℝ)] ![(15333143176443/20000000000000 : ℝ), (6559955234191/100000000000000 : ℝ), (16774328879413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8184780839/10000000000 : ℝ)|^65 ≤ (15333143176443/20000000000000 : ℝ)^49
        have hw : |(8184780839/10000000000 : ℝ)|=(8184780839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-641350267/5000000000 : ℝ)|^65 ≤ (6559955234191/100000000000000 : ℝ)^49
        have hw : |(-641350267/5000000000 : ℝ)|=(641350267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-325395651/1250000000 : ℝ)|^65 ≤ (16774328879413/100000000000000 : ℝ)^49
        have hw : |(-325395651/1250000000 : ℝ)|=(325395651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s0_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-23659823/500000000 : ℝ)*x 0 + (-1104715381/2000000000 : ℝ)*x 1 + (-1543586303/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (23659823/500000000 : ℝ)^65 ≤ (1747438792033/100000000000000 : ℝ)^49 := by
    have hnat : (23659823 : ℕ)^65*100000000000000^49 ≤ 1747438792033^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23659823 500000000 1747438792033 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104715381/2000000000 : ℝ)^65 ≤ (9100756023651/20000000000000 : ℝ)^49 := by
    have hnat : (1104715381 : ℕ)^65*20000000000000^49 ≤ 9100756023651^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104715381 2000000000 9100756023651 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1543586303/2500000000 : ℝ)^65 ≤ (26374390537869/50000000000000 : ℝ)^49 := by
    have hnat : (1543586303 : ℕ)^65*50000000000000^49 ≤ 26374390537869^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1543586303 2500000000 26374390537869 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-23659823/500000000 : ℝ), (-1104715381/2000000000 : ℝ), (-1543586303/2500000000 : ℝ)] ![(1747438792033/100000000000000 : ℝ), (9100756023651/20000000000000 : ℝ), (26374390537869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-23659823/500000000 : ℝ)|^65 ≤ (1747438792033/100000000000000 : ℝ)^49
        have hw : |(-23659823/500000000 : ℝ)|=(23659823/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1104715381/2000000000 : ℝ)|^65 ≤ (9100756023651/20000000000000 : ℝ)^49
        have hw : |(-1104715381/2000000000 : ℝ)|=(1104715381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1543586303/2500000000 : ℝ)|^65 ≤ (26374390537869/50000000000000 : ℝ)^49
        have hw : |(-1543586303/2500000000 : ℝ)|=(1543586303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s0_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (206757257/500000000 : ℝ)*x 0 + (4290895723/10000000000 : ℝ)*x 1 + (-2336748527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206757257/500000000 : ℝ)^65 ≤ (15496486922549/50000000000000 : ℝ)^49 := by
    have hnat : (206757257 : ℕ)^65*50000000000000^49 ≤ 15496486922549^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206757257 500000000 15496486922549 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4290895723/10000000000 : ℝ)^65 ≤ (32550946481273/100000000000000 : ℝ)^49 := by
    have hnat : (4290895723 : ℕ)^65*100000000000000^49 ≤ 32550946481273^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4290895723 10000000000 32550946481273 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2336748527/5000000000 : ℝ)^65 ≤ (455700995731/1250000000000 : ℝ)^49 := by
    have hnat : (2336748527 : ℕ)^65*1250000000000^49 ≤ 455700995731^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2336748527 5000000000 455700995731 1250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(206757257/500000000 : ℝ), (4290895723/10000000000 : ℝ), (-2336748527/5000000000 : ℝ)] ![(15496486922549/50000000000000 : ℝ), (32550946481273/100000000000000 : ℝ), (455700995731/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(206757257/500000000 : ℝ)|^65 ≤ (15496486922549/50000000000000 : ℝ)^49
        have hw : |(206757257/500000000 : ℝ)|=(206757257/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4290895723/10000000000 : ℝ)|^65 ≤ (32550946481273/100000000000000 : ℝ)^49
        have hw : |(4290895723/10000000000 : ℝ)|=(4290895723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2336748527/5000000000 : ℝ)|^65 ≤ (455700995731/1250000000000 : ℝ)^49
        have hw : |(-2336748527/5000000000 : ℝ)|=(2336748527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s0_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2831389869/5000000000 : ℝ)*x 0 + (-140608343/400000000 : ℝ)*x 1 + (3828645109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2831389869/5000000000 : ℝ)^65 ≤ (47031225589669/100000000000000 : ℝ)^49 := by
    have hnat : (2831389869 : ℕ)^65*100000000000000^49 ≤ 47031225589669^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2831389869 5000000000 47031225589669 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140608343/400000000 : ℝ)^65 ≤ (24985625911217/100000000000000 : ℝ)^49 := by
    have hnat : (140608343 : ℕ)^65*100000000000000^49 ≤ 24985625911217^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140608343 400000000 24985625911217 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3828645109/10000000000 : ℝ)^65 ≤ (1748946780487/6250000000000 : ℝ)^49 := by
    have hnat : (3828645109 : ℕ)^65*6250000000000^49 ≤ 1748946780487^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3828645109 10000000000 1748946780487 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2831389869/5000000000 : ℝ), (-140608343/400000000 : ℝ), (3828645109/10000000000 : ℝ)] ![(47031225589669/100000000000000 : ℝ), (24985625911217/100000000000000 : ℝ), (1748946780487/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2831389869/5000000000 : ℝ)|^65 ≤ (47031225589669/100000000000000 : ℝ)^49
        have hw : |(2831389869/5000000000 : ℝ)|=(2831389869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-140608343/400000000 : ℝ)|^65 ≤ (24985625911217/100000000000000 : ℝ)^49
        have hw : |(-140608343/400000000 : ℝ)|=(140608343/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3828645109/10000000000 : ℝ)|^65 ≤ (1748946780487/6250000000000 : ℝ)^49
        have hw : |(3828645109/10000000000 : ℝ)|=(3828645109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s0_19 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9469013913/10000000000 : ℝ)*x 0 + (-752532441/10000000000 : ℝ)*x 1 + (-420596577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9469013913/10000000000 : ℝ)^65 ≤ (46509057217383/50000000000000 : ℝ)^49 := by
    have hnat : (9469013913 : ℕ)^65*50000000000000^49 ≤ 46509057217383^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9469013913 10000000000 46509057217383 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (752532441/10000000000 : ℝ)^65 ≤ (404190716309/12500000000000 : ℝ)^49 := by
    have hnat : (752532441 : ℕ)^65*12500000000000^49 ≤ 404190716309^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752532441 10000000000 404190716309 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420596577/5000000000 : ℝ)^65 ≤ (1874179910071/50000000000000 : ℝ)^49 := by
    have hnat : (420596577 : ℕ)^65*50000000000000^49 ≤ 1874179910071^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420596577 5000000000 1874179910071 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9469013913/10000000000 : ℝ), (-752532441/10000000000 : ℝ), (-420596577/5000000000 : ℝ)] ![(46509057217383/50000000000000 : ℝ), (404190716309/12500000000000 : ℝ), (1874179910071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9469013913/10000000000 : ℝ)|^65 ≤ (46509057217383/50000000000000 : ℝ)^49
        have hw : |(9469013913/10000000000 : ℝ)|=(9469013913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-752532441/10000000000 : ℝ)|^65 ≤ (404190716309/12500000000000 : ℝ)^49
        have hw : |(-752532441/10000000000 : ℝ)|=(752532441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-420596577/5000000000 : ℝ)|^65 ≤ (1874179910071/50000000000000 : ℝ)^49
        have hw : |(-420596577/5000000000 : ℝ)|=(420596577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s0_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-473197081/10000000000 : ℝ)*x 0 + (-617434451/1000000000 : ℝ)*x 1 + (-2761788677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (473197081/10000000000 : ℝ)^65 ≤ (218430229263/12500000000000 : ℝ)^49 := by
    have hnat : (473197081 : ℕ)^65*12500000000000^49 ≤ 218430229263^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473197081 10000000000 218430229263 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (617434451/1000000000 : ℝ)^65 ≤ (13187193280021/25000000000000 : ℝ)^49 := by
    have hnat : (617434451 : ℕ)^65*25000000000000^49 ≤ 13187193280021^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617434451 1000000000 13187193280021 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2761788677/5000000000 : ℝ)^65 ≤ (45503785024969/100000000000000 : ℝ)^49 := by
    have hnat : (2761788677 : ℕ)^65*100000000000000^49 ≤ 45503785024969^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2761788677 5000000000 45503785024969 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-473197081/10000000000 : ℝ), (-617434451/1000000000 : ℝ), (-2761788677/5000000000 : ℝ)] ![(218430229263/12500000000000 : ℝ), (13187193280021/25000000000000 : ℝ), (45503785024969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-473197081/10000000000 : ℝ)|^65 ≤ (218430229263/12500000000000 : ℝ)^49
        have hw : |(-473197081/10000000000 : ℝ)|=(473197081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-617434451/1000000000 : ℝ)|^65 ≤ (13187193280021/25000000000000 : ℝ)^49
        have hw : |(-617434451/1000000000 : ℝ)|=(617434451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2761788677/5000000000 : ℝ)|^65 ≤ (45503785024969/100000000000000 : ℝ)^49
        have hw : |(-2761788677/5000000000 : ℝ)|=(2761788677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s0_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (707847497/1250000000 : ℝ)*x 0 + (478580537/1250000000 : ℝ)*x 1 + (-3515209133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (707847497/1250000000 : ℝ)^65 ≤ (47031228211779/100000000000000 : ℝ)^49 := by
    have hnat : (707847497 : ℕ)^65*100000000000000^49 ≤ 47031228211779^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707847497 1250000000 47031228211779 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (478580537/1250000000 : ℝ)^65 ≤ (13991570302689/50000000000000 : ℝ)^49 := by
    have hnat : (478580537 : ℕ)^65*50000000000000^49 ≤ 13991570302689^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478580537 1250000000 13991570302689 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3515209133/10000000000 : ℝ)^65 ≤ (24985631172487/100000000000000 : ℝ)^49 := by
    have hnat : (3515209133 : ℕ)^65*100000000000000^49 ≤ 24985631172487^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3515209133 10000000000 24985631172487 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(707847497/1250000000 : ℝ), (478580537/1250000000 : ℝ), (-3515209133/10000000000 : ℝ)] ![(47031228211779/100000000000000 : ℝ), (13991570302689/50000000000000 : ℝ), (24985631172487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(707847497/1250000000 : ℝ)|^65 ≤ (47031228211779/100000000000000 : ℝ)^49
        have hw : |(707847497/1250000000 : ℝ)|=(707847497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(478580537/1250000000 : ℝ)|^65 ≤ (13991570302689/50000000000000 : ℝ)^49
        have hw : |(478580537/1250000000 : ℝ)|=(478580537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3515209133/10000000000 : ℝ)|^65 ≤ (24985631172487/100000000000000 : ℝ)^49
        have hw : |(-3515209133/10000000000 : ℝ)|=(3515209133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s0_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4135143373/10000000000 : ℝ)*x 0 + (-2336748567/5000000000 : ℝ)*x 1 + (4290897387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4135143373/10000000000 : ℝ)^65 ≤ (30992956276937/100000000000000 : ℝ)^49 := by
    have hnat : (4135143373 : ℕ)^65*100000000000000^49 ≤ 30992956276937^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135143373 10000000000 30992956276937 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2336748567/5000000000 : ℝ)^65 ≤ (18228040243149/50000000000000 : ℝ)^49 := by
    have hnat : (2336748567 : ℕ)^65*50000000000000^49 ≤ 18228040243149^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2336748567 5000000000 18228040243149 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4290897387/10000000000 : ℝ)^65 ≤ (8137740806579/25000000000000 : ℝ)^49 := by
    have hnat : (4290897387 : ℕ)^65*25000000000000^49 ≤ 8137740806579^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4290897387 10000000000 8137740806579 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4135143373/10000000000 : ℝ), (-2336748567/5000000000 : ℝ), (4290897387/10000000000 : ℝ)] ![(30992956276937/100000000000000 : ℝ), (18228040243149/50000000000000 : ℝ), (8137740806579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4135143373/10000000000 : ℝ)|^65 ≤ (30992956276937/100000000000000 : ℝ)^49
        have hw : |(4135143373/10000000000 : ℝ)|=(4135143373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2336748567/5000000000 : ℝ)|^65 ≤ (18228040243149/50000000000000 : ℝ)^49
        have hw : |(-2336748567/5000000000 : ℝ)|=(2336748567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4290897387/10000000000 : ℝ)|^65 ≤ (8137740806579/25000000000000 : ℝ)^49
        have hw : |(4290897387/10000000000 : ℝ)|=(4290897387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s0_25 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (9469014111/10000000000 : ℝ)*x 0 + (-841192843/10000000000 : ℝ)*x 1 + (-75253231/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9469014111/10000000000 : ℝ)^65 ≤ (93018117014917/100000000000000 : ℝ)^49 := by
    have hnat : (9469014111 : ℕ)^65*100000000000000^49 ≤ 93018117014917^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9469014111 10000000000 93018117014917 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (841192843/10000000000 : ℝ)^65 ≤ (3748357981813/100000000000000 : ℝ)^49 := by
    have hnat : (841192843 : ℕ)^65*100000000000000^49 ≤ 3748357981813^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841192843 10000000000 3748357981813 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75253231/1000000000 : ℝ)^65 ≤ (3233524983783/100000000000000 : ℝ)^49 := by
    have hnat : (75253231 : ℕ)^65*100000000000000^49 ≤ 3233524983783^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75253231 1000000000 3233524983783 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9469014111/10000000000 : ℝ), (-841192843/10000000000 : ℝ), (-75253231/1000000000 : ℝ)] ![(93018117014917/100000000000000 : ℝ), (3748357981813/100000000000000 : ℝ), (3233524983783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9469014111/10000000000 : ℝ)|^65 ≤ (93018117014917/100000000000000 : ℝ)^49
        have hw : |(9469014111/10000000000 : ℝ)|=(9469014111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-841192843/10000000000 : ℝ)|^65 ≤ (3748357981813/100000000000000 : ℝ)^49
        have hw : |(-841192843/10000000000 : ℝ)|=(841192843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-75253231/1000000000 : ℝ)|^65 ≤ (3233524983783/100000000000000 : ℝ)^49
        have hw : |(-75253231/1000000000 : ℝ)|=(75253231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s1_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2862763121/10000000000 : ℝ)*x 0 + (-5057844097/10000000000 : ℝ)*x 1 + (-5057844097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2862763121/10000000000 : ℝ)^65 ≤ (4757176130847/25000000000000 : ℝ)^49 := by
    have hnat : (2862763121 : ℕ)^65*25000000000000^49 ≤ 4757176130847^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2862763121 10000000000 4757176130847 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5057844097/10000000000 : ℝ)^65 ≤ (40485647727049/100000000000000 : ℝ)^49 := by
    have hnat : (5057844097 : ℕ)^65*100000000000000^49 ≤ 40485647727049^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5057844097 10000000000 40485647727049 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5057844097/10000000000 : ℝ)^65 ≤ (40485647727049/100000000000000 : ℝ)^49 := by
    have hnat : (5057844097 : ℕ)^65*100000000000000^49 ≤ 40485647727049^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5057844097 10000000000 40485647727049 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2862763121/10000000000 : ℝ), (-5057844097/10000000000 : ℝ), (-5057844097/10000000000 : ℝ)] ![(4757176130847/25000000000000 : ℝ), (40485647727049/100000000000000 : ℝ), (40485647727049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2862763121/10000000000 : ℝ)|^65 ≤ (4757176130847/25000000000000 : ℝ)^49
        have hw : |(-2862763121/10000000000 : ℝ)|=(2862763121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5057844097/10000000000 : ℝ)|^65 ≤ (40485647727049/100000000000000 : ℝ)^49
        have hw : |(-5057844097/10000000000 : ℝ)|=(5057844097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5057844097/10000000000 : ℝ)|^65 ≤ (40485647727049/100000000000000 : ℝ)^49
        have hw : |(-5057844097/10000000000 : ℝ)|=(5057844097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s1_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4606663493/10000000000 : ℝ)*x 0 + (212384799/500000000 : ℝ)*x 1 + (-212384799/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4606663493/10000000000 : ℝ)^65 ≤ (17883061811497/50000000000000 : ℝ)^49 := by
    have hnat : (4606663493 : ℕ)^65*50000000000000^49 ≤ 17883061811497^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4606663493 10000000000 17883061811497 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212384799/500000000 : ℝ)^65 ≤ (16058469091781/50000000000000 : ℝ)^49 := by
    have hnat : (212384799 : ℕ)^65*50000000000000^49 ≤ 16058469091781^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212384799 500000000 16058469091781 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212384799/500000000 : ℝ)^65 ≤ (16058469091781/50000000000000 : ℝ)^49 := by
    have hnat : (212384799 : ℕ)^65*50000000000000^49 ≤ 16058469091781^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212384799 500000000 16058469091781 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4606663493/10000000000 : ℝ), (212384799/500000000 : ℝ), (-212384799/500000000 : ℝ)] ![(17883061811497/50000000000000 : ℝ), (16058469091781/50000000000000 : ℝ), (16058469091781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4606663493/10000000000 : ℝ)|^65 ≤ (17883061811497/50000000000000 : ℝ)^49
        have hw : |(4606663493/10000000000 : ℝ)|=(4606663493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(212384799/500000000 : ℝ)|^65 ≤ (16058469091781/50000000000000 : ℝ)^49
        have hw : |(212384799/500000000 : ℝ)|=(212384799/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212384799/500000000 : ℝ)|^65 ≤ (16058469091781/50000000000000 : ℝ)^49
        have hw : |(-212384799/500000000 : ℝ)|=(212384799/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s1_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4606663493/10000000000 : ℝ)*x 0 + (-212384799/500000000 : ℝ)*x 1 + (212384799/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4606663493/10000000000 : ℝ)^65 ≤ (17883061811497/50000000000000 : ℝ)^49 := by
    have hnat : (4606663493 : ℕ)^65*50000000000000^49 ≤ 17883061811497^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4606663493 10000000000 17883061811497 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212384799/500000000 : ℝ)^65 ≤ (16058469091781/50000000000000 : ℝ)^49 := by
    have hnat : (212384799 : ℕ)^65*50000000000000^49 ≤ 16058469091781^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212384799 500000000 16058469091781 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212384799/500000000 : ℝ)^65 ≤ (16058469091781/50000000000000 : ℝ)^49 := by
    have hnat : (212384799 : ℕ)^65*50000000000000^49 ≤ 16058469091781^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212384799 500000000 16058469091781 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4606663493/10000000000 : ℝ), (-212384799/500000000 : ℝ), (212384799/500000000 : ℝ)] ![(17883061811497/50000000000000 : ℝ), (16058469091781/50000000000000 : ℝ), (16058469091781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4606663493/10000000000 : ℝ)|^65 ≤ (17883061811497/50000000000000 : ℝ)^49
        have hw : |(4606663493/10000000000 : ℝ)|=(4606663493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212384799/500000000 : ℝ)|^65 ≤ (16058469091781/50000000000000 : ℝ)^49
        have hw : |(-212384799/500000000 : ℝ)|=(212384799/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(212384799/500000000 : ℝ)|^65 ≤ (16058469091781/50000000000000 : ℝ)^49
        have hw : |(212384799/500000000 : ℝ)|=(212384799/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301046_s1_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6208507809/10000000000 : ℝ)*x 0 + (-1674561837/5000000000 : ℝ)*x 1 + (-1674561837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6208507809/10000000000 : ℝ)^65 ≤ (10627257932493/20000000000000 : ℝ)^49 := by
    have hnat : (6208507809 : ℕ)^65*20000000000000^49 ≤ 10627257932493^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6208507809 10000000000 10627257932493 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1674561837/5000000000 : ℝ)^65 ≤ (23431855160477/100000000000000 : ℝ)^49 := by
    have hnat : (1674561837 : ℕ)^65*100000000000000^49 ≤ 23431855160477^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674561837 5000000000 23431855160477 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1674561837/5000000000 : ℝ)^65 ≤ (23431855160477/100000000000000 : ℝ)^49 := by
    have hnat : (1674561837 : ℕ)^65*100000000000000^49 ≤ 23431855160477^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674561837 5000000000 23431855160477 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6208507809/10000000000 : ℝ), (-1674561837/5000000000 : ℝ), (-1674561837/5000000000 : ℝ)] ![(10627257932493/20000000000000 : ℝ), (23431855160477/100000000000000 : ℝ), (23431855160477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6208507809/10000000000 : ℝ)|^65 ≤ (10627257932493/20000000000000 : ℝ)^49
        have hw : |(6208507809/10000000000 : ℝ)|=(6208507809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1674561837/5000000000 : ℝ)|^65 ≤ (23431855160477/100000000000000 : ℝ)^49
        have hw : |(-1674561837/5000000000 : ℝ)|=(1674561837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1674561837/5000000000 : ℝ)|^65 ≤ (23431855160477/100000000000000 : ℝ)^49
        have hw : |(-1674561837/5000000000 : ℝ)|=(1674561837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301046 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (129/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^129 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^129*1^32 ≤ 1^32*1^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11876107154580011/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (11876107154580011/10000000000000000 : ℝ)^129 := by
      have hnat : (2 : ℕ)^32*10000000000000000^129 ≤ 11876107154580011^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11876107154580011 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11876107154580011/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6566374745045327/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (6566374745045327/5000000000000000 : ℝ)^129 := by
      have hnat : (3 : ℕ)^32*5000000000000000^129 ≤ 6566374745045327^129*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6566374745045327 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6566374745045327/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-701140483/5000000000 : ℝ)*X 0 0+(-5597041817/10000000000 : ℝ)*X 0 1+(-5597041817/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((4676712079/10000000000 : ℝ)*X 1 0+(2105796149/5000000000 : ℝ)*X 1 1+(-2105796149/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4676712079/10000000000 : ℝ)*X 2 0+(-2105796149/5000000000 : ℝ)*X 2 1+(2105796149/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_3 : ((1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s0_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1345101779/10000000000 : ℝ)*X 0 0+(-1189782273/2000000000 : ℝ)*X 0 1+(-5274682013/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((4554494913/10000000000 : ℝ)*X 1 0+(251480931/500000000 : ℝ)*X 1 1+(-1736261807/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((284655927/625000000 : ℝ)*X 2 0+(-173626189/500000000 : ℝ)*X 2 1+(628702319/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((8184780839/10000000000 : ℝ)*X 0 0+(-641350267/5000000000 : ℝ)*X 0 1+(-325395651/1250000000 : ℝ)*X 0 2+(8184780839/10000000000 : ℝ)*X 1 0+(-641350267/5000000000 : ℝ)*X 1 1+(-325395651/1250000000 : ℝ)*X 1 2+(8184780839/10000000000 : ℝ)*X 2 0+(-641350267/5000000000 : ℝ)*X 2 1+(-325395651/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-23659823/500000000 : ℝ)*X 0 0+(-1104715381/2000000000 : ℝ)*X 0 1+(-1543586303/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((206757257/500000000 : ℝ)*X 1 0+(4290895723/10000000000 : ℝ)*X 1 1+(-2336748527/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((2831389869/5000000000 : ℝ)*X 2 0+(-140608343/400000000 : ℝ)*X 2 1+(3828645109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((9469013913/10000000000 : ℝ)*X 0 0+(-752532441/10000000000 : ℝ)*X 0 1+(-420596577/5000000000 : ℝ)*X 0 2+(9469013913/10000000000 : ℝ)*X 1 0+(-752532441/10000000000 : ℝ)*X 1 1+(-420596577/5000000000 : ℝ)*X 1 2+(9469013913/10000000000 : ℝ)*X 2 0+(-752532441/10000000000 : ℝ)*X 2 1+(-420596577/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-473197081/10000000000 : ℝ)*X 0 0+(-617434451/1000000000 : ℝ)*X 0 1+(-2761788677/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((707847497/1250000000 : ℝ)*X 1 0+(478580537/1250000000 : ℝ)*X 1 1+(-3515209133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4135143373/10000000000 : ℝ)*X 2 0+(-2336748567/5000000000 : ℝ)*X 2 1+(4290897387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((9469014111/10000000000 : ℝ)*X 0 0+(-841192843/10000000000 : ℝ)*X 0 1+(-75253231/1000000000 : ℝ)*X 0 2+(9469014111/10000000000 : ℝ)*X 1 0+(-841192843/10000000000 : ℝ)*X 1 1+(-75253231/1000000000 : ℝ)*X 1 2+(9469014111/10000000000 : ℝ)*X 2 0+(-841192843/10000000000 : ℝ)*X 2 1+(-75253231/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((1177/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1177/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (73571859939027383423877/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (934089/1000000000000 : ℝ)*(base3) + (224315286183/250000000000 : ℝ)*(base39) + (2818793/1000000000000 : ℝ)*(base49) + (754801/250000000000 : ℝ)*(base59) + (3760566935269/1000000000000 : ℝ)*(major_s0_0) + (3760566935269/1000000000000 : ℝ)*(major_s0_1) + (3760566935269/1000000000000 : ℝ)*(major_s0_2) + (246531/25000000000 : ℝ)*(sp_s0_2) + (995779978369/200000000000 : ℝ)*(sp_s0_7) + (248937557583/50000000000 : ℝ)*(sp_s0_8) + (2489374294801/500000000000 : ℝ)*(sp_s0_9) + (2542228139807/1000000000000 : ℝ)*(sp_s0_13) + (149674273/1000000000000 : ℝ)*(sp_s0_15) + (141441003/1000000000000 : ℝ)*(sp_s0_22) + (317778634237/125000000000 : ℝ)*(f.failure) + (995779978369/200000000000 : ℝ)*(f.sum) + (2468829790692041/5000000000000000000000000000 : ℝ)*base62 + (4794070004567967/10000000000000000000000000000 : ℝ)*base65 + (7146313482567967/10000000000000000000000000000 : ℝ)*base67 + (4691243754692041/10000000000000000000000000000 : ℝ)*base68 + (1280005559437963/5000000000000000000000000000 : ℝ)*base71 + (2350179520432033/10000000000000000000000000000 : ℝ)*base72 + (9796532897692041/10000000000000000000000000000 : ℝ)*base74 + (4450610538307959/10000000000000000000000000000 : ℝ)*base77 + (1728480422932033/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (359/390625000000000 : ℝ)*base87 + (359/390625000000000 : ℝ)*base89 + (359/390625000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11391/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-11391/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (48523015076239091239143/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51719/7812500000 : ℝ)*(base12) + (76755756823/250000000000 : ℝ)*(base39) + (10319376763031/1000000000000 : ℝ)*(major_s0_0) + (2472151592473/500000000000 : ℝ)*(major_s0_1) + (2472151592473/500000000000 : ℝ)*(major_s0_2) + (956477/10000000000 : ℝ)*(sp_s0_0) + (1109713/12500000000 : ℝ)*(sp_s0_1) + (1343768394521/250000000000 : ℝ)*(sp_s0_3) + (28835733/500000000000 : ℝ)*(sp_s0_9) + (27592759/1000000000000 : ℝ)*(sp_s0_13) + (3273019536377/500000000000 : ℝ)*(sp_s0_14) + (3273026281723/500000000000 : ℝ)*(sp_s0_15) + (6546083669021/1000000000000 : ℝ)*(sp_s0_16) + (133697368071/40000000000 : ℝ)*(sp_s0_19) + (1671230897267/500000000000 : ℝ)*(f.failure) + (3273070670243/500000000000 : ℝ)*(f.sum) + (450958690142797/2500000000000000000000000000 : ℝ)*base62 + (896116765690139/5000000000000000000000000000 : ℝ)*base65 + (1118851075190139/5000000000000000000000000000 : ℝ)*base67 + (3334439655857203/5000000000000000000000000000 : ℝ)*base69 + (1226296359753619/10000000000000000000000000000 : ℝ)*base71 + (273529015438933/10000000000000000000000000000 : ℝ)*base73 + (787668850857203/5000000000000000000000000000 : ℝ)*base75 + (6698492112373341/10000000000000000000000000000 : ℝ)*base77 + (5747802329180789/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (6573/12500000000000000 : ℝ)*base86 + (5927/12500000000000000 : ℝ)*base89 + (5927/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-11391/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-11391/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6201138611420623692267/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (86177798597/100000000000 : ℝ)*(base39) + (203779/125000000000 : ℝ)*(base49) + (1103119/200000000000 : ℝ)*(base59) + (6678566473/781250000 : ℝ)*(major_s0_0) + (618037872051/125000000000 : ℝ)*(major_s0_1) + (618037872051/125000000000 : ℝ)*(major_s0_2) + (5504339/125000000000 : ℝ)*(sp_s0_2) + (450532763629/125000000000 : ℝ)*(sp_s0_3) + (134621241/1000000000000 : ℝ)*(sp_s0_7) + (45448561/500000000000 : ℝ)*(sp_s0_8) + (6546006370737/1000000000000 : ℝ)*(sp_s0_20) + (818256261857/125000000000 : ℝ)*(sp_s0_21) + (3273048478633/500000000000 : ℝ)*(sp_s0_22) + (1671230826779/500000000000 : ℝ)*(sp_s0_25) + (1671230826779/500000000000 : ℝ)*(f.failure) + (3273070495989/500000000000 : ℝ)*(f.sum) + (349911096202439/625000000000000000000000000 : ℝ)*base62 + (760466336363793/1250000000000000000000000000 : ℝ)*base65 + (635765559113793/1250000000000000000000000000 : ℝ)*base67 + (1251995537327439/1250000000000000000000000000 : ℝ)*base68 + (78013578618727/1250000000000000000000000000 : ℝ)*base70 + (4999719578389/7812500000000000000000000 : ℝ)*base73 + (1284125615327439/1250000000000000000000000000 : ℝ)*base74 + (6995985539281/15625000000000000000000000 : ℝ)*base77 + (102663456031033/1250000000000000000000000000 : ℝ)*base79 + (14199/12500000000000000 : ℝ)*base87 + (14199/12500000000000000 : ℝ)*base89 + (14199/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (1177/10000 : ℝ) ^ (129/32 : ℝ) ≤ (17950130728530043/100000000000000000000 : ℝ) := by
    have hpowers : (1177/10000 : ℝ)^129 ≤ (17950130728530043/100000000000000000000 : ℝ)^32 := by
      have hnat : (1177 : ℕ)^129*100000000000000000000^32 ≤ 17950130728530043^32*10000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1177 10000 17950130728530043 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1177/10000 : ℝ)) (X := (17950130728530043/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100017950130728530043/100000000000000000000 : ℝ) ≤ (10000445244513647/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (100017950130728530043/100000000000000000000 : ℝ)^32 ≤ (10000445244513647/10000000000000000 : ℝ)^129 := by
      have hnat : (100017950130728530043 : ℕ)^32*10000000000000000^129 ≤ 10000445244513647^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100017950130728530043 100000000000000000000 10000445244513647 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000445244513647/10000000000000000 : ℝ)) (X := (100017950130728530043/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50017950130728530043/50000000000000000000 : ℝ) ≤ (2000178085789153/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (50017950130728530043/50000000000000000000 : ℝ)^32 ≤ (2000178085789153/2000000000000000 : ℝ)^129 := by
      have hnat : (50017950130728530043 : ℕ)^32*2000000000000000^129 ≤ 2000178085789153^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017950130728530043 50000000000000000000 2000178085789153 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000178085789153/2000000000000000 : ℝ)) (X := (50017950130728530043/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(445244513647/1177000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(222592216059/588500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1177/10000 : ℝ)) (alpha := (445244513647/1177000000000000 : ℝ)) (beta := (222592216059/588500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1177/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(445244513647/1177000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(222592216059/588500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (11391/25000 : ℝ) ^ (129/32 : ℝ) ≤ (210275807625525463/5000000000000000000 : ℝ) := by
    have hpowers : (11391/25000 : ℝ)^129 ≤ (210275807625525463/5000000000000000000 : ℝ)^32 := by
      have hnat : (11391 : ℕ)^129*5000000000000000000^32 ≤ 210275807625525463^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11391 25000 210275807625525463 5000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11391/25000 : ℝ)) (X := (210275807625525463/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (5210275807625525463/5000000000000000000 : ℝ) ≤ (10102712760871833/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (5210275807625525463/5000000000000000000 : ℝ)^32 ≤ (10102712760871833/10000000000000000 : ℝ)^129 := by
      have hnat : (5210275807625525463 : ℕ)^32*10000000000000000^129 ≤ 10102712760871833^129*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5210275807625525463 5000000000000000000 10102712760871833 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10102712760871833/10000000000000000 : ℝ)) (X := (5210275807625525463/5000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (2710275807625525463/2500000000000000000 : ℝ) ≤ (5101177112186607/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2710275807625525463/2500000000000000000 : ℝ)^32 ≤ (5101177112186607/5000000000000000 : ℝ)^129 := by
      have hnat : (2710275807625525463 : ℕ)^32*5000000000000000^129 ≤ 5101177112186607^129*2500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2710275807625525463 2500000000000000000 5101177112186607 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5101177112186607/5000000000000000 : ℝ)) (X := (2710275807625525463/2500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(102712760871833/4556400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(33213821167127/1518800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (11391/25000 : ℝ)) (alpha := (102712760871833/4556400000000000 : ℝ)) (beta := (33213821167127/1518800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (11391/25000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(102712760871833/4556400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(33213821167127/1518800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (11391/25000 : ℝ) ^ (129/32 : ℝ) ≤ (210275807625525463/5000000000000000000 : ℝ) := by
    have hpowers : (11391/25000 : ℝ)^129 ≤ (210275807625525463/5000000000000000000 : ℝ)^32 := by
      have hnat : (11391 : ℕ)^129*5000000000000000000^32 ≤ 210275807625525463^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11391 25000 210275807625525463 5000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11391/25000 : ℝ)) (X := (210275807625525463/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (5210275807625525463/5000000000000000000 : ℝ) ≤ (10102712760871833/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (5210275807625525463/5000000000000000000 : ℝ)^32 ≤ (10102712760871833/10000000000000000 : ℝ)^129 := by
      have hnat : (5210275807625525463 : ℕ)^32*10000000000000000^129 ≤ 10102712760871833^129*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5210275807625525463 5000000000000000000 10102712760871833 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10102712760871833/10000000000000000 : ℝ)) (X := (5210275807625525463/5000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (2710275807625525463/2500000000000000000 : ℝ) ≤ (5101177112186607/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (2710275807625525463/2500000000000000000 : ℝ)^32 ≤ (5101177112186607/5000000000000000 : ℝ)^129 := by
      have hnat : (2710275807625525463 : ℕ)^32*5000000000000000^129 ≤ 5101177112186607^129*2500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2710275807625525463 2500000000000000000 5101177112186607 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5101177112186607/5000000000000000 : ℝ)) (X := (2710275807625525463/2500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(102712760871833/4556400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(33213821167127/1518800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (11391/25000 : ℝ)) (alpha := (102712760871833/4556400000000000 : ℝ)) (beta := (33213821167127/1518800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (11391/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(102712760871833/4556400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(33213821167127/1518800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2862763121/10000000000 : ℝ)*X 0 0+(-5057844097/10000000000 : ℝ)*X 0 1+(-5057844097/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4606663493/10000000000 : ℝ)*X 1 0+(212384799/500000000 : ℝ)*X 1 1+(-212384799/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4606663493/10000000000 : ℝ)*X 2 0+(-212384799/500000000 : ℝ)*X 2 1+(212384799/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6208507809/10000000000 : ℝ)*X 0 0+(-1674561837/5000000000 : ℝ)*X 0 1+(-1674561837/5000000000 : ℝ)*X 0 2+(6208507809/10000000000 : ℝ)*X 1 0+(-1674561837/5000000000 : ℝ)*X 1 1+(-1674561837/5000000000 : ℝ)*X 1 2+(6208507809/10000000000 : ℝ)*X 2 0+(-1674561837/5000000000 : ℝ)*X 2 1+(-1674561837/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301046_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-73443/12500 : ℝ) < ((-36981/25000 : ℝ)*P 0+(-36981/25000 : ℝ)*P 1+(-36981/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-73443/12500 : ℝ) < (-16220626006889805545592478989/2793168125000000000000000000 : ℝ) := by norm_num
    linear_combination (85831/500000000000 : ℝ)*(base10) + (85831/500000000000 : ℝ)*(base12) + (304387/1000000000000 : ℝ)*(base27) + (2572163391/4000000000 : ℝ)*(base39) + (8038009653/25000000000 : ℝ)*(base40) + (132906835743/1000000000000 : ℝ)*(base49) + (132906835743/1000000000000 : ℝ)*(base59) + (36981/25000 : ℝ)*(major_s1_0) + (36981/25000 : ℝ)*(major_s1_1) + (36981/25000 : ℝ)*(major_s1_2) + (1935749705959/1000000000000 : ℝ)*(sp_s1_0) + (1935750049283/1000000000000 : ℝ)*(sp_s1_1) + (1935750049283/1000000000000 : ℝ)*(sp_s1_2) + (999999695613/1000000000000 : ℝ)*(sp_s1_6) + (1935750049283/1000000000000 : ℝ)*(f.sum) + (5189604762383/18985000000000000000000000 : ℝ)*base62 + (2375337969111/7594000000000000000000000 : ℝ)*base64 + (2375337969111/7594000000000000000000000 : ℝ)*base66 + (199314036377/9492500000000000000000000 : ℝ)*base69 + (2551504333977141/22345345000000000000000000000 : ℝ)*base70 + (1659585780573/5885000000000000000000000 : ℝ)*base72 + (199314036377/9492500000000000000000000 : ℝ)*base75 + (3004795980573/5885000000000000000000000 : ℝ)*base76 + (2556258795422859/22345345000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p001_b026 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 54)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=46 ∨ c=47 ∨ c=48 ∨ c=49 ∨ c=50 ∨ c=51 ∨ c=52 ∨ c=53 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact collision_c301046 p hpa (by linarith only [hpb]) X hX
  · exact collision_c301047 p hpa (by linarith only [hpb]) X hX
  · exact collision_c301048 p hpa (by linarith only [hpb]) X hX
  · exact collision_c301049 p hpa (by linarith only [hpb]) X hX
  · exact collision_c301050 p hpa (by linarith only [hpb]) X hX
  · exact collision_c301051 p hpa (by linarith only [hpb]) X hX
  · exact collision_c301052 p hpa (by linarith only [hpb]) X hX
  · exact collision_c301053 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 46 ≤ c.val) (hhi : c.val < 54)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b026 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

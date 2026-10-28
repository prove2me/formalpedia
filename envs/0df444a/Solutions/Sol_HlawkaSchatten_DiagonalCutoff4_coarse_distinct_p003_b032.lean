-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b032
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:54:59.041451+00:00
-- url     : https://prove2.me/submissions/621e7529-5865-4ace-b03a-aeb0617a89aa

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10075
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c10076
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
theorem collision_support_c303073_s0_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3928074809/10000000000 : ℝ)*x 0 + (-224280777/500000000 : ℝ)*x 1 + (92556031/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3928074809/10000000000 : ℝ)^33 ≤ (455131921163/1562500000000 : ℝ)^25 := by
    have hnat : (3928074809 : ℕ)^33*1562500000000^25 ≤ 455131921163^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3928074809 10000000000 455131921163 1562500000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224280777/500000000 : ℝ)^33 ≤ (34706043191141/100000000000000 : ℝ)^25 := by
    have hnat : (224280777 : ℕ)^33*100000000000000^25 ≤ 34706043191141^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224280777 500000000 34706043191141 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (92556031/200000000 : ℝ)^33 ≤ (7233102767561/20000000000000 : ℝ)^25 := by
    have hnat : (92556031 : ℕ)^33*20000000000000^25 ≤ 7233102767561^25*200000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92556031 200000000 7233102767561 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3928074809/10000000000 : ℝ), (-224280777/500000000 : ℝ), (92556031/200000000 : ℝ)] ![(455131921163/1562500000000 : ℝ), (34706043191141/100000000000000 : ℝ), (7233102767561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3928074809/10000000000 : ℝ)|^33 ≤ (455131921163/1562500000000 : ℝ)^25
        have hw : |(-3928074809/10000000000 : ℝ)|=(3928074809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-224280777/500000000 : ℝ)|^33 ≤ (34706043191141/100000000000000 : ℝ)^25
        have hw : |(-224280777/500000000 : ℝ)|=(224280777/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(92556031/200000000 : ℝ)|^33 ≤ (7233102767561/20000000000000 : ℝ)^25
        have hw : |(92556031/200000000 : ℝ)|=(92556031/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s0_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2232198407/5000000000 : ℝ)*x 0 + (5098061697/10000000000 : ℝ)*x 1 + (3436596411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2232198407/5000000000 : ℝ)^33 ≤ (34489498713903/100000000000000 : ℝ)^25 := by
    have hnat : (2232198407 : ℕ)^33*100000000000000^25 ≤ 34489498713903^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2232198407 5000000000 34489498713903 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5098061697/10000000000 : ℝ)^33 ≤ (41093649734919/100000000000000 : ℝ)^25 := by
    have hnat : (5098061697 : ℕ)^33*100000000000000^25 ≤ 41093649734919^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5098061697 10000000000 41093649734919 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3436596411/10000000000 : ℝ)^33 ≤ (24416851534973/100000000000000 : ℝ)^25 := by
    have hnat : (3436596411 : ℕ)^33*100000000000000^25 ≤ 24416851534973^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3436596411 10000000000 24416851534973 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2232198407/5000000000 : ℝ), (5098061697/10000000000 : ℝ), (3436596411/10000000000 : ℝ)] ![(34489498713903/100000000000000 : ℝ), (41093649734919/100000000000000 : ℝ), (24416851534973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2232198407/5000000000 : ℝ)|^33 ≤ (34489498713903/100000000000000 : ℝ)^25
        have hw : |(2232198407/5000000000 : ℝ)|=(2232198407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5098061697/10000000000 : ℝ)|^33 ≤ (41093649734919/100000000000000 : ℝ)^25
        have hw : |(5098061697/10000000000 : ℝ)|=(5098061697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3436596411/10000000000 : ℝ)|^33 ≤ (24416851534973/100000000000000 : ℝ)^25
        have hw : |(3436596411/10000000000 : ℝ)|=(3436596411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s0_5 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (0 : ℝ)*x 1 + (1 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^33 ≤ (0 : ℝ)^25 := by
    have hnat : (0 : ℕ)^33*1^25 ≤ 0^25*1^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (0 : ℝ)^33 ≤ (0 : ℝ)^25 := by
    have hnat : (0 : ℕ)^33*1^25 ≤ 0^25*1^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1 : ℝ)^33 ≤ (1 : ℝ)^25 := by
    have hnat : (1 : ℕ)^33*1^25 ≤ 1^25*1^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] ![(0 : ℝ), (0 : ℝ), (1 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^33 ≤ (0 : ℝ)^25
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(0 : ℝ)|^33 ≤ (0 : ℝ)^25
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1 : ℝ)|^33 ≤ (1 : ℝ)^25
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s0_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1868905769/10000000000 : ℝ)*x 0 + (-1529005757/10000000000 : ℝ)*x 1 + (4249891393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1868905769/10000000000 : ℝ)^33 ≤ (27317149709/250000000000 : ℝ)^25 := by
    have hnat : (1868905769 : ℕ)^33*250000000000^25 ≤ 27317149709^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868905769 10000000000 27317149709 250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1529005757/10000000000 : ℝ)^33 ≤ (8383397122283/100000000000000 : ℝ)^25 := by
    have hnat : (1529005757 : ℕ)^33*100000000000000^25 ≤ 8383397122283^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1529005757 10000000000 8383397122283 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4249891393/5000000000 : ℝ)^33 ≤ (16137948595761/20000000000000 : ℝ)^25 := by
    have hnat : (4249891393 : ℕ)^33*20000000000000^25 ≤ 16137948595761^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249891393 5000000000 16137948595761 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1868905769/10000000000 : ℝ), (-1529005757/10000000000 : ℝ), (4249891393/5000000000 : ℝ)] ![(27317149709/250000000000 : ℝ), (8383397122283/100000000000000 : ℝ), (16137948595761/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1868905769/10000000000 : ℝ)|^33 ≤ (27317149709/250000000000 : ℝ)^25
        have hw : |(1868905769/10000000000 : ℝ)|=(1868905769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1529005757/10000000000 : ℝ)|^33 ≤ (8383397122283/100000000000000 : ℝ)^25
        have hw : |(-1529005757/10000000000 : ℝ)|=(1529005757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4249891393/5000000000 : ℝ)|^33 ≤ (16137948595761/20000000000000 : ℝ)^25
        have hw : |(4249891393/5000000000 : ℝ)|=(4249891393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s0_7 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3955768371/10000000000 : ℝ)*x 0 + (-303638097/625000000 : ℝ)*x 1 + (4221976827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3955768371/10000000000 : ℝ)^33 ≤ (14699911874607/50000000000000 : ℝ)^25 := by
    have hnat : (3955768371 : ℕ)^33*50000000000000^25 ≤ 14699911874607^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3955768371 10000000000 14699911874607 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (303638097/625000000 : ℝ)^33 ≤ (1928051569717/5000000000000 : ℝ)^25 := by
    have hnat : (303638097 : ℕ)^33*5000000000000^25 ≤ 1928051569717^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303638097 625000000 1928051569717 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4221976827/10000000000 : ℝ)^33 ≤ (800978621007/2500000000000 : ℝ)^25 := by
    have hnat : (4221976827 : ℕ)^33*2500000000000^25 ≤ 800978621007^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221976827 10000000000 800978621007 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3955768371/10000000000 : ℝ), (-303638097/625000000 : ℝ), (4221976827/10000000000 : ℝ)] ![(14699911874607/50000000000000 : ℝ), (1928051569717/5000000000000 : ℝ), (800978621007/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3955768371/10000000000 : ℝ)|^33 ≤ (14699911874607/50000000000000 : ℝ)^25
        have hw : |(-3955768371/10000000000 : ℝ)|=(3955768371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-303638097/625000000 : ℝ)|^33 ≤ (1928051569717/5000000000000 : ℝ)^25
        have hw : |(-303638097/625000000 : ℝ)|=(303638097/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4221976827/10000000000 : ℝ)|^33 ≤ (800978621007/2500000000000 : ℝ)^25
        have hw : |(4221976827/10000000000 : ℝ)|=(4221976827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s0_8 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2105987077/5000000000 : ℝ)*x 0 + (16165201/31250000 : ℝ)*x 1 + (1810952977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105987077/5000000000 : ℝ)^33 ≤ (15969492880333/50000000000000 : ℝ)^25 := by
    have hnat : (2105987077 : ℕ)^33*50000000000000^25 ≤ 15969492880333^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105987077 5000000000 15969492880333 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16165201/31250000 : ℝ)^33 ≤ (41891415502053/100000000000000 : ℝ)^25 := by
    have hnat : (16165201 : ℕ)^33*100000000000000^25 ≤ 41891415502053^25*31250000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16165201 31250000 41891415502053 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1810952977/5000000000 : ℝ)^33 ≤ (13084799364747/50000000000000 : ℝ)^25 := by
    have hnat : (1810952977 : ℕ)^33*50000000000000^25 ≤ 13084799364747^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1810952977 5000000000 13084799364747 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2105987077/5000000000 : ℝ), (16165201/31250000 : ℝ), (1810952977/5000000000 : ℝ)] ![(15969492880333/50000000000000 : ℝ), (41891415502053/100000000000000 : ℝ), (13084799364747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2105987077/5000000000 : ℝ)|^33 ≤ (15969492880333/50000000000000 : ℝ)^25
        have hw : |(2105987077/5000000000 : ℝ)|=(2105987077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16165201/31250000 : ℝ)|^33 ≤ (41891415502053/100000000000000 : ℝ)^25
        have hw : |(16165201/31250000 : ℝ)|=(16165201/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1810952977/5000000000 : ℝ)|^33 ≤ (13084799364747/50000000000000 : ℝ)^25
        have hw : |(1810952977/5000000000 : ℝ)|=(1810952977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s0_9 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5804528651/10000000000 : ℝ)*x 0 + (-2272061579/5000000000 : ℝ)*x 1 + (-497167453/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5804528651/10000000000 : ℝ)^33 ≤ (48772204503853/100000000000000 : ℝ)^25 := by
    have hnat : (5804528651 : ℕ)^33*100000000000000^25 ≤ 48772204503853^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5804528651 10000000000 48772204503853 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2272061579/5000000000 : ℝ)^33 ≤ (17652414946707/50000000000000 : ℝ)^25 := by
    have hnat : (2272061579 : ℕ)^33*50000000000000^25 ≤ 17652414946707^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272061579 5000000000 17652414946707 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497167453/2000000000 : ℝ)^33 ≤ (15922965581607/100000000000000 : ℝ)^25 := by
    have hnat : (497167453 : ℕ)^33*100000000000000^25 ≤ 15922965581607^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497167453 2000000000 15922965581607 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5804528651/10000000000 : ℝ), (-2272061579/5000000000 : ℝ), (-497167453/2000000000 : ℝ)] ![(48772204503853/100000000000000 : ℝ), (17652414946707/50000000000000 : ℝ), (15922965581607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5804528651/10000000000 : ℝ)|^33 ≤ (48772204503853/100000000000000 : ℝ)^25
        have hw : |(5804528651/10000000000 : ℝ)|=(5804528651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2272061579/5000000000 : ℝ)|^33 ≤ (17652414946707/50000000000000 : ℝ)^25
        have hw : |(-2272061579/5000000000 : ℝ)|=(2272061579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-497167453/2000000000 : ℝ)|^33 ≤ (15922965581607/100000000000000 : ℝ)^25
        have hw : |(-497167453/2000000000 : ℝ)|=(497167453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s0_12 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (518084311/5000000000 : ℝ)*x 0 + (-811173157/10000000000 : ℝ)*x 1 + (9337787849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518084311/5000000000 : ℝ)^33 ≤ (1254030747017/25000000000000 : ℝ)^25 := by
    have hnat : (518084311 : ℕ)^33*25000000000000^25 ≤ 1254030747017^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518084311 5000000000 1254030747017 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (811173157/10000000000 : ℝ)^33 ≤ (3631030637533/100000000000000 : ℝ)^25 := by
    have hnat : (811173157 : ℕ)^33*100000000000000^25 ≤ 3631030637533^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811173157 10000000000 3631030637533 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9337787849/10000000000 : ℝ)^33 ≤ (11419105794351/12500000000000 : ℝ)^25 := by
    have hnat : (9337787849 : ℕ)^33*12500000000000^25 ≤ 11419105794351^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9337787849 10000000000 11419105794351 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518084311/5000000000 : ℝ), (-811173157/10000000000 : ℝ), (9337787849/10000000000 : ℝ)] ![(1254030747017/25000000000000 : ℝ), (3631030637533/100000000000000 : ℝ), (11419105794351/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518084311/5000000000 : ℝ)|^33 ≤ (1254030747017/25000000000000 : ℝ)^25
        have hw : |(518084311/5000000000 : ℝ)|=(518084311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-811173157/10000000000 : ℝ)|^33 ≤ (3631030637533/100000000000000 : ℝ)^25
        have hw : |(-811173157/10000000000 : ℝ)|=(811173157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9337787849/10000000000 : ℝ)|^33 ≤ (11419105794351/12500000000000 : ℝ)^25
        have hw : |(9337787849/10000000000 : ℝ)|=(9337787849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s0_13 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1865166317/5000000000 : ℝ)*x 0 + (-2058412563/5000000000 : ℝ)*x 1 + (5164432523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1865166317/5000000000 : ℝ)^33 ≤ (13604318251473/50000000000000 : ℝ)^25 := by
    have hnat : (1865166317 : ℕ)^33*50000000000000^25 ≤ 13604318251473^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865166317 5000000000 13604318251473 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2058412563/5000000000 : ℝ)^33 ≤ (484219661449/1562500000000 : ℝ)^25 := by
    have hnat : (2058412563 : ℕ)^33*1562500000000^25 ≤ 484219661449^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058412563 5000000000 484219661449 1562500000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5164432523/10000000000 : ℝ)^33 ≤ (8360261029427/20000000000000 : ℝ)^25 := by
    have hnat : (5164432523 : ℕ)^33*20000000000000^25 ≤ 8360261029427^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5164432523 10000000000 8360261029427 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1865166317/5000000000 : ℝ), (-2058412563/5000000000 : ℝ), (5164432523/10000000000 : ℝ)] ![(13604318251473/50000000000000 : ℝ), (484219661449/1562500000000 : ℝ), (8360261029427/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1865166317/5000000000 : ℝ)|^33 ≤ (13604318251473/50000000000000 : ℝ)^25
        have hw : |(-1865166317/5000000000 : ℝ)|=(1865166317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2058412563/5000000000 : ℝ)|^33 ≤ (484219661449/1562500000000 : ℝ)^25
        have hw : |(-2058412563/5000000000 : ℝ)|=(2058412563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5164432523/10000000000 : ℝ)|^33 ≤ (8360261029427/20000000000000 : ℝ)^25
        have hw : |(5164432523/10000000000 : ℝ)|=(5164432523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s0_14 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2341429997/5000000000 : ℝ)*x 0 + (5168041989/10000000000 : ℝ)*x 1 + (3112652651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2341429997/5000000000 : ℝ)^33 ≤ (9183638031163/25000000000000 : ℝ)^25 := by
    have hnat : (2341429997 : ℕ)^33*25000000000000^25 ≤ 9183638031163^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2341429997 5000000000 9183638031163 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5168041989/10000000000 : ℝ)^33 ≤ (20919936820321/50000000000000 : ℝ)^25 := by
    have hnat : (5168041989 : ℕ)^33*50000000000000^25 ≤ 20919936820321^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168041989 10000000000 20919936820321 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3112652651/10000000000 : ℝ)^33 ≤ (10712787114551/50000000000000 : ℝ)^25 := by
    have hnat : (3112652651 : ℕ)^33*50000000000000^25 ≤ 10712787114551^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3112652651 10000000000 10712787114551 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2341429997/5000000000 : ℝ), (5168041989/10000000000 : ℝ), (3112652651/10000000000 : ℝ)] ![(9183638031163/25000000000000 : ℝ), (20919936820321/50000000000000 : ℝ), (10712787114551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2341429997/5000000000 : ℝ)|^33 ≤ (9183638031163/25000000000000 : ℝ)^25
        have hw : |(2341429997/5000000000 : ℝ)|=(2341429997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5168041989/10000000000 : ℝ)|^33 ≤ (20919936820321/50000000000000 : ℝ)^25
        have hw : |(5168041989/10000000000 : ℝ)|=(5168041989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3112652651/10000000000 : ℝ)|^33 ≤ (10712787114551/50000000000000 : ℝ)^25
        have hw : |(3112652651/10000000000 : ℝ)|=(3112652651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s0_15 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (239324769/400000000 : ℝ)*x 0 + (-1163035177/2500000000 : ℝ)*x 1 + (-1054729549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239324769/400000000 : ℝ)^33 ≤ (12690668973193/25000000000000 : ℝ)^25 := by
    have hnat : (239324769 : ℕ)^33*25000000000000^25 ≤ 12690668973193^25*400000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239324769 400000000 12690668973193 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1163035177/2500000000 : ℝ)^33 ≤ (36416797505241/100000000000000 : ℝ)^25 := by
    have hnat : (1163035177 : ℕ)^33*100000000000000^25 ≤ 36416797505241^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163035177 2500000000 36416797505241 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054729549/5000000000 : ℝ)^33 ≤ (12820526590493/100000000000000 : ℝ)^25 := by
    have hnat : (1054729549 : ℕ)^33*100000000000000^25 ≤ 12820526590493^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054729549 5000000000 12820526590493 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(239324769/400000000 : ℝ), (-1163035177/2500000000 : ℝ), (-1054729549/5000000000 : ℝ)] ![(12690668973193/25000000000000 : ℝ), (36416797505241/100000000000000 : ℝ), (12820526590493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(239324769/400000000 : ℝ)|^33 ≤ (12690668973193/25000000000000 : ℝ)^25
        have hw : |(239324769/400000000 : ℝ)|=(239324769/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1163035177/2500000000 : ℝ)|^33 ≤ (36416797505241/100000000000000 : ℝ)^25
        have hw : |(-1163035177/2500000000 : ℝ)|=(1163035177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1054729549/5000000000 : ℝ)|^33 ≤ (12820526590493/100000000000000 : ℝ)^25
        have hw : |(-1054729549/5000000000 : ℝ)|=(1054729549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s0_18 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1170449997/10000000000 : ℝ)*x 0 + (-910076813/10000000000 : ℝ)*x 1 + (9223664757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1170449997/10000000000 : ℝ)^33 ≤ (5891498637943/100000000000000 : ℝ)^25 := by
    have hnat : (1170449997 : ℕ)^33*100000000000000^25 ≤ 5891498637943^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170449997 10000000000 5891498637943 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (910076813/10000000000 : ℝ)^33 ≤ (4226520943627/100000000000000 : ℝ)^25 := by
    have hnat : (910076813 : ℕ)^33*100000000000000^25 ≤ 4226520943627^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910076813 10000000000 4226520943627 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9223664757/10000000000 : ℝ)^33 ≤ (44940990202353/50000000000000 : ℝ)^25 := by
    have hnat : (9223664757 : ℕ)^33*50000000000000^25 ≤ 44940990202353^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9223664757 10000000000 44940990202353 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1170449997/10000000000 : ℝ), (-910076813/10000000000 : ℝ), (9223664757/10000000000 : ℝ)] ![(5891498637943/100000000000000 : ℝ), (4226520943627/100000000000000 : ℝ), (44940990202353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1170449997/10000000000 : ℝ)|^33 ≤ (5891498637943/100000000000000 : ℝ)^25
        have hw : |(1170449997/10000000000 : ℝ)|=(1170449997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-910076813/10000000000 : ℝ)|^33 ≤ (4226520943627/100000000000000 : ℝ)^25
        have hw : |(-910076813/10000000000 : ℝ)|=(910076813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9223664757/10000000000 : ℝ)|^33 ≤ (44940990202353/50000000000000 : ℝ)^25
        have hw : |(9223664757/10000000000 : ℝ)|=(9223664757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s0_19 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-268348309/625000000 : ℝ)*x 0 + (-4151365461/10000000000 : ℝ)*x 1 + (4602817103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268348309/625000000 : ℝ)^33 ≤ (32758263817249/100000000000000 : ℝ)^25 := by
    have hnat : (268348309 : ℕ)^33*100000000000000^25 ≤ 32758263817249^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268348309 625000000 32758263817249 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4151365461/10000000000 : ℝ)^33 ≤ (31333728596593/100000000000000 : ℝ)^25 := by
    have hnat : (4151365461 : ℕ)^33*100000000000000^25 ≤ 31333728596593^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151365461 10000000000 31333728596593 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4602817103/10000000000 : ℝ)^33 ≤ (17954003781129/50000000000000 : ℝ)^25 := by
    have hnat : (4602817103 : ℕ)^33*50000000000000^25 ≤ 17954003781129^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4602817103 10000000000 17954003781129 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-268348309/625000000 : ℝ), (-4151365461/10000000000 : ℝ), (4602817103/10000000000 : ℝ)] ![(32758263817249/100000000000000 : ℝ), (31333728596593/100000000000000 : ℝ), (17954003781129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-268348309/625000000 : ℝ)|^33 ≤ (32758263817249/100000000000000 : ℝ)^25
        have hw : |(-268348309/625000000 : ℝ)|=(268348309/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4151365461/10000000000 : ℝ)|^33 ≤ (31333728596593/100000000000000 : ℝ)^25
        have hw : |(-4151365461/10000000000 : ℝ)|=(4151365461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4602817103/10000000000 : ℝ)|^33 ≤ (17954003781129/50000000000000 : ℝ)^25
        have hw : |(4602817103/10000000000 : ℝ)|=(4602817103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s0_20 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2059809583/5000000000 : ℝ)*x 0 + (5375723003/10000000000 : ℝ)*x 1 + (3488920097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2059809583/5000000000 : ℝ)^33 ≤ (15508912177737/50000000000000 : ℝ)^25 := by
    have hnat : (2059809583 : ℕ)^33*50000000000000^25 ≤ 15508912177737^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2059809583 5000000000 15508912177737 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375723003/10000000000 : ℝ)^33 ≤ (11018353296827/25000000000000 : ℝ)^25 := by
    have hnat : (5375723003 : ℕ)^33*25000000000000^25 ≤ 11018353296827^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375723003 10000000000 11018353296827 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3488920097/10000000000 : ℝ)^33 ≤ (12454381224467/50000000000000 : ℝ)^25 := by
    have hnat : (3488920097 : ℕ)^33*50000000000000^25 ≤ 12454381224467^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3488920097 10000000000 12454381224467 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2059809583/5000000000 : ℝ), (5375723003/10000000000 : ℝ), (3488920097/10000000000 : ℝ)] ![(15508912177737/50000000000000 : ℝ), (11018353296827/25000000000000 : ℝ), (12454381224467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2059809583/5000000000 : ℝ)|^33 ≤ (15508912177737/50000000000000 : ℝ)^25
        have hw : |(2059809583/5000000000 : ℝ)|=(2059809583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375723003/10000000000 : ℝ)|^33 ≤ (11018353296827/25000000000000 : ℝ)^25
        have hw : |(5375723003/10000000000 : ℝ)|=(5375723003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3488920097/10000000000 : ℝ)|^33 ≤ (12454381224467/50000000000000 : ℝ)^25
        have hw : |(3488920097/10000000000 : ℝ)|=(3488920097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s0_21 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5756839347/10000000000 : ℝ)*x 0 + (-4532885113/10000000000 : ℝ)*x 1 + (-2561570591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5756839347/10000000000 : ℝ)^33 ≤ (24121984248797/50000000000000 : ℝ)^25 := by
    have hnat : (5756839347 : ℕ)^33*50000000000000^25 ≤ 24121984248797^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5756839347 10000000000 24121984248797 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4532885113/10000000000 : ℝ)^33 ≤ (35189623455393/100000000000000 : ℝ)^25 := by
    have hnat : (4532885113 : ℕ)^33*100000000000000^25 ≤ 35189623455393^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532885113 10000000000 35189623455393 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2561570591/10000000000 : ℝ)^33 ≤ (8283204012243/50000000000000 : ℝ)^25 := by
    have hnat : (2561570591 : ℕ)^33*50000000000000^25 ≤ 8283204012243^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2561570591 10000000000 8283204012243 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5756839347/10000000000 : ℝ), (-4532885113/10000000000 : ℝ), (-2561570591/10000000000 : ℝ)] ![(24121984248797/50000000000000 : ℝ), (35189623455393/100000000000000 : ℝ), (8283204012243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5756839347/10000000000 : ℝ)|^33 ≤ (24121984248797/50000000000000 : ℝ)^25
        have hw : |(5756839347/10000000000 : ℝ)|=(5756839347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4532885113/10000000000 : ℝ)|^33 ≤ (35189623455393/100000000000000 : ℝ)^25
        have hw : |(-4532885113/10000000000 : ℝ)|=(4532885113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2561570591/10000000000 : ℝ)|^33 ≤ (8283204012243/50000000000000 : ℝ)^25
        have hw : |(-2561570591/10000000000 : ℝ)|=(2561570591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s0_25 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (324981781/2000000000 : ℝ)*x 0 + (-461487247/2500000000 : ℝ)*x 1 + (2114480537/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324981781/2000000000 : ℝ)^33 ≤ (908435933909/10000000000000 : ℝ)^25 := by
    have hnat : (324981781 : ℕ)^33*10000000000000^25 ≤ 908435933909^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324981781 2000000000 908435933909 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (461487247/2500000000 : ℝ)^33 ≤ (2687509490023/25000000000000 : ℝ)^25 := by
    have hnat : (461487247 : ℕ)^33*25000000000000^25 ≤ 2687509490023^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461487247 2500000000 2687509490023 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114480537/2500000000 : ℝ)^33 ≤ (80165602690169/100000000000000 : ℝ)^25 := by
    have hnat : (2114480537 : ℕ)^33*100000000000000^25 ≤ 80165602690169^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114480537 2500000000 80165602690169 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324981781/2000000000 : ℝ), (-461487247/2500000000 : ℝ), (2114480537/2500000000 : ℝ)] ![(908435933909/10000000000000 : ℝ), (2687509490023/25000000000000 : ℝ), (80165602690169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324981781/2000000000 : ℝ)|^33 ≤ (908435933909/10000000000000 : ℝ)^25
        have hw : |(324981781/2000000000 : ℝ)|=(324981781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-461487247/2500000000 : ℝ)|^33 ≤ (2687509490023/25000000000000 : ℝ)^25
        have hw : |(-461487247/2500000000 : ℝ)|=(461487247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2114480537/2500000000 : ℝ)|^33 ≤ (80165602690169/100000000000000 : ℝ)^25
        have hw : |(2114480537/2500000000 : ℝ)|=(2114480537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s1_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-494409807/1250000000 : ℝ)*x 0 + (-408156963/1000000000 : ℝ)*x 1 + (998321223/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (494409807/1250000000 : ℝ)^33 ≤ (29395017570287/100000000000000 : ℝ)^25 := by
    have hnat : (494409807 : ℕ)^33*100000000000000^25 ≤ 29395017570287^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494409807 1250000000 29395017570287 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408156963/1000000000 : ℝ)^33 ≤ (3830027832273/12500000000000 : ℝ)^25 := by
    have hnat : (408156963 : ℕ)^33*12500000000000^25 ≤ 3830027832273^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408156963 1000000000 3830027832273 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (998321223/2000000000 : ℝ)^33 ≤ (7992951952413/20000000000000 : ℝ)^25 := by
    have hnat : (998321223 : ℕ)^33*20000000000000^25 ≤ 7992951952413^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998321223 2000000000 7992951952413 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-494409807/1250000000 : ℝ), (-408156963/1000000000 : ℝ), (998321223/2000000000 : ℝ)] ![(29395017570287/100000000000000 : ℝ), (3830027832273/12500000000000 : ℝ), (7992951952413/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-494409807/1250000000 : ℝ)|^33 ≤ (29395017570287/100000000000000 : ℝ)^25
        have hw : |(-494409807/1250000000 : ℝ)|=(494409807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-408156963/1000000000 : ℝ)|^33 ≤ (3830027832273/12500000000000 : ℝ)^25
        have hw : |(-408156963/1000000000 : ℝ)|=(408156963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(998321223/2000000000 : ℝ)|^33 ≤ (7992951952413/20000000000000 : ℝ)^25
        have hw : |(998321223/2000000000 : ℝ)|=(998321223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s1_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4530110949/10000000000 : ℝ)*x 0 + (4674756399/10000000000 : ℝ)*x 1 + (1915815209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4530110949/10000000000 : ℝ)^33 ≤ (35161198261487/100000000000000 : ℝ)^25 := by
    have hnat : (4530110949 : ℕ)^33*100000000000000^25 ≤ 35161198261487^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530110949 10000000000 35161198261487 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4674756399/10000000000 : ℝ)^33 ≤ (36650665074163/100000000000000 : ℝ)^25 := by
    have hnat : (4674756399 : ℕ)^33*100000000000000^25 ≤ 36650665074163^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4674756399 10000000000 36650665074163 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1915815209/5000000000 : ℝ)^33 ≤ (2818813665393/10000000000000 : ℝ)^25 := by
    have hnat : (1915815209 : ℕ)^33*10000000000000^25 ≤ 2818813665393^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915815209 5000000000 2818813665393 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4530110949/10000000000 : ℝ), (4674756399/10000000000 : ℝ), (1915815209/5000000000 : ℝ)] ![(35161198261487/100000000000000 : ℝ), (36650665074163/100000000000000 : ℝ), (2818813665393/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4530110949/10000000000 : ℝ)|^33 ≤ (35161198261487/100000000000000 : ℝ)^25
        have hw : |(4530110949/10000000000 : ℝ)|=(4530110949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4674756399/10000000000 : ℝ)|^33 ≤ (36650665074163/100000000000000 : ℝ)^25
        have hw : |(4674756399/10000000000 : ℝ)|=(4674756399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1915815209/5000000000 : ℝ)|^33 ≤ (2818813665393/10000000000000 : ℝ)^25
        have hw : |(1915815209/5000000000 : ℝ)|=(1915815209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s1_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2375237213/5000000000 : ℝ)*x 0 + (-2279742231/5000000000 : ℝ)*x 1 + (-1859587099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2375237213/5000000000 : ℝ)^33 ≤ (1169884107123/3125000000000 : ℝ)^25 := by
    have hnat : (2375237213 : ℕ)^33*3125000000000^25 ≤ 1169884107123^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2375237213 5000000000 1169884107123 3125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2279742231/5000000000 : ℝ)^33 ≤ (7092490659431/20000000000000 : ℝ)^25 := by
    have hnat : (2279742231 : ℕ)^33*20000000000000^25 ≤ 7092490659431^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279742231 5000000000 7092490659431 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1859587099/5000000000 : ℝ)^33 ≤ (27101255258827/100000000000000 : ℝ)^25 := by
    have hnat : (1859587099 : ℕ)^33*100000000000000^25 ≤ 27101255258827^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859587099 5000000000 27101255258827 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2375237213/5000000000 : ℝ), (-2279742231/5000000000 : ℝ), (-1859587099/5000000000 : ℝ)] ![(1169884107123/3125000000000 : ℝ), (7092490659431/20000000000000 : ℝ), (27101255258827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2375237213/5000000000 : ℝ)|^33 ≤ (1169884107123/3125000000000 : ℝ)^25
        have hw : |(2375237213/5000000000 : ℝ)|=(2375237213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2279742231/5000000000 : ℝ)|^33 ≤ (7092490659431/20000000000000 : ℝ)^25
        have hw : |(-2279742231/5000000000 : ℝ)|=(2279742231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1859587099/5000000000 : ℝ)|^33 ≤ (27101255258827/100000000000000 : ℝ)^25
        have hw : |(-1859587099/5000000000 : ℝ)|=(1859587099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303073_s1_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3929441143/10000000000 : ℝ)*x 0 + (-471432541/1250000000 : ℝ)*x 1 + (2649865127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3929441143/10000000000 : ℝ)^33 ≤ (1821363619657/6250000000000 : ℝ)^25 := by
    have hnat : (3929441143 : ℕ)^33*6250000000000^25 ≤ 1821363619657^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3929441143 10000000000 1821363619657 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (471432541/1250000000 : ℝ)^33 ≤ (5521061608637/20000000000000 : ℝ)^25 := by
    have hnat : (471432541 : ℕ)^33*20000000000000^25 ≤ 5521061608637^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471432541 1250000000 5521061608637 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2649865127/5000000000 : ℝ)^33 ≤ (21626437013043/50000000000000 : ℝ)^25 := by
    have hnat : (2649865127 : ℕ)^33*50000000000000^25 ≤ 21626437013043^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2649865127 5000000000 21626437013043 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3929441143/10000000000 : ℝ), (-471432541/1250000000 : ℝ), (2649865127/5000000000 : ℝ)] ![(1821363619657/6250000000000 : ℝ), (5521061608637/20000000000000 : ℝ), (21626437013043/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3929441143/10000000000 : ℝ)|^33 ≤ (1821363619657/6250000000000 : ℝ)^25
        have hw : |(3929441143/10000000000 : ℝ)|=(3929441143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-471432541/1250000000 : ℝ)|^33 ≤ (5521061608637/20000000000000 : ℝ)^25
        have hw : |(-471432541/1250000000 : ℝ)|=(471432541/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2649865127/5000000000 : ℝ)|^33 ≤ (21626437013043/50000000000000 : ℝ)^25
        have hw : |(2649865127/5000000000 : ℝ)|=(2649865127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303073 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
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
  have s0_pow0 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(368994434359861/2000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-3928074809/10000000000 : ℝ)*X 0 0+(-224280777/500000000 : ℝ)*X 0 1+(92556031/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2232198407/5000000000 : ℝ)*X 1 0+(5098061697/10000000000 : ℝ)*X 1 1+(3436596411/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_5 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(-1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s0_5 p hpa hpb (pair X 2)
    change _ ≤ P 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((1868905769/10000000000 : ℝ)*X 0 0+(-1529005757/10000000000 : ℝ)*X 0 1+(4249891393/5000000000 : ℝ)*X 0 2+(1868905769/10000000000 : ℝ)*X 1 0+(-1529005757/10000000000 : ℝ)*X 1 1+(4249891393/5000000000 : ℝ)*X 1 2+(1868905769/10000000000 : ℝ)*X 2 0+(-1529005757/10000000000 : ℝ)*X 2 1+(4249891393/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-3955768371/10000000000 : ℝ)*X 0 0+(-303638097/625000000 : ℝ)*X 0 1+(4221976827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2105987077/5000000000 : ℝ)*X 1 0+(16165201/31250000 : ℝ)*X 1 1+(1810952977/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((5804528651/10000000000 : ℝ)*X 2 0+(-2272061579/5000000000 : ℝ)*X 2 1+(-497167453/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_12 : ((518084311/5000000000 : ℝ)*X 0 0+(-811173157/10000000000 : ℝ)*X 0 1+(9337787849/10000000000 : ℝ)*X 0 2+(518084311/5000000000 : ℝ)*X 1 0+(-811173157/10000000000 : ℝ)*X 1 1+(9337787849/10000000000 : ℝ)*X 1 2+(518084311/5000000000 : ℝ)*X 2 0+(-811173157/10000000000 : ℝ)*X 2 1+(9337787849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s0_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-1865166317/5000000000 : ℝ)*X 0 0+(-2058412563/5000000000 : ℝ)*X 0 1+(5164432523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((2341429997/5000000000 : ℝ)*X 1 0+(5168041989/10000000000 : ℝ)*X 1 1+(3112652651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((239324769/400000000 : ℝ)*X 2 0+(-1163035177/2500000000 : ℝ)*X 2 1+(-1054729549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_18 : ((1170449997/10000000000 : ℝ)*X 0 0+(-910076813/10000000000 : ℝ)*X 0 1+(9223664757/10000000000 : ℝ)*X 0 2+(1170449997/10000000000 : ℝ)*X 1 0+(-910076813/10000000000 : ℝ)*X 1 1+(9223664757/10000000000 : ℝ)*X 1 2+(1170449997/10000000000 : ℝ)*X 2 0+(-910076813/10000000000 : ℝ)*X 2 1+(9223664757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s0_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((-268348309/625000000 : ℝ)*X 0 0+(-4151365461/10000000000 : ℝ)*X 0 1+(4602817103/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s0_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((2059809583/5000000000 : ℝ)*X 1 0+(5375723003/10000000000 : ℝ)*X 1 1+(3488920097/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s0_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((5756839347/10000000000 : ℝ)*X 2 0+(-4532885113/10000000000 : ℝ)*X 2 1+(-2561570591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s0_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((324981781/2000000000 : ℝ)*X 0 0+(-461487247/2500000000 : ℝ)*X 0 1+(2114480537/2500000000 : ℝ)*X 0 2+(324981781/2000000000 : ℝ)*X 1 0+(-461487247/2500000000 : ℝ)*X 1 1+(2114480537/2500000000 : ℝ)*X 1 2+(324981781/2000000000 : ℝ)*X 2 0+(-461487247/2500000000 : ℝ)*X 2 1+(2114480537/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((6029/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6029/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (34813896141010816841361/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (139442190959/1000000000000 : ℝ)*(base40) + (535978135559/1000000000000 : ℝ)*(base59) + (7358514229059/1000000000000 : ℝ)*(major_s0_0) + (7358514229059/1000000000000 : ℝ)*(major_s0_1) + (6699775616257/500000000000 : ℝ)*(major_s0_2) + (7374763/125000000000 : ℝ)*(sp_s0_0) + (1208207400691/200000000000 : ℝ)*(sp_s0_5) + (9824988526493/1000000000000 : ℝ)*(sp_s0_7) + (9824738709691/1000000000000 : ℝ)*(sp_s0_8) + (4912114527057/500000000000 : ℝ)*(sp_s0_9) + (4891898934273/1000000000000 : ℝ)*(sp_s0_12) + (39839159/500000000000 : ℝ)*(sp_s0_18) + (61762981/200000000000 : ℝ)*(sp_s0_20) + (818470483/1000000000000 : ℝ)*(sp_s0_21) + (4891978612591/1000000000000 : ℝ)*(f.failure) + (9825047524597/1000000000000 : ℝ)*(f.sum) + (281393381718069/5000000000000000000000000000 : ℝ)*base62 + (102083808576467/625000000000000000000000000 : ℝ)*base64 + (498158693399201/2000000000000000000000000000 : ℝ)*base66 + (341849170539723/1000000000000000000000000000 : ℝ)*base69 + (1282090121219477/10000000000000000000000000000 : ℝ)*base70 + (706556956229171/1250000000000000000000000000 : ℝ)*base73 + (49393852354171/1250000000000000000000000000 : ℝ)*base74 + (873905013399201/2000000000000000000000000000 : ℝ)*base76 + (2279358258837363/10000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1911/5000000000000000 : ℝ)*base87 + (1911/5000000000000000 : ℝ)*base89 + (1911/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-33251/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-33251/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9197038625589534009747/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (399719165851/500000000000 : ℝ)*(base40) + (642808528537/500000000000 : ℝ)*(base59) + (8456916100869/1000000000000 : ℝ)*(major_s0_0) + (8456916100869/1000000000000 : ℝ)*(major_s0_1) + (3402702600687/250000000000 : ℝ)*(major_s0_2) + (212389683/500000000000 : ℝ)*(sp_s0_1) + (5153894301879/1000000000000 : ℝ)*(sp_s0_5) + (115041221/1000000000000 : ℝ)*(sp_s0_6) + (39488083/125000000000 : ℝ)*(sp_s0_9) + (5645702466027/500000000000 : ℝ)*(sp_s0_13) + (35285001923/3125000000 : ℝ)*(sp_s0_14) + (5645654745031/500000000000 : ℝ)*(sp_s0_15) + (56220868607/10000000000 : ℝ)*(sp_s0_18) + (13778917/62500000000 : ℝ)*(sp_s0_19) + (5622201901921/1000000000000 : ℝ)*(f.failure) + (5645812697363/500000000000 : ℝ)*(f.sum) + (253835723321343/2500000000000000000000000000 : ℝ)*base63 + (215190909349953/312500000000000000000000000 : ℝ)*base65 + (1208560491980791/2000000000000000000000000000 : ℝ)*base66 + (197705224474507/500000000000000000000000000 : ℝ)*base68 + (865893965294541/10000000000000000000000000000 : ℝ)*base71 + (632818675846939/1250000000000000000000000000 : ℝ)*base72 + (469386131028061/1250000000000000000000000000 : ℝ)*base74 + (515150361819209/2000000000000000000000000000 : ℝ)*base77 + (1490545980679467/10000000000000000000000000000 : ℝ)*base78 + (2841/5000000000000000 : ℝ)*base87 + (2841/5000000000000000 : ℝ)*base89 + (2841/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(607/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(607/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (403436737091578339863/125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2194601/500000000000 : ℝ)*(base1) + (556156701887/1000000000000 : ℝ)*(base40) + (1268302017909/1000000000000 : ℝ)*(base59) + (794010481661/125000000000 : ℝ)*(major_s0_0) + (794010481661/125000000000 : ℝ)*(major_s0_1) + (794010481661/125000000000 : ℝ)*(major_s0_2) + (16015603/500000000000 : ℝ)*(sp_s0_0) + (7669109/250000000000 : ℝ)*(sp_s0_6) + (103981/31250000000 : ℝ)*(sp_s0_7) + (178786287/1000000000000 : ℝ)*(sp_s0_9) + (2120309302039/250000000000 : ℝ)*(sp_s0_19) + (530079261097/62500000000 : ℝ)*(sp_s0_20) + (1696217878253/200000000000 : ℝ)*(sp_s0_21) + (131964480861/31250000000 : ℝ)*(sp_s0_25) + (422289845319/100000000000 : ℝ)*(f.failure) + (530079261097/62500000000 : ℝ)*(f.sum) + (133593882096323/1250000000000000000000000000 : ℝ)*base63 + (30241018486491/156250000000000000000000000 : ℝ)*base64 + (51477658590879/250000000000000000000000000 : ℝ)*base66 + (27327601909121/250000000000000000000000000 : ℝ)*base68 + (991613847346323/1250000000000000000000000000 : ℝ)*base70 + (36157045513509/156250000000000000000000000 : ℝ)*base73 + (14363570076009/156250000000000000000000000 : ℝ)*base74 + (59651392015879/250000000000000000000000000 : ℝ)*base76 + (415277340903677/1250000000000000000000000000 : ℝ)*base79 + (199/500000000000000 : ℝ)*base87 + (199/500000000000000 : ℝ)*base89 + (199/500000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (6029/25000 : ℝ) ^ (131/32 : ℝ) ≤ (296013978730221557/100000000000000000000 : ℝ) := by
    have hpowers : (6029/25000 : ℝ)^131 ≤ (296013978730221557/100000000000000000000 : ℝ)^32 := by
      have hnat : (6029 : ℕ)^131*100000000000000000000^32 ≤ 296013978730221557^32*25000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6029 25000 296013978730221557 100000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6029/25000 : ℝ)) (X := (296013978730221557/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (100296013978730221557/100000000000000000000 : ℝ) ≤ (200144456037519/200000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (100296013978730221557/100000000000000000000 : ℝ)^32 ≤ (200144456037519/200000000000000 : ℝ)^131 := by
      have hnat : (100296013978730221557 : ℕ)^32*200000000000000^131 ≤ 200144456037519^131*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100296013978730221557 100000000000000000000 200144456037519 200000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200144456037519/200000000000000 : ℝ)) (X := (100296013978730221557/100000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (50296013978730221557/50000000000000000000 : ℝ) ≤ (10014429511576047/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50296013978730221557/50000000000000000000 : ℝ)^32 ≤ (10014429511576047/10000000000000000 : ℝ)^131 := by
      have hnat : (50296013978730221557 : ℕ)^32*10000000000000000^131 ≤ 10014429511576047^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50296013978730221557 50000000000000000000 10014429511576047 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014429511576047/10000000000000000 : ℝ)) (X := (50296013978730221557/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(144456037519/48232000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(7206709700097/2411600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (6029/25000 : ℝ)) (alpha := (144456037519/48232000000000 : ℝ)) (beta := (7206709700097/2411600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (6029/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(144456037519/48232000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(7206709700097/2411600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (33251/100000 : ℝ) ^ (131/32 : ℝ) ≤ (220504791524355373/20000000000000000000 : ℝ) := by
    have hpowers : (33251/100000 : ℝ)^131 ≤ (220504791524355373/20000000000000000000 : ℝ)^32 := by
      have hnat : (33251 : ℕ)^131*20000000000000000000^32 ≤ 220504791524355373^32*100000^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33251 100000 220504791524355373 20000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33251/100000 : ℝ)) (X := (220504791524355373/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (20220504791524355373/20000000000000000000 : ℝ) ≤ (5013410201260659/5000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (20220504791524355373/20000000000000000000 : ℝ)^32 ≤ (5013410201260659/5000000000000000 : ℝ)^131 := by
      have hnat : (20220504791524355373 : ℕ)^32*5000000000000000^131 ≤ 5013410201260659^131*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20220504791524355373 20000000000000000000 5013410201260659 5000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013410201260659/5000000000000000 : ℝ)) (X := (20220504791524355373/20000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (10220504791524355373/10000000000000000000 : ℝ) ≤ (10053420675304281/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (10220504791524355373/10000000000000000000 : ℝ)^32 ≤ (10053420675304281/10000000000000000 : ℝ)^131 := by
      have hnat : (10220504791524355373 : ℕ)^32*10000000000000000^131 ≤ 10053420675304281^131*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10220504791524355373 10000000000000000000 10053420675304281 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10053420675304281/10000000000000000 : ℝ)) (X := (10220504791524355373/10000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(13410201260659/1662550000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(26600272782963/3325100000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (33251/100000 : ℝ)) (alpha := (13410201260659/1662550000000000 : ℝ)) (beta := (26600272782963/3325100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (33251/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(13410201260659/1662550000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(26600272782963/3325100000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (607/12500 : ℝ) ^ (131/32 : ℝ) ≤ (209374285664569/50000000000000000000 : ℝ) := by
    have hpowers : (607/12500 : ℝ)^131 ≤ (209374285664569/50000000000000000000 : ℝ)^32 := by
      have hnat : (607 : ℕ)^131*50000000000000000000^32 ≤ 209374285664569^32*12500^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        607 12500 209374285664569 50000000000000000000 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (607/12500 : ℝ)) (X := (209374285664569/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50000209374285664569/50000000000000000000 : ℝ) ≤ (200000204579131/200000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (50000209374285664569/50000000000000000000 : ℝ)^32 ≤ (200000204579131/200000000000000 : ℝ)^131 := by
      have hnat : (50000209374285664569 : ℕ)^32*200000000000000^131 ≤ 200000204579131^131*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000209374285664569 50000000000000000000 200000204579131 200000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200000204579131/200000000000000 : ℝ)) (X := (50000209374285664569/50000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25000209374285664569/25000000000000000000 : ℝ) ≤ (10000020457880729/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (25000209374285664569/25000000000000000000 : ℝ)^32 ≤ (10000020457880729/10000000000000000 : ℝ)^131 := by
      have hnat : (25000209374285664569 : ℕ)^32*10000000000000000^131 ≤ 10000020457880729^131*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000209374285664569 25000000000000000000 10000020457880729 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000020457880729/10000000000000000 : ℝ)) (X := (25000209374285664569/25000000000000000000 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(204579131/9712000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(10228924179/485600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (607/12500 : ℝ)) (alpha := (204579131/9712000000000 : ℝ)) (beta := (10228924179/485600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (607/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(204579131/9712000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(10228924179/485600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-494409807/1250000000 : ℝ)*X 0 0+(-408156963/1000000000 : ℝ)*X 0 1+(998321223/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4530110949/10000000000 : ℝ)*X 1 0+(4674756399/10000000000 : ℝ)*X 1 1+(1915815209/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2375237213/5000000000 : ℝ)*X 2 0+(-2279742231/5000000000 : ℝ)*X 2 1+(-1859587099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3929441143/10000000000 : ℝ)*X 0 0+(-471432541/1250000000 : ℝ)*X 0 1+(2649865127/5000000000 : ℝ)*X 0 2+(3929441143/10000000000 : ℝ)*X 1 0+(-471432541/1250000000 : ℝ)*X 1 1+(2649865127/5000000000 : ℝ)*X 1 2+(3929441143/10000000000 : ℝ)*X 2 0+(-471432541/1250000000 : ℝ)*X 2 1+(2649865127/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303073_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15063/2500 : ℝ) < ((-7521/5000 : ℝ)*P 0+(-7521/5000 : ℝ)*P 1+(-7521/5000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15063/2500 : ℝ) < (-36068250499071952274491801643992743/6084272967650000000000000000000000 : ℝ) := by norm_num
    linear_combination (49/488281250 : ℝ)*(base1) + (507/15625000000 : ℝ)*(base17) + (89/1250000000 : ℝ)*(base22) + (110788833437/500000000000 : ℝ)*(base40) + (13463/125000000000 : ℝ)*(base43) + (20063899527/125000000000 : ℝ)*(base49) + (536546288441/1000000000000 : ℝ)*(base59) + (216057445661/1000000000000 : ℝ)*(base60) + (7521/5000 : ℝ)*(major_s1_0) + (188024986537/125000000000 : ℝ)*(major_s1_1) + (7521/5000 : ℝ)*(major_s1_2) + (1976037266167/1000000000000 : ℝ)*(sp_s1_0) + (1976037241071/1000000000000 : ℝ)*(sp_s1_1) + (395207418923/200000000000 : ℝ)*(sp_s1_2) + (488281201/488281250 : ℝ)*(sp_s1_6) + (1976037273519/1000000000000 : ℝ)*(f.sum) + (87579130970410253/252291962500000000000000000000 : ℝ)*base63 + (954419630839/3035000000000000000000000 : ℝ)*base65 + (162522923577171/1662550000000000000000000000 : ℝ)*base66 + (3509938545899/6070000000000000000000000 : ℝ)*base69 + (2816273659036471/7319206000000000000000000000 : ℝ)*base70 + (313205401983/6029000000000000000000000 : ℝ)*base72 + (157585924011147/831275000000000000000000000 : ℝ)*base74 + (19755863303773/30145000000000000000000000 : ℝ)*base77 + (758001653083161917/5011756975000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c303074_s0_0 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-645995399/2500000000 : ℝ)*x 0 + (-1538089879/2500000000 : ℝ)*x 1 + (-1018757431/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (645995399/2500000000 : ℝ)^33 ≤ (16757993950399/100000000000000 : ℝ)^25 := by
    have hnat : (645995399 : ℕ)^33*100000000000000^25 ≤ 16757993950399^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645995399 2500000000 16757993950399 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1538089879/2500000000 : ℝ)^33 ≤ (52666571996071/100000000000000 : ℝ)^25 := by
    have hnat : (1538089879 : ℕ)^33*100000000000000^25 ≤ 52666571996071^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1538089879 2500000000 52666571996071 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1018757431/2500000000 : ℝ)^33 ≤ (7643858508769/25000000000000 : ℝ)^25 := by
    have hnat : (1018757431 : ℕ)^33*25000000000000^25 ≤ 7643858508769^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018757431 2500000000 7643858508769 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-645995399/2500000000 : ℝ), (-1538089879/2500000000 : ℝ), (-1018757431/2500000000 : ℝ)] ![(16757993950399/100000000000000 : ℝ), (52666571996071/100000000000000 : ℝ), (7643858508769/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-645995399/2500000000 : ℝ)|^33 ≤ (16757993950399/100000000000000 : ℝ)^25
        have hw : |(-645995399/2500000000 : ℝ)|=(645995399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1538089879/2500000000 : ℝ)|^33 ≤ (52666571996071/100000000000000 : ℝ)^25
        have hw : |(-1538089879/2500000000 : ℝ)|=(1538089879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1018757431/2500000000 : ℝ)|^33 ≤ (7643858508769/25000000000000 : ℝ)^25
        have hw : |(-1018757431/2500000000 : ℝ)|=(1018757431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303074_s0_1 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1256208183/2000000000 : ℝ)*x 0 + (2742860033/10000000000 : ℝ)*x 1 + (-3785726487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1256208183/2000000000 : ℝ)^33 ≤ (54125477604767/100000000000000 : ℝ)^25 := by
    have hnat : (1256208183 : ℕ)^33*100000000000000^25 ≤ 54125477604767^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256208183 2000000000 54125477604767 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2742860033/10000000000 : ℝ)^33 ≤ (9065647272459/50000000000000 : ℝ)^25 := by
    have hnat : (2742860033 : ℕ)^33*50000000000000^25 ≤ 9065647272459^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742860033 10000000000 9065647272459 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3785726487/10000000000 : ℝ)^33 ≤ (5548645566631/20000000000000 : ℝ)^25 := by
    have hnat : (3785726487 : ℕ)^33*20000000000000^25 ≤ 5548645566631^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3785726487 10000000000 5548645566631 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1256208183/2000000000 : ℝ), (2742860033/10000000000 : ℝ), (-3785726487/10000000000 : ℝ)] ![(54125477604767/100000000000000 : ℝ), (9065647272459/50000000000000 : ℝ), (5548645566631/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1256208183/2000000000 : ℝ)|^33 ≤ (54125477604767/100000000000000 : ℝ)^25
        have hw : |(1256208183/2000000000 : ℝ)|=(1256208183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2742860033/10000000000 : ℝ)|^33 ≤ (9065647272459/50000000000000 : ℝ)^25
        have hw : |(2742860033/10000000000 : ℝ)|=(2742860033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3785726487/10000000000 : ℝ)|^33 ≤ (5548645566631/20000000000000 : ℝ)^25
        have hw : |(-3785726487/10000000000 : ℝ)|=(3785726487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303074_s0_2 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3540199999/10000000000 : ℝ)*x 0 + (-1920353461/5000000000 : ℝ)*x 1 + (5583019727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3540199999/10000000000 : ℝ)^33 ≤ (507863134201/2000000000000 : ℝ)^25 := by
    have hnat : (3540199999 : ℕ)^33*2000000000000^25 ≤ 507863134201^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3540199999 10000000000 507863134201 2000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1920353461/5000000000 : ℝ)^33 ≤ (28276310497949/100000000000000 : ℝ)^25 := by
    have hnat : (1920353461 : ℕ)^33*100000000000000^25 ≤ 28276310497949^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920353461 5000000000 28276310497949 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5583019727/10000000000 : ℝ)^33 ≤ (23165266386221/50000000000000 : ℝ)^25 := by
    have hnat : (5583019727 : ℕ)^33*50000000000000^25 ≤ 23165266386221^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5583019727 10000000000 23165266386221 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3540199999/10000000000 : ℝ), (-1920353461/5000000000 : ℝ), (5583019727/10000000000 : ℝ)] ![(507863134201/2000000000000 : ℝ), (28276310497949/100000000000000 : ℝ), (23165266386221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3540199999/10000000000 : ℝ)|^33 ≤ (507863134201/2000000000000 : ℝ)^25
        have hw : |(3540199999/10000000000 : ℝ)|=(3540199999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1920353461/5000000000 : ℝ)|^33 ≤ (28276310497949/100000000000000 : ℝ)^25
        have hw : |(-1920353461/5000000000 : ℝ)|=(1920353461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5583019727/10000000000 : ℝ)|^33 ≤ (23165266386221/50000000000000 : ℝ)^25
        have hw : |(5583019727/10000000000 : ℝ)|=(5583019727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303074_s0_3 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2499999997/2500000000 : ℝ)*x 0 + (2079/10000000000 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2499999997/2500000000 : ℝ)^33 ≤ (99999999841601/100000000000000 : ℝ)^25 := by
    have hnat : (2499999997 : ℕ)^33*100000000000000^25 ≤ 99999999841601^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2499999997 2500000000 99999999841601 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079/10000000000 : ℝ)^33 ≤ (75603/50000000000000 : ℝ)^25 := by
    have hnat : (2079 : ℕ)^33*50000000000000^25 ≤ 75603^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079 10000000000 75603 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^33 ≤ (0 : ℝ)^25 := by
    have hnat : (0 : ℕ)^33*1^25 ≤ 0^25*1^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2499999997/2500000000 : ℝ), (2079/10000000000 : ℝ), (0 : ℝ)] ![(99999999841601/100000000000000 : ℝ), (75603/50000000000000 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2499999997/2500000000 : ℝ)|^33 ≤ (99999999841601/100000000000000 : ℝ)^25
        have hw : |(2499999997/2500000000 : ℝ)|=(2499999997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2079/10000000000 : ℝ)|^33 ≤ (75603/50000000000000 : ℝ)^25
        have hw : |(2079/10000000000 : ℝ)|=(2079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^33 ≤ (0 : ℝ)^25
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c303074_s0_6 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (523622507/1000000000 : ℝ)*x 0 + (-2286910521/5000000000 : ℝ)*x 1 + (-3155992169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523622507/1000000000 : ℝ)^33 ≤ (42570050315023/100000000000000 : ℝ)^25 := by
    have hnat : (523622507 : ℕ)^33*100000000000000^25 ≤ 42570050315023^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523622507 1000000000 42570050315023 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2286910521/5000000000 : ℝ)^33 ≤ (8902428834203/25000000000000 : ℝ)^25 := by
    have hnat : (2286910521 : ℕ)^33*25000000000000^25 ≤ 8902428834203^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286910521 5000000000 8902428834203 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3155992169/10000000000 : ℝ)^33 ≤ (21820234335887/100000000000000 : ℝ)^25 := by
    have hnat : (3155992169 : ℕ)^33*100000000000000^25 ≤ 21820234335887^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3155992169 10000000000 21820234335887 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523622507/1000000000 : ℝ), (-2286910521/5000000000 : ℝ), (-3155992169/10000000000 : ℝ)] ![(42570050315023/100000000000000 : ℝ), (8902428834203/25000000000000 : ℝ), (21820234335887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523622507/1000000000 : ℝ)|^33 ≤ (42570050315023/100000000000000 : ℝ)^25
        have hw : |(523622507/1000000000 : ℝ)|=(523622507/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2286910521/5000000000 : ℝ)|^33 ≤ (8902428834203/25000000000000 : ℝ)^25
        have hw : |(-2286910521/5000000000 : ℝ)|=(2286910521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3155992169/10000000000 : ℝ)|^33 ≤ (21820234335887/100000000000000 : ℝ)^25
        have hw : |(-3155992169/10000000000 : ℝ)|=(3155992169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c303074 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76461/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76461/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76461/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76461/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(154156222119969/1250000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (131/32 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^131 ≤ (1 : ℝ)^32 := by
      have hnat : (1 : ℕ)^131*1^32 ≤ 1^32*1^131 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 131 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (2368994434359861/2000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (2 : ℝ)^32 ≤ (2368994434359861/2000000000000000 : ℝ)^131 := by
      have hnat : (2 : ℕ)^32*2000000000000000^131 ≤ 2368994434359861^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 2368994434359861 2000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2368994434359861/2000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (13078221948759057/10000000000000000 : ℝ) ^ (131/32 : ℝ) := by
    have hpowers : (3 : ℝ)^32 ≤ (13078221948759057/10000000000000000 : ℝ)^131 := by
      have hnat : (3 : ℕ)^32*10000000000000000^131 ≤ 13078221948759057^131*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 13078221948759057 10000000000000000 32 131 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (13078221948759057/10000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 131 32 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (131/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (368994434359861/2000000000000000 : ℝ)) (beta := (154156222119969/1250000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(368994434359861/2000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(154156222119969/1250000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-645995399/2500000000 : ℝ)*X 0 0+(-1538089879/2500000000 : ℝ)*X 0 1+(-1018757431/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303074_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1256208183/2000000000 : ℝ)*X 1 0+(2742860033/10000000000 : ℝ)*X 1 1+(-3785726487/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c303074_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3540199999/10000000000 : ℝ)*X 2 0+(-1920353461/5000000000 : ℝ)*X 2 1+(5583019727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c303074_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_3 : ((2499999997/2500000000 : ℝ)*X 1 0+(2079/10000000000 : ℝ)*X 1 1+(2499999997/2500000000 : ℝ)*X 2 0+(2079/10000000000 : ℝ)*X 2 1+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c303074_s0_3 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((523622507/1000000000 : ℝ)*X 0 0+(-2286910521/5000000000 : ℝ)*X 0 1+(-3155992169/10000000000 : ℝ)*X 0 2+(523622507/1000000000 : ℝ)*X 1 0+(-2286910521/5000000000 : ℝ)*X 1 1+(-3155992169/10000000000 : ℝ)*X 1 2+(523622507/1000000000 : ℝ)*X 2 0+(-2286910521/5000000000 : ℝ)*X 2 1+(-3155992169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c303074_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-15063/2500 : ℝ) < ((-7521/5000 : ℝ)*P 0+(-7521/5000 : ℝ)*P 1+(-7521/5000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-15063/2500 : ℝ) < (-15022569431636478763718028021/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (193131/1000000000000 : ℝ)*(base1) + (2343/200000000000 : ℝ)*(base22) + (244810812033/1000000000000 : ℝ)*(base39) + (180814655749/1000000000000 : ℝ)*(base49) + (18969564301/200000000000 : ℝ)*(base50) + (2607/500000000000 : ℝ)*(base54) + (13/1600000000 : ℝ)*(base59) + (376050156093/250000000000 : ℝ)*(major_s0_0) + (7521/5000 : ℝ)*(major_s0_1) + (752099997393/500000000000 : ℝ)*(major_s0_2) + (2003009450677/1000000000000 : ℝ)*(sp_s0_0) + (2003009257547/1000000000000 : ℝ)*(sp_s0_1) + (1001504620309/500000000000 : ℝ)*(sp_s0_2) + (156093/250000000000 : ℝ)*(sp_s0_3) + (124999975207/125000000000 : ℝ)*(sp_s0_6) + (2003009257547/1000000000000 : ℝ)*(f.sum) + (476625658957627/1000000000000000000000000000 : ℝ)*base62 + (130111465490817/625000000000000000000000000 : ℝ)*base64 + (22684003/2500000000000000000000 : ℝ)*base67 + (181708172257627/1000000000000000000000000000 : ℝ)*base68 + (214016864202097/2500000000000000000000000000 : ℝ)*base71 + (289389923977367/312500000000000000000000000 : ℝ)*base73 + (930270619/5000000000000000000000 : ℝ)*base74 + (13161718216927/500000000000000000000000000 : ℝ)*base76 + (134651246633617/312500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
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
theorem coarse_distinct_p003_b032 (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 73 ≤ c.val) (hhi : c.val < 77)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=73 ∨ c=74 ∨ c=75 ∨ c=76 := by omega
  rcases hc with rfl|rfl|rfl|rfl
  · exact collision_c303073 p hpa (by linarith only [hpb]) X hX
  · exact collision_c303074 p hpa (by linarith only [hpb]) X hX
  · exact collision_c10075 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))
  · exact collision_c10076 p (by linarith only [hpa]) (by linarith only [hpb]) X (orderedChart_weaken
      (by linarith only [hpa]) hX (by norm_num) (by norm_num) (by norm_num))

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (131/32 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (c : Fin 88) (hlo : 73 ≤ c.val) (hhi : c.val < 77)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7521/5000 : ℝ) (91389/50000 : ℝ) (76461/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p003_b032 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

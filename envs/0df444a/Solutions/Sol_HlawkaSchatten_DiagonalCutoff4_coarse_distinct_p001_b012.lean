-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b012
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:23:38.897995+00:00
-- url     : https://prove2.me/submissions/add658bd-bcc2-43c2-9cbe-b886a06468d0

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_collision_c301023
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
theorem collision_support_c301022_s0_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (256902019/1000000000 : ℝ)*x 0 + (1132102107/2000000000 : ℝ)*x 1 + (4678773257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256902019/1000000000 : ℝ)^65 ≤ (16483086719371/100000000000000 : ℝ)^49 := by
    have hnat : (256902019 : ℕ)^65*100000000000000^49 ≤ 16483086719371^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256902019 1000000000 16483086719371 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132102107/2000000000 : ℝ)^65 ≤ (23503113404229/50000000000000 : ℝ)^49 := by
    have hnat : (1132102107 : ℕ)^65*50000000000000^49 ≤ 23503113404229^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132102107 2000000000 23503113404229 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4678773257/10000000000 : ℝ)^65 ≤ (2281917904117/6250000000000 : ℝ)^49 := by
    have hnat : (4678773257 : ℕ)^65*6250000000000^49 ≤ 2281917904117^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4678773257 10000000000 2281917904117 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(256902019/1000000000 : ℝ), (1132102107/2000000000 : ℝ), (4678773257/10000000000 : ℝ)] ![(16483086719371/100000000000000 : ℝ), (23503113404229/50000000000000 : ℝ), (2281917904117/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(256902019/1000000000 : ℝ)|^65 ≤ (16483086719371/100000000000000 : ℝ)^49
        have hw : |(256902019/1000000000 : ℝ)|=(256902019/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1132102107/2000000000 : ℝ)|^65 ≤ (23503113404229/50000000000000 : ℝ)^49
        have hw : |(1132102107/2000000000 : ℝ)|=(1132102107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4678773257/10000000000 : ℝ)|^65 ≤ (2281917904117/6250000000000 : ℝ)^49
        have hw : |(4678773257/10000000000 : ℝ)|=(4678773257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301022_s0_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2827942441/10000000000 : ℝ)*x 0 + (3774558671/10000000000 : ℝ)*x 1 + (-6268436247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2827942441/10000000000 : ℝ)^65 ≤ (3744457532123/20000000000000 : ℝ)^49 := by
    have hnat : (2827942441 : ℕ)^65*20000000000000^49 ≤ 3744457532123^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2827942441 10000000000 3744457532123 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3774558671/10000000000 : ℝ)^65 ≤ (13729984264057/50000000000000 : ℝ)^49 := by
    have hnat : (3774558671 : ℕ)^65*50000000000000^49 ≤ 13729984264057^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3774558671 10000000000 13729984264057 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6268436247/10000000000 : ℝ)^65 ≤ (13454435951777/25000000000000 : ℝ)^49 := by
    have hnat : (6268436247 : ℕ)^65*25000000000000^49 ≤ 13454435951777^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6268436247 10000000000 13454435951777 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2827942441/10000000000 : ℝ), (3774558671/10000000000 : ℝ), (-6268436247/10000000000 : ℝ)] ![(3744457532123/20000000000000 : ℝ), (13729984264057/50000000000000 : ℝ), (13454435951777/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2827942441/10000000000 : ℝ)|^65 ≤ (3744457532123/20000000000000 : ℝ)^49
        have hw : |(-2827942441/10000000000 : ℝ)|=(2827942441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3774558671/10000000000 : ℝ)|^65 ≤ (13729984264057/50000000000000 : ℝ)^49
        have hw : |(3774558671/10000000000 : ℝ)|=(3774558671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6268436247/10000000000 : ℝ)|^65 ≤ (13454435951777/25000000000000 : ℝ)^49
        have hw : |(-6268436247/10000000000 : ℝ)|=(6268436247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301022_s0_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7403947107/10000000000 : ℝ)*x 0 + (-292831567/10000000000 : ℝ)*x 1 + (-4231785717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7403947107/10000000000 : ℝ)^65 ≤ (33559005767477/50000000000000 : ℝ)^49 := by
    have hnat : (7403947107 : ℕ)^65*50000000000000^49 ≤ 33559005767477^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7403947107 10000000000 33559005767477 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (292831567/10000000000 : ℝ)^65 ≤ (924531457573/100000000000000 : ℝ)^49 := by
    have hnat : (292831567 : ℕ)^65*100000000000000^49 ≤ 924531457573^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292831567 10000000000 924531457573 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231785717/10000000000 : ℝ)^65 ≤ (7989364249411/25000000000000 : ℝ)^49 := by
    have hnat : (4231785717 : ℕ)^65*25000000000000^49 ≤ 7989364249411^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231785717 10000000000 7989364249411 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7403947107/10000000000 : ℝ), (-292831567/10000000000 : ℝ), (-4231785717/10000000000 : ℝ)] ![(33559005767477/50000000000000 : ℝ), (924531457573/100000000000000 : ℝ), (7989364249411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7403947107/10000000000 : ℝ)|^65 ≤ (33559005767477/50000000000000 : ℝ)^49
        have hw : |(7403947107/10000000000 : ℝ)|=(7403947107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-292831567/10000000000 : ℝ)|^65 ≤ (924531457573/100000000000000 : ℝ)^49
        have hw : |(-292831567/10000000000 : ℝ)|=(292831567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4231785717/10000000000 : ℝ)|^65 ≤ (7989364249411/25000000000000 : ℝ)^49
        have hw : |(-4231785717/10000000000 : ℝ)|=(4231785717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301022_s0_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1697392551/10000000000 : ℝ)*x 0 + (1767763199/2500000000 : ℝ)*x 1 + (470306469/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1697392551/10000000000 : ℝ)^65 ≤ (1189029542483/12500000000000 : ℝ)^49 := by
    have hnat : (1697392551 : ℕ)^65*12500000000000^49 ≤ 1189029542483^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1697392551 10000000000 1189029542483 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1767763199/2500000000 : ℝ)^65 ≤ (31572286034279/50000000000000 : ℝ)^49 := by
    have hnat : (1767763199 : ℕ)^65*50000000000000^49 ≤ 31572286034279^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1767763199 2500000000 31572286034279 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (470306469/1250000000 : ℝ)^65 ≤ (13671595790723/50000000000000 : ℝ)^49 := by
    have hnat : (470306469 : ℕ)^65*50000000000000^49 ≤ 13671595790723^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470306469 1250000000 13671595790723 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1697392551/10000000000 : ℝ), (1767763199/2500000000 : ℝ), (470306469/1250000000 : ℝ)] ![(1189029542483/12500000000000 : ℝ), (31572286034279/50000000000000 : ℝ), (13671595790723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1697392551/10000000000 : ℝ)|^65 ≤ (1189029542483/12500000000000 : ℝ)^49
        have hw : |(1697392551/10000000000 : ℝ)|=(1697392551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1767763199/2500000000 : ℝ)|^65 ≤ (31572286034279/50000000000000 : ℝ)^49
        have hw : |(1767763199/2500000000 : ℝ)|=(1767763199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(470306469/1250000000 : ℝ)|^65 ≤ (13671595790723/50000000000000 : ℝ)^49
        have hw : |(470306469/1250000000 : ℝ)|=(470306469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301022_s0_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2889712943/10000000000 : ℝ)*x 0 + (3885191041/5000000000 : ℝ)*x 1 + (-51613711/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2889712943/10000000000 : ℝ)^65 ≤ (2408337079691/12500000000000 : ℝ)^49 := by
    have hnat : (2889712943 : ℕ)^65*12500000000000^49 ≤ 2408337079691^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2889712943 10000000000 2408337079691 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3885191041/5000000000 : ℝ)^65 ≤ (14311938169861/20000000000000 : ℝ)^49 := by
    have hnat : (3885191041 : ℕ)^65*20000000000000^49 ≤ 14311938169861^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3885191041 5000000000 14311938169861 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51613711/312500000 : ℝ)^65 ≤ (9173612496611/100000000000000 : ℝ)^49 := by
    have hnat : (51613711 : ℕ)^65*100000000000000^49 ≤ 9173612496611^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51613711 312500000 9173612496611 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2889712943/10000000000 : ℝ), (3885191041/5000000000 : ℝ), (-51613711/312500000 : ℝ)] ![(2408337079691/12500000000000 : ℝ), (14311938169861/20000000000000 : ℝ), (9173612496611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2889712943/10000000000 : ℝ)|^65 ≤ (2408337079691/12500000000000 : ℝ)^49
        have hw : |(2889712943/10000000000 : ℝ)|=(2889712943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3885191041/5000000000 : ℝ)|^65 ≤ (14311938169861/20000000000000 : ℝ)^49
        have hw : |(3885191041/5000000000 : ℝ)|=(3885191041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51613711/312500000 : ℝ)|^65 ≤ (9173612496611/100000000000000 : ℝ)^49
        have hw : |(-51613711/312500000 : ℝ)|=(51613711/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301022_s0_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3124311487/10000000000 : ℝ)*x 0 + (1049828043/2500000000 : ℝ)*x 1 + (-5659839917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3124311487/10000000000 : ℝ)^65 ≤ (5342150942327/25000000000000 : ℝ)^49 := by
    have hnat : (3124311487 : ℕ)^65*25000000000000^49 ≤ 5342150942327^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3124311487 10000000000 5342150942327 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049828043/2500000000 : ℝ)^65 ≤ (7908139170523/25000000000000 : ℝ)^49 := by
    have hnat : (1049828043 : ℕ)^65*25000000000000^49 ≤ 7908139170523^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049828043 2500000000 7908139170523 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5659839917/10000000000 : ℝ)^65 ≤ (11749709885047/25000000000000 : ℝ)^49 := by
    have hnat : (5659839917 : ℕ)^65*25000000000000^49 ≤ 11749709885047^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5659839917 10000000000 11749709885047 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3124311487/10000000000 : ℝ), (1049828043/2500000000 : ℝ), (-5659839917/10000000000 : ℝ)] ![(5342150942327/25000000000000 : ℝ), (7908139170523/25000000000000 : ℝ), (11749709885047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3124311487/10000000000 : ℝ)|^65 ≤ (5342150942327/25000000000000 : ℝ)^49
        have hw : |(-3124311487/10000000000 : ℝ)|=(3124311487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049828043/2500000000 : ℝ)|^65 ≤ (7908139170523/25000000000000 : ℝ)^49
        have hw : |(1049828043/2500000000 : ℝ)|=(1049828043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5659839917/10000000000 : ℝ)|^65 ≤ (11749709885047/25000000000000 : ℝ)^49
        have hw : |(-5659839917/10000000000 : ℝ)|=(5659839917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301022_s0_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (439982991/500000000 : ℝ)*x 0 + (-162563681/1250000000 : ℝ)*x 1 + (-1617225599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (439982991/500000000 : ℝ)^65 ≤ (42199013517659/50000000000000 : ℝ)^49 := by
    have hnat : (439982991 : ℕ)^65*50000000000000^49 ≤ 42199013517659^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439982991 500000000 42199013517659 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162563681/1250000000 : ℝ)^65 ≤ (668104588079/10000000000000 : ℝ)^49 := by
    have hnat : (162563681 : ℕ)^65*10000000000000^49 ≤ 668104588079^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162563681 1250000000 668104588079 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1617225599/10000000000 : ℝ)^65 ≤ (4460463536173/50000000000000 : ℝ)^49 := by
    have hnat : (1617225599 : ℕ)^65*50000000000000^49 ≤ 4460463536173^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1617225599 10000000000 4460463536173 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(439982991/500000000 : ℝ), (-162563681/1250000000 : ℝ), (-1617225599/10000000000 : ℝ)] ![(42199013517659/50000000000000 : ℝ), (668104588079/10000000000000 : ℝ), (4460463536173/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(439982991/500000000 : ℝ)|^65 ≤ (42199013517659/50000000000000 : ℝ)^49
        have hw : |(439982991/500000000 : ℝ)|=(439982991/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-162563681/1250000000 : ℝ)|^65 ≤ (668104588079/10000000000000 : ℝ)^49
        have hw : |(-162563681/1250000000 : ℝ)|=(162563681/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1617225599/10000000000 : ℝ)|^65 ≤ (4460463536173/50000000000000 : ℝ)^49
        have hw : |(-1617225599/10000000000 : ℝ)|=(1617225599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301022_s0_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1920535889/10000000000 : ℝ)*x 0 + (2879162113/5000000000 : ℝ)*x 1 + (5078730507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1920535889/10000000000 : ℝ)^65 ≤ (87544314019/781250000000 : ℝ)^49 := by
    have hnat : (1920535889 : ℕ)^65*781250000000^49 ≤ 87544314019^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920535889 10000000000 87544314019 781250000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2879162113/5000000000 : ℝ)^65 ≤ (24043376781811/50000000000000 : ℝ)^49 := by
    have hnat : (2879162113 : ℕ)^65*50000000000000^49 ≤ 24043376781811^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2879162113 5000000000 24043376781811 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5078730507/10000000000 : ℝ)^65 ≤ (40707574226673/100000000000000 : ℝ)^49 := by
    have hnat : (5078730507 : ℕ)^65*100000000000000^49 ≤ 40707574226673^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078730507 10000000000 40707574226673 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1920535889/10000000000 : ℝ), (2879162113/5000000000 : ℝ), (5078730507/10000000000 : ℝ)] ![(87544314019/781250000000 : ℝ), (24043376781811/50000000000000 : ℝ), (40707574226673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1920535889/10000000000 : ℝ)|^65 ≤ (87544314019/781250000000 : ℝ)^49
        have hw : |(1920535889/10000000000 : ℝ)|=(1920535889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2879162113/5000000000 : ℝ)|^65 ≤ (24043376781811/50000000000000 : ℝ)^49
        have hw : |(2879162113/5000000000 : ℝ)|=(2879162113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5078730507/10000000000 : ℝ)|^65 ≤ (40707574226673/100000000000000 : ℝ)^49
        have hw : |(5078730507/10000000000 : ℝ)|=(5078730507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301022_s0_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (494121733/2000000000 : ℝ)*x 0 + (5044154541/10000000000 : ℝ)*x 1 + (-215448843/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (494121733/2000000000 : ℝ)^65 ≤ (7825387818983/50000000000000 : ℝ)^49 := by
    have hnat : (494121733 : ℕ)^65*50000000000000^49 ≤ 7825387818983^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494121733 2000000000 7825387818983 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5044154541/10000000000 : ℝ)^65 ≤ (20170176438433/50000000000000 : ℝ)^49 := by
    have hnat : (5044154541 : ℕ)^65*50000000000000^49 ≤ 20170176438433^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5044154541 10000000000 20170176438433 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215448843/400000000 : ℝ)^65 ≤ (2200443573349/5000000000000 : ℝ)^49 := by
    have hnat : (215448843 : ℕ)^65*5000000000000^49 ≤ 2200443573349^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215448843 400000000 2200443573349 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(494121733/2000000000 : ℝ), (5044154541/10000000000 : ℝ), (-215448843/400000000 : ℝ)] ![(7825387818983/50000000000000 : ℝ), (20170176438433/50000000000000 : ℝ), (2200443573349/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(494121733/2000000000 : ℝ)|^65 ≤ (7825387818983/50000000000000 : ℝ)^49
        have hw : |(494121733/2000000000 : ℝ)|=(494121733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5044154541/10000000000 : ℝ)|^65 ≤ (20170176438433/50000000000000 : ℝ)^49
        have hw : |(5044154541/10000000000 : ℝ)|=(5044154541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-215448843/400000000 : ℝ)|^65 ≤ (2200443573349/5000000000000 : ℝ)^49
        have hw : |(-215448843/400000000 : ℝ)|=(215448843/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301022_s0_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2037846891/10000000000 : ℝ)*x 0 + (434813/781250 : ℝ)*x 1 + (-5191765719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037846891/10000000000 : ℝ)^65 ≤ (189415249693/1562500000000 : ℝ)^49 := by
    have hnat : (2037846891 : ℕ)^65*1562500000000^49 ≤ 189415249693^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037846891 10000000000 189415249693 1562500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (434813/781250 : ℝ)^65 ≤ (11490912983213/25000000000000 : ℝ)^49 := by
    have hnat : (434813 : ℕ)^65*25000000000000^49 ≤ 11490912983213^49*781250^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434813 781250 11490912983213 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5191765719/10000000000 : ℝ)^65 ≤ (838275441463/2000000000000 : ℝ)^49 := by
    have hnat : (5191765719 : ℕ)^65*2000000000000^49 ≤ 838275441463^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191765719 10000000000 838275441463 2000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2037846891/10000000000 : ℝ), (434813/781250 : ℝ), (-5191765719/10000000000 : ℝ)] ![(189415249693/1562500000000 : ℝ), (11490912983213/25000000000000 : ℝ), (838275441463/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2037846891/10000000000 : ℝ)|^65 ≤ (189415249693/1562500000000 : ℝ)^49
        have hw : |(-2037846891/10000000000 : ℝ)|=(2037846891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(434813/781250 : ℝ)|^65 ≤ (11490912983213/25000000000000 : ℝ)^49
        have hw : |(434813/781250 : ℝ)|=(434813/781250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5191765719/10000000000 : ℝ)|^65 ≤ (838275441463/2000000000000 : ℝ)^49
        have hw : |(-5191765719/10000000000 : ℝ)|=(5191765719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301022_s0_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2136863093/2500000000 : ℝ)*x 0 + (-570369737/10000000000 : ℝ)*x 1 + (-515537901/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136863093/2500000000 : ℝ)^65 ≤ (81204347682051/100000000000000 : ℝ)^49 := by
    have hnat : (2136863093 : ℕ)^65*100000000000000^49 ≤ 81204347682051^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136863093 2500000000 81204347682051 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (570369737/10000000000 : ℝ)^65 ≤ (2238739110837/100000000000000 : ℝ)^49 := by
    have hnat : (570369737 : ℕ)^65*100000000000000^49 ≤ 2238739110837^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570369737 10000000000 2238739110837 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (515537901/2000000000 : ℝ)^65 ≤ (16556913191079/100000000000000 : ℝ)^49 := by
    have hnat : (515537901 : ℕ)^65*100000000000000^49 ≤ 16556913191079^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515537901 2000000000 16556913191079 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2136863093/2500000000 : ℝ), (-570369737/10000000000 : ℝ), (-515537901/2000000000 : ℝ)] ![(81204347682051/100000000000000 : ℝ), (2238739110837/100000000000000 : ℝ), (16556913191079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2136863093/2500000000 : ℝ)|^65 ≤ (81204347682051/100000000000000 : ℝ)^49
        have hw : |(2136863093/2500000000 : ℝ)|=(2136863093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-570369737/10000000000 : ℝ)|^65 ≤ (2238739110837/100000000000000 : ℝ)^49
        have hw : |(-570369737/10000000000 : ℝ)|=(570369737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-515537901/2000000000 : ℝ)|^65 ≤ (16556913191079/100000000000000 : ℝ)^49
        have hw : |(-515537901/2000000000 : ℝ)|=(515537901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301022_s0_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (928601539/5000000000 : ℝ)*x 0 + (1206697749/2000000000 : ℝ)*x 1 + (151054253/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (928601539/5000000000 : ℝ)^65 ≤ (10718144437721/100000000000000 : ℝ)^49 := by
    have hnat : (928601539 : ℕ)^65*100000000000000^49 ≤ 10718144437721^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928601539 5000000000 10718144437721 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1206697749/2000000000 : ℝ)^65 ≤ (25579226732069/50000000000000 : ℝ)^49 := by
    have hnat : (1206697749 : ℕ)^65*50000000000000^49 ≤ 25579226732069^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206697749 2000000000 25579226732069 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (151054253/312500000 : ℝ)^65 ≤ (9530850521479/25000000000000 : ℝ)^49 := by
    have hnat : (151054253 : ℕ)^65*25000000000000^49 ≤ 9530850521479^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151054253 312500000 9530850521479 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(928601539/5000000000 : ℝ), (1206697749/2000000000 : ℝ), (151054253/312500000 : ℝ)] ![(10718144437721/100000000000000 : ℝ), (25579226732069/50000000000000 : ℝ), (9530850521479/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(928601539/5000000000 : ℝ)|^65 ≤ (10718144437721/100000000000000 : ℝ)^49
        have hw : |(928601539/5000000000 : ℝ)|=(928601539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1206697749/2000000000 : ℝ)|^65 ≤ (25579226732069/50000000000000 : ℝ)^49
        have hw : |(1206697749/2000000000 : ℝ)|=(1206697749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(151054253/312500000 : ℝ)|^65 ≤ (9530850521479/25000000000000 : ℝ)^49
        have hw : |(151054253/312500000 : ℝ)|=(151054253/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301022_s0_25 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2897/5000000000 : ℝ)*x 0 + (9999999919/10000000000 : ℝ)*x 1 + (-2897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2897/5000000000 : ℝ)^65 ≤ (532599/100000000000000 : ℝ)^49 := by
    have hnat : (2897 : ℕ)^65*100000000000000^49 ≤ 532599^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2897 5000000000 532599 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9999999919/10000000000 : ℝ)^65 ≤ (99999998925511/100000000000000 : ℝ)^49 := by
    have hnat : (9999999919 : ℕ)^65*100000000000000^49 ≤ 99999998925511^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999919 10000000000 99999998925511 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2897/5000000000 : ℝ)^65 ≤ (532599/100000000000000 : ℝ)^49 := by
    have hnat : (2897 : ℕ)^65*100000000000000^49 ≤ 532599^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2897 5000000000 532599 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2897/5000000000 : ℝ), (9999999919/10000000000 : ℝ), (-2897/5000000000 : ℝ)] ![(532599/100000000000000 : ℝ), (99999998925511/100000000000000 : ℝ), (532599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2897/5000000000 : ℝ)|^65 ≤ (532599/100000000000000 : ℝ)^49
        have hw : |(-2897/5000000000 : ℝ)|=(2897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9999999919/10000000000 : ℝ)|^65 ≤ (99999998925511/100000000000000 : ℝ)^49
        have hw : |(9999999919/10000000000 : ℝ)|=(9999999919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2897/5000000000 : ℝ)|^65 ≤ (532599/100000000000000 : ℝ)^49
        have hw : |(-2897/5000000000 : ℝ)|=(2897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301022_s0_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5216408173/10000000000 : ℝ)*x 0 + (5751146991/10000000000 : ℝ)*x 1 + (-1737943533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5216408173/10000000000 : ℝ)^65 ≤ (10544469622347/25000000000000 : ℝ)^49 := by
    have hnat : (5216408173 : ℕ)^65*25000000000000^49 ≤ 10544469622347^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216408173 10000000000 10544469622347 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5751146991/10000000000 : ℝ)^65 ≤ (24003631518363/50000000000000 : ℝ)^49 := by
    have hnat : (5751146991 : ℕ)^65*50000000000000^49 ≤ 24003631518363^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5751146991 10000000000 24003631518363 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1737943533/10000000000 : ℝ)^65 ≤ (9814858463473/100000000000000 : ℝ)^49 := by
    have hnat : (1737943533 : ℕ)^65*100000000000000^49 ≤ 9814858463473^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1737943533 10000000000 9814858463473 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5216408173/10000000000 : ℝ), (5751146991/10000000000 : ℝ), (-1737943533/10000000000 : ℝ)] ![(10544469622347/25000000000000 : ℝ), (24003631518363/50000000000000 : ℝ), (9814858463473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5216408173/10000000000 : ℝ)|^65 ≤ (10544469622347/25000000000000 : ℝ)^49
        have hw : |(5216408173/10000000000 : ℝ)|=(5216408173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5751146991/10000000000 : ℝ)|^65 ≤ (24003631518363/50000000000000 : ℝ)^49
        have hw : |(5751146991/10000000000 : ℝ)|=(5751146991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1737943533/10000000000 : ℝ)|^65 ≤ (9814858463473/100000000000000 : ℝ)^49
        have hw : |(-1737943533/10000000000 : ℝ)|=(1737943533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301022_s1_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-14618339/39062500 : ℝ)*x 0 + (118137723/250000000 : ℝ)*x 1 + (-4615358201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14618339/39062500 : ℝ)^65 ≤ (13574520151063/50000000000000 : ℝ)^49 := by
    have hnat : (14618339 : ℕ)^65*50000000000000^49 ≤ 13574520151063^49*39062500^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14618339 39062500 13574520151063 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118137723/250000000 : ℝ)^65 ≤ (36995260112491/100000000000000 : ℝ)^49 := by
    have hnat : (118137723 : ℕ)^65*100000000000000^49 ≤ 36995260112491^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118137723 250000000 36995260112491 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4615358201/10000000000 : ℝ)^65 ≤ (35855699570949/100000000000000 : ℝ)^49 := by
    have hnat : (4615358201 : ℕ)^65*100000000000000^49 ≤ 35855699570949^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4615358201 10000000000 35855699570949 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14618339/39062500 : ℝ), (118137723/250000000 : ℝ), (-4615358201/10000000000 : ℝ)] ![(13574520151063/50000000000000 : ℝ), (36995260112491/100000000000000 : ℝ), (35855699570949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14618339/39062500 : ℝ)|^65 ≤ (13574520151063/50000000000000 : ℝ)^49
        have hw : |(-14618339/39062500 : ℝ)|=(14618339/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(118137723/250000000 : ℝ)|^65 ≤ (36995260112491/100000000000000 : ℝ)^49
        have hw : |(118137723/250000000 : ℝ)|=(118137723/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4615358201/10000000000 : ℝ)|^65 ≤ (35855699570949/100000000000000 : ℝ)^49
        have hw : |(-4615358201/10000000000 : ℝ)|=(4615358201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301022_s1_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5701526761/10000000000 : ℝ)*x 0 + (-2783344539/10000000000 : ℝ)*x 1 + (-1113681509/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5701526761/10000000000 : ℝ)^65 ≤ (47458588071687/100000000000000 : ℝ)^49 := by
    have hnat : (5701526761 : ℕ)^65*100000000000000^49 ≤ 47458588071687^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5701526761 10000000000 47458588071687 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2783344539/10000000000 : ℝ)^65 ≤ (18331629942181/100000000000000 : ℝ)^49 := by
    have hnat : (2783344539 : ℕ)^65*100000000000000^49 ≤ 18331629942181^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2783344539 10000000000 18331629942181 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1113681509/2500000000 : ℝ)^65 ≤ (4276222747747/12500000000000 : ℝ)^49 := by
    have hnat : (1113681509 : ℕ)^65*12500000000000^49 ≤ 4276222747747^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1113681509 2500000000 4276222747747 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5701526761/10000000000 : ℝ), (-2783344539/10000000000 : ℝ), (-1113681509/2500000000 : ℝ)] ![(47458588071687/100000000000000 : ℝ), (18331629942181/100000000000000 : ℝ), (4276222747747/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5701526761/10000000000 : ℝ)|^65 ≤ (47458588071687/100000000000000 : ℝ)^49
        have hw : |(5701526761/10000000000 : ℝ)|=(5701526761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2783344539/10000000000 : ℝ)|^65 ≤ (18331629942181/100000000000000 : ℝ)^49
        have hw : |(-2783344539/10000000000 : ℝ)|=(2783344539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1113681509/2500000000 : ℝ)|^65 ≤ (4276222747747/12500000000000 : ℝ)^49
        have hw : |(-1113681509/2500000000 : ℝ)|=(1113681509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301022_s1_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3646369541/10000000000 : ℝ)*x 0 + (4929502971/10000000000 : ℝ)*x 1 + (1124263489/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3646369541/10000000000 : ℝ)^65 ≤ (131148939773/500000000000 : ℝ)^49 := by
    have hnat : (3646369541 : ℕ)^65*500000000000^49 ≤ 131148939773^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3646369541 10000000000 131148939773 500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4929502971/10000000000 : ℝ)^65 ≤ (19564283880767/50000000000000 : ℝ)^49 := by
    have hnat : (4929502971 : ℕ)^65*50000000000000^49 ≤ 19564283880767^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4929502971 10000000000 19564283880767 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124263489/2500000000 : ℝ)^65 ≤ (34641644275213/100000000000000 : ℝ)^49 := by
    have hnat : (1124263489 : ℕ)^65*100000000000000^49 ≤ 34641644275213^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124263489 2500000000 34641644275213 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3646369541/10000000000 : ℝ), (4929502971/10000000000 : ℝ), (1124263489/2500000000 : ℝ)] ![(131148939773/500000000000 : ℝ), (19564283880767/50000000000000 : ℝ), (34641644275213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3646369541/10000000000 : ℝ)|^65 ≤ (131148939773/500000000000 : ℝ)^49
        have hw : |(3646369541/10000000000 : ℝ)|=(3646369541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4929502971/10000000000 : ℝ)|^65 ≤ (19564283880767/50000000000000 : ℝ)^49
        have hw : |(4929502971/10000000000 : ℝ)|=(4929502971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124263489/2500000000 : ℝ)|^65 ≤ (34641644275213/100000000000000 : ℝ)^49
        have hw : |(1124263489/2500000000 : ℝ)|=(1124263489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301022_s1_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (66021411/156250000 : ℝ)*x 0 + (2744076729/5000000000 : ℝ)*x 1 + (-660274621/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66021411/156250000 : ℝ)^65 ≤ (127572822211/400000000000 : ℝ)^49 := by
    have hnat : (66021411 : ℕ)^65*400000000000^49 ≤ 127572822211^49*156250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66021411 156250000 127572822211 400000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2744076729/5000000000 : ℝ)^65 ≤ (22558537666187/50000000000000 : ℝ)^49 := by
    have hnat : (2744076729 : ℕ)^65*50000000000000^49 ≤ 22558537666187^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744076729 5000000000 22558537666187 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660274621/2000000000 : ℝ)^65 ≤ (22989719102319/100000000000000 : ℝ)^49 := by
    have hnat : (660274621 : ℕ)^65*100000000000000^49 ≤ 22989719102319^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660274621 2000000000 22989719102319 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66021411/156250000 : ℝ), (2744076729/5000000000 : ℝ), (-660274621/2000000000 : ℝ)] ![(127572822211/400000000000 : ℝ), (22558537666187/50000000000000 : ℝ), (22989719102319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66021411/156250000 : ℝ)|^65 ≤ (127572822211/400000000000 : ℝ)^49
        have hw : |(66021411/156250000 : ℝ)|=(66021411/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2744076729/5000000000 : ℝ)|^65 ≤ (22558537666187/50000000000000 : ℝ)^49
        have hw : |(2744076729/5000000000 : ℝ)|=(2744076729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-660274621/2000000000 : ℝ)|^65 ≤ (22989719102319/100000000000000 : ℝ)^49
        have hw : |(-660274621/2000000000 : ℝ)|=(660274621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301022 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]]) : False := by
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
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1876107154580011/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_2 : ((256902019/1000000000 : ℝ)*X 2 0+(1132102107/2000000000 : ℝ)*X 2 1+(4678773257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301022_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2827942441/10000000000 : ℝ)*X 0 0+(3774558671/10000000000 : ℝ)*X 0 1+(-6268436247/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301022_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((7403947107/10000000000 : ℝ)*X 1 0+(-292831567/10000000000 : ℝ)*X 1 1+(-4231785717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301022_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1697392551/10000000000 : ℝ)*X 2 0+(1767763199/2500000000 : ℝ)*X 2 1+(470306469/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301022_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((2889712943/10000000000 : ℝ)*X 0 0+(3885191041/5000000000 : ℝ)*X 0 1+(-51613711/312500000 : ℝ)*X 0 2+(2889712943/10000000000 : ℝ)*X 1 0+(3885191041/5000000000 : ℝ)*X 1 1+(-51613711/312500000 : ℝ)*X 1 2+(2889712943/10000000000 : ℝ)*X 2 0+(3885191041/5000000000 : ℝ)*X 2 1+(-51613711/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301022_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-3124311487/10000000000 : ℝ)*X 0 0+(1049828043/2500000000 : ℝ)*X 0 1+(-5659839917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301022_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((439982991/500000000 : ℝ)*X 1 0+(-162563681/1250000000 : ℝ)*X 1 1+(-1617225599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301022_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((1920535889/10000000000 : ℝ)*X 2 0+(2879162113/5000000000 : ℝ)*X 2 1+(5078730507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301022_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((494121733/2000000000 : ℝ)*X 0 0+(5044154541/10000000000 : ℝ)*X 0 1+(-215448843/400000000 : ℝ)*X 0 2+(494121733/2000000000 : ℝ)*X 1 0+(5044154541/10000000000 : ℝ)*X 1 1+(-215448843/400000000 : ℝ)*X 1 2+(494121733/2000000000 : ℝ)*X 2 0+(5044154541/10000000000 : ℝ)*X 2 1+(-215448843/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301022_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-2037846891/10000000000 : ℝ)*X 0 0+(434813/781250 : ℝ)*X 0 1+(-5191765719/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301022_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2136863093/2500000000 : ℝ)*X 1 0+(-570369737/10000000000 : ℝ)*X 1 1+(-515537901/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301022_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((928601539/5000000000 : ℝ)*X 2 0+(1206697749/2000000000 : ℝ)*X 2 1+(151054253/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301022_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((-2897/5000000000 : ℝ)*X 0 0+(9999999919/10000000000 : ℝ)*X 0 1+(-2897/5000000000 : ℝ)*X 0 2+(-2897/5000000000 : ℝ)*X 2 0+(9999999919/10000000000 : ℝ)*X 2 1+(-2897/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301022_s0_25 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((5216408173/10000000000 : ℝ)*X 0 0+(5751146991/10000000000 : ℝ)*X 0 1+(-1737943533/10000000000 : ℝ)*X 0 2+(5216408173/10000000000 : ℝ)*X 1 0+(5751146991/10000000000 : ℝ)*X 1 1+(-1737943533/10000000000 : ℝ)*X 1 2+(5216408173/10000000000 : ℝ)*X 2 0+(5751146991/10000000000 : ℝ)*X 2 1+(-1737943533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301022_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((41121/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41121/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (21768251855691365087157/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5141123/1000000000000 : ℝ)*(base18) + (92378496701/125000000000 : ℝ)*(base39) + (101520958977/125000000000 : ℝ)*(base50) + (7348243279/20000000000 : ℝ)*(base60) + (1825645732113/500000000000 : ℝ)*(major_s0_0) + (4765572515497/1000000000000 : ℝ)*(major_s0_1) + (1825645732113/500000000000 : ℝ)*(major_s0_2) + (1208553186519/250000000000 : ℝ)*(sp_s0_7) + (2417109987291/500000000000 : ℝ)*(sp_s0_8) + (966844195723/200000000000 : ℝ)*(sp_s0_9) + (308544545191/125000000000 : ℝ)*(sp_s0_13) + (12369629/1000000000000 : ℝ)*(sp_s0_21) + (413709/100000000000 : ℝ)*(sp_s0_23) + (1114281051271/1000000000000 : ℝ)*(sp_s0_25) + (308544545191/125000000000 : ℝ)*(f.failure) + (966845023141/200000000000 : ℝ)*(f.sum) + (419867337743981/10000000000000000000000000000 : ℝ)*base62 + (1149602032121341/5000000000000000000000000000 : ℝ)*base64 + (1697849272934571/10000000000000000000000000000 : ℝ)*base66 + (269202458406757/5000000000000000000000000000 : ℝ)*base68 + (494797541014049/2500000000000000000000000000 : ℝ)*base70 + (1306706613378659/5000000000000000000000000000 : ℝ)*base73 + (1466901561069533/10000000000000000000000000000 : ℝ)*base75 + (1600655836906757/5000000000000000000000000000 : ℝ)*base76 + (1092863539177253/10000000000000000000000000000 : ℝ)*base78 + (2121/3125000000000000 : ℝ)*base87 + (2121/3125000000000000 : ℝ)*base89 + (2121/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(22229/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(22229/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3297408612874968014679/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2878329/1000000000000 : ℝ)*(base3) + (78146239839/100000000000 : ℝ)*(base39) + (1609151509/50000000000 : ℝ)*(base50) + (23829240227/62500000000 : ℝ)*(base60) + (1319602477141/500000000000 : ℝ)*(major_s0_0) + (1319602477141/500000000000 : ℝ)*(major_s0_1) + (1319602477141/500000000000 : ℝ)*(major_s0_2) + (164137/62500000000 : ℝ)*(sp_s0_2) + (3047057/1000000000000 : ℝ)*(sp_s0_7) + (698848639953/200000000000 : ℝ)*(sp_s0_14) + (3494228228831/1000000000000 : ℝ)*(sp_s0_15) + (349424362063/100000000000 : ℝ)*(sp_s0_16) + (1784159904101/1000000000000 : ℝ)*(sp_s0_20) + (65301/3125000000 : ℝ)*(sp_s0_22) + (178416278243/100000000000 : ℝ)*(f.failure) + (1747123123411/500000000000 : ℝ)*(f.sum) + (1736011527/10000000000000000000000 : ℝ)*base63 + (1098085235711663/5000000000000000000000000000 : ℝ)*base65 + (1554820390211663/5000000000000000000000000000 : ℝ)*base66 + (52530770528551/5000000000000000000000000000 : ℝ)*base69 + (510948148120107/2500000000000000000000000000 : ℝ)*base71 + (1171220558288337/5000000000000000000000000000 : ℝ)*base72 + (771360059471449/5000000000000000000000000000 : ℝ)*base75 + (1561025212528551/5000000000000000000000000000 : ℝ)*base77 + (1827778179/10000000000000000000000 : ℝ)*base78 + (617/2500000000000000 : ℝ)*base86 + (617/2500000000000000 : ℝ)*base88 + (617/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-9011/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-9011/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (577906888441458660927/78125000000000000000000000 : ℝ) := by norm_num
    linear_combination (520113243581/500000000000 : ℝ)*(base39) + (360403194111/500000000000 : ℝ)*(base50) + (3370491179777/1000000000000 : ℝ)*(major_s0_0) + (210655900627/62500000000 : ℝ)*(major_s0_1) + (3370491179777/1000000000000 : ℝ)*(major_s0_2) + (60534891/1000000000000 : ℝ)*(sp_s0_2) + (1025479/50000000000 : ℝ)*(sp_s0_9) + (410319/62500000000 : ℝ)*(sp_s0_13) + (22930707/1000000000000 : ℝ)*(sp_s0_15) + (4462450933147/1000000000000 : ℝ)*(sp_s0_21) + (4462428002441/1000000000000 : ℝ)*(sp_s0_22) + (1115592472169/250000000000 : ℝ)*(sp_s0_23) + (646051/200000000000 : ℝ)*(sp_s0_25) + (2278522395563/1000000000000 : ℝ)*(sp_s0_27) + (2278528960667/1000000000000 : ℝ)*(f.failure) + (4462450933147/1000000000000 : ℝ)*(f.sum) + (697839624513439/2000000000000000000000000000 : ℝ)*base63 + (409170796133389/10000000000000000000000000000 : ℝ)*base64 + (171671393248161/625000000000000000000000000 : ℝ)*base66 + (10500625931362453/10000000000000000000000000000 : ℝ)*base68 + (753825716752079/5000000000000000000000000000 : ℝ)*base71 + (4196491294866611/10000000000000000000000000000 : ℝ)*base73 + (143467825995603/625000000000000000000000000 : ℝ)*base75 + (827146459362453/10000000000000000000000000000 : ℝ)*base76 + (584637243620793/2000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1327/25000000000000000 : ℝ)*base87 + (1327/25000000000000000 : ℝ)*base89 + (1327/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (41121/100000 : ℝ) ^ (129/32 : ℝ) ≤ (695239067289165997/25000000000000000000 : ℝ) := by
    have hpowers : (41121/100000 : ℝ)^129 ≤ (695239067289165997/25000000000000000000 : ℝ)^32 := by
      have hnat : (41121 : ℕ)^129*25000000000000000000^32 ≤ 695239067289165997^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41121 100000 695239067289165997 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (41121/100000 : ℝ)) (X := (695239067289165997/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (25695239067289165997/25000000000000000000 : ℝ) ≤ (78658399853657/78125000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (25695239067289165997/25000000000000000000 : ℝ)^32 ≤ (78658399853657/78125000000000 : ℝ)^129 := by
      have hnat : (25695239067289165997 : ℕ)^32*78125000000000^129 ≤ 78658399853657^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25695239067289165997 25000000000000000000 78658399853657 78125000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78658399853657/78125000000000 : ℝ)) (X := (25695239067289165997/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (13195239067289165997/12500000000000000000 : ℝ) ≤ (10135175091945809/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (13195239067289165997/12500000000000000000 : ℝ)^32 ≤ (10135175091945809/10000000000000000 : ℝ)^129 := by
      have hnat : (13195239067289165997 : ℕ)^32*10000000000000000^129 ≤ 10135175091945809^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13195239067289165997 12500000000000000000 10135175091945809 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10135175091945809/10000000000000000 : ℝ)) (X := (13195239067289165997/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(177799951219/10708593750000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(66899910677713/4112100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (41121/100000 : ℝ)) (alpha := (177799951219/10708593750000 : ℝ)) (beta := (66899910677713/4112100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (41121/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(177799951219/10708593750000 : ℝ)*((1 : ℝ)*pair X 0 1)+(66899910677713/4112100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (22229/100000 : ℝ) ^ (129/32 : ℝ) ≤ (58238604469382961/25000000000000000000 : ℝ) := by
    have hpowers : (22229/100000 : ℝ)^129 ≤ (58238604469382961/25000000000000000000 : ℝ)^32 := by
      have hnat : (22229 : ℕ)^129*25000000000000000000^32 ≤ 58238604469382961^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22229 100000 58238604469382961 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22229/100000 : ℝ)) (X := (58238604469382961/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (25058238604469382961/25000000000000000000 : ℝ) ≤ (10005773659908057/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (25058238604469382961/25000000000000000000 : ℝ)^32 ≤ (10005773659908057/10000000000000000 : ℝ)^129 := by
      have hnat : (25058238604469382961 : ℕ)^32*10000000000000000^129 ≤ 10005773659908057^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25058238604469382961 25000000000000000000 10005773659908057 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005773659908057/10000000000000000 : ℝ)) (X := (25058238604469382961/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (12558238604469382961/12500000000000000000 : ℝ) ≤ (10011537238557683/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (12558238604469382961/12500000000000000000 : ℝ)^32 ≤ (10011537238557683/10000000000000000 : ℝ)^129 := by
      have hnat : (12558238604469382961 : ℕ)^32*10000000000000000^129 ≤ 10011537238557683^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12558238604469382961 12500000000000000000 10011537238557683 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011537238557683/10000000000000000 : ℝ)) (X := (12558238604469382961/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(5773659908057/2222900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(2881789324813/1111450000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (22229/100000 : ℝ)) (alpha := (5773659908057/2222900000000000 : ℝ)) (beta := (2881789324813/1111450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (22229/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(5773659908057/2222900000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(2881789324813/1111450000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (9011/25000 : ℝ) ^ (129/32 : ℝ) ≤ (1634868984221582643/100000000000000000000 : ℝ) := by
    have hpowers : (9011/25000 : ℝ)^129 ≤ (1634868984221582643/100000000000000000000 : ℝ)^32 := by
      have hnat : (9011 : ℕ)^129*100000000000000000000^32 ≤ 1634868984221582643^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9011 25000 1634868984221582643 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9011/25000 : ℝ)) (X := (1634868984221582643/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (101634868984221582643/100000000000000000000 : ℝ) ≤ (5020153984142289/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (101634868984221582643/100000000000000000000 : ℝ)^32 ≤ (5020153984142289/5000000000000000 : ℝ)^129 := by
      have hnat : (101634868984221582643 : ℕ)^32*5000000000000000^129 ≤ 5020153984142289^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101634868984221582643 100000000000000000000 5020153984142289 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5020153984142289/5000000000000000 : ℝ)) (X := (101634868984221582643/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (51634868984221582643/50000000000000000000 : ℝ) ≤ (10080131301401999/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (51634868984221582643/50000000000000000000 : ℝ)^32 ≤ (10080131301401999/10000000000000000 : ℝ)^129 := by
      have hnat : (51634868984221582643 : ℕ)^32*10000000000000000^129 ≤ 10080131301401999^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51634868984221582643 50000000000000000000 10080131301401999 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10080131301401999/10000000000000000 : ℝ)) (X := (51634868984221582643/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(20153984142289/1802200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(39823333117421/3604400000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (9011/25000 : ℝ)) (alpha := (20153984142289/1802200000000000 : ℝ)) (beta := (39823333117421/3604400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (9011/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(20153984142289/1802200000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(39823333117421/3604400000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-14618339/39062500 : ℝ)*X 0 0+(118137723/250000000 : ℝ)*X 0 1+(-4615358201/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301022_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5701526761/10000000000 : ℝ)*X 1 0+(-2783344539/10000000000 : ℝ)*X 1 1+(-1113681509/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301022_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3646369541/10000000000 : ℝ)*X 2 0+(4929502971/10000000000 : ℝ)*X 2 1+(1124263489/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301022_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((66021411/156250000 : ℝ)*X 0 0+(2744076729/5000000000 : ℝ)*X 0 1+(-660274621/2000000000 : ℝ)*X 0 2+(66021411/156250000 : ℝ)*X 1 0+(2744076729/5000000000 : ℝ)*X 1 1+(-660274621/2000000000 : ℝ)*X 1 2+(66021411/156250000 : ℝ)*X 2 0+(2744076729/5000000000 : ℝ)*X 2 1+(-660274621/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301022_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-73443/12500 : ℝ) < ((-36981/25000 : ℝ)*P 0+(-36981/25000 : ℝ)*P 1+(-36981/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-73443/12500 : ℝ) < (-17729958307301716458924836899609493/3050653054370000000000000000000000 : ℝ) := by norm_num
    linear_combination (268967/500000000000 : ℝ)*(base1) + (52077/500000000000 : ℝ)*(base5) + (33811/125000000000 : ℝ)*(base16) + (1153061/1000000000000 : ℝ)*(base18) + (52405785973/200000000000 : ℝ)*(base39) + (1095547623/12500000000 : ℝ)*(base49) + (173227593523/500000000000 : ℝ)*(base50) + (31302166521/1000000000000 : ℝ)*(base60) + (36981/25000 : ℝ)*(major_s1_0) + (36981/25000 : ℝ)*(major_s1_1) + (36981/25000 : ℝ)*(major_s1_2) + (387457219037/200000000000 : ℝ)*(sp_s1_0) + (968642066851/500000000000 : ℝ)*(sp_s1_1) + (968642830703/500000000000 : ℝ)*(sp_s1_2) + (124999919739/125000000000 : ℝ)*(sp_s1_6) + (484321389313/250000000000 : ℝ)*(f.sum) + (5927027801875641/15648868671875000000000000000 : ℝ)*base63 + (3183548396607/11263750000000000000000000 : ℝ)*base64 + (30170724394319/44458000000000000000000000 : ℝ)*base66 + (5956985808083/9011000000000000000000000 : ℝ)*base69 + (36193060865685727/68618765000000000000000000000 : ℝ)*base70 + (872285470987/2855625000000000000000000 : ℝ)*base72 + (7322505918137/111145000000000000000000000 : ℝ)*base75 + (793290906103/7615000000000000000000000 : ℝ)*base76 + (9764047288585693/31738844062500000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c301024_s0_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-620228431/1250000000 : ℝ)*x 0 + (1545196007/5000000000 : ℝ)*x 1 + (-1240457039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (620228431/1250000000 : ℝ)^65 ≤ (39469292464921/100000000000000 : ℝ)^49 := by
    have hnat : (620228431 : ℕ)^65*100000000000000^49 ≤ 39469292464921^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620228431 1250000000 39469292464921 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1545196007/5000000000 : ℝ)^65 ≤ (526535189379/2500000000000 : ℝ)^49 := by
    have hnat : (1545196007 : ℕ)^65*2500000000000^49 ≤ 526535189379^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545196007 5000000000 526535189379 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1240457039/2500000000 : ℝ)^65 ≤ (1973464996787/5000000000000 : ℝ)^49 := by
    have hnat : (1240457039 : ℕ)^65*5000000000000^49 ≤ 1973464996787^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1240457039 2500000000 1973464996787 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-620228431/1250000000 : ℝ), (1545196007/5000000000 : ℝ), (-1240457039/2500000000 : ℝ)] ![(39469292464921/100000000000000 : ℝ), (526535189379/2500000000000 : ℝ), (1973464996787/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-620228431/1250000000 : ℝ)|^65 ≤ (39469292464921/100000000000000 : ℝ)^49
        have hw : |(-620228431/1250000000 : ℝ)|=(620228431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1545196007/5000000000 : ℝ)|^65 ≤ (526535189379/2500000000000 : ℝ)^49
        have hw : |(1545196007/5000000000 : ℝ)|=(1545196007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1240457039/2500000000 : ℝ)|^65 ≤ (1973464996787/5000000000000 : ℝ)^49
        have hw : |(-1240457039/2500000000 : ℝ)|=(1240457039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301024_s0_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (620228431/1250000000 : ℝ)*x 0 + (-1545196007/5000000000 : ℝ)*x 1 + (-1240457039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (620228431/1250000000 : ℝ)^65 ≤ (39469292464921/100000000000000 : ℝ)^49 := by
    have hnat : (620228431 : ℕ)^65*100000000000000^49 ≤ 39469292464921^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620228431 1250000000 39469292464921 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1545196007/5000000000 : ℝ)^65 ≤ (526535189379/2500000000000 : ℝ)^49 := by
    have hnat : (1545196007 : ℕ)^65*2500000000000^49 ≤ 526535189379^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545196007 5000000000 526535189379 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1240457039/2500000000 : ℝ)^65 ≤ (1973464996787/5000000000000 : ℝ)^49 := by
    have hnat : (1240457039 : ℕ)^65*5000000000000^49 ≤ 1973464996787^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1240457039 2500000000 1973464996787 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(620228431/1250000000 : ℝ), (-1545196007/5000000000 : ℝ), (-1240457039/2500000000 : ℝ)] ![(39469292464921/100000000000000 : ℝ), (526535189379/2500000000000 : ℝ), (1973464996787/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(620228431/1250000000 : ℝ)|^65 ≤ (39469292464921/100000000000000 : ℝ)^49
        have hw : |(620228431/1250000000 : ℝ)|=(620228431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1545196007/5000000000 : ℝ)|^65 ≤ (526535189379/2500000000000 : ℝ)^49
        have hw : |(-1545196007/5000000000 : ℝ)|=(1545196007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1240457039/2500000000 : ℝ)|^65 ≤ (1973464996787/5000000000000 : ℝ)^49
        have hw : |(-1240457039/2500000000 : ℝ)|=(1240457039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301024_s0_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (174752669/500000000 : ℝ)*x 0 + (596668887/1000000000 : ℝ)*x 1 + (3495053879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174752669/500000000 : ℝ)^65 ≤ (2479576474261/10000000000000 : ℝ)^49 := by
    have hnat : (174752669 : ℕ)^65*10000000000000^49 ≤ 2479576474261^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174752669 500000000 2479576474261 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (596668887/1000000000 : ℝ)^65 ≤ (12602116448291/25000000000000 : ℝ)^49 := by
    have hnat : (596668887 : ℕ)^65*25000000000000^49 ≤ 12602116448291^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596668887 1000000000 12602116448291 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3495053879/10000000000 : ℝ)^65 ≤ (4959153887751/20000000000000 : ℝ)^49 := by
    have hnat : (3495053879 : ℕ)^65*20000000000000^49 ≤ 4959153887751^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3495053879 10000000000 4959153887751 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174752669/500000000 : ℝ), (596668887/1000000000 : ℝ), (3495053879/10000000000 : ℝ)] ![(2479576474261/10000000000000 : ℝ), (12602116448291/25000000000000 : ℝ), (4959153887751/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174752669/500000000 : ℝ)|^65 ≤ (2479576474261/10000000000000 : ℝ)^49
        have hw : |(174752669/500000000 : ℝ)|=(174752669/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(596668887/1000000000 : ℝ)|^65 ≤ (12602116448291/25000000000000 : ℝ)^49
        have hw : |(596668887/1000000000 : ℝ)|=(596668887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3495053879/10000000000 : ℝ)|^65 ≤ (4959153887751/20000000000000 : ℝ)^49
        have hw : |(3495053879/10000000000 : ℝ)|=(3495053879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301024_s0_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (174752669/500000000 : ℝ)*x 0 + (596668887/1000000000 : ℝ)*x 1 + (-3495053879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174752669/500000000 : ℝ)^65 ≤ (2479576474261/10000000000000 : ℝ)^49 := by
    have hnat : (174752669 : ℕ)^65*10000000000000^49 ≤ 2479576474261^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174752669 500000000 2479576474261 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (596668887/1000000000 : ℝ)^65 ≤ (12602116448291/25000000000000 : ℝ)^49 := by
    have hnat : (596668887 : ℕ)^65*25000000000000^49 ≤ 12602116448291^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596668887 1000000000 12602116448291 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3495053879/10000000000 : ℝ)^65 ≤ (4959153887751/20000000000000 : ℝ)^49 := by
    have hnat : (3495053879 : ℕ)^65*20000000000000^49 ≤ 4959153887751^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3495053879 10000000000 4959153887751 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174752669/500000000 : ℝ), (596668887/1000000000 : ℝ), (-3495053879/10000000000 : ℝ)] ![(2479576474261/10000000000000 : ℝ), (12602116448291/25000000000000 : ℝ), (4959153887751/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174752669/500000000 : ℝ)|^65 ≤ (2479576474261/10000000000000 : ℝ)^49
        have hw : |(174752669/500000000 : ℝ)|=(174752669/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(596668887/1000000000 : ℝ)|^65 ≤ (12602116448291/25000000000000 : ℝ)^49
        have hw : |(596668887/1000000000 : ℝ)|=(596668887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3495053879/10000000000 : ℝ)|^65 ≤ (4959153887751/20000000000000 : ℝ)^49
        have hw : |(-3495053879/10000000000 : ℝ)|=(3495053879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301024 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]]) : False := by
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
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1256642335510643/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (1 : ℝ)) (alpha := (1876107154580011/10000000000000000 : ℝ)) (beta := (1256642335510643/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1876107154580011/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1256642335510643/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-620228431/1250000000 : ℝ)*X 0 0+(1545196007/5000000000 : ℝ)*X 0 1+(-1240457039/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301024_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((620228431/1250000000 : ℝ)*X 1 0+(-1545196007/5000000000 : ℝ)*X 1 1+(-1240457039/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301024_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((174752669/500000000 : ℝ)*X 2 0+(596668887/1000000000 : ℝ)*X 2 1+(3495053879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301024_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((174752669/500000000 : ℝ)*X 0 0+(596668887/1000000000 : ℝ)*X 0 1+(-3495053879/10000000000 : ℝ)*X 0 2+(174752669/500000000 : ℝ)*X 1 0+(596668887/1000000000 : ℝ)*X 1 1+(-3495053879/10000000000 : ℝ)*X 1 2+(174752669/500000000 : ℝ)*X 2 0+(596668887/1000000000 : ℝ)*X 2 1+(-3495053879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301024_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-73443/12500 : ℝ) < ((-36981/25000 : ℝ)*P 0+(-36981/25000 : ℝ)*P 1+(-36981/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-73443/12500 : ℝ) < (-911382002522377714221527343/156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (515038769/1600000000 : ℝ)*(base5) + (42223/100000000000 : ℝ)*(base8) + (111183/250000000000 : ℝ)*(base11) + (22908385601/250000000000 : ℝ)*(base39) + (28661/250000000000 : ℝ)*(base44) + (132155289643/500000000000 : ℝ)*(base49) + (43169162297/250000000000 : ℝ)*(base50) + (71972837539/250000000000 : ℝ)*(base59) + (36981/25000 : ℝ)*(major_s0_0) + (369809971339/250000000000 : ℝ)*(major_s0_1) + (36981/25000 : ℝ)*(major_s0_2) + (388856147683/200000000000 : ℝ)*(sp_s0_0) + (1944281490733/1000000000000 : ℝ)*(sp_s0_1) + (1133090418001/500000000000 : ℝ)*(sp_s0_2) + (169525163683/250000000000 : ℝ)*(sp_s0_6) + (1944281605377/1000000000000 : ℝ)*(f.sum) + (1630776787695271/2500000000000000000000000000 : ℝ)*base63 + (163980197/1000000000000000000000 : ℝ)*base64 + (948439301460977/2500000000000000000000000000 : ℝ)*base67 + (13059213/312500000000000000000 : ℝ)*base69 + (156446871/5000000000000000000000 : ℝ)*base71 + (366541887/1250000000000000000000 : ℝ)*base73 + (546944277695271/2500000000000000000000000000 : ℝ)*base75 + (431522947/500000000000000000000 : ℝ)*base76 + (1071636006960977/2500000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p001_b012 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 22 ≤ c.val) (hhi : c.val < 25)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=22 ∨ c=23 ∨ c=24 := by omega
  rcases hc with rfl|rfl|rfl
  · exact collision_c301022 p hpa (by linarith only [hpb]) X hX
  · exact collision_c301023 p hpa (by linarith only [hpb]) X hX
  · exact collision_c301024 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (c : Fin 88) (hlo : 22 ≤ c.val) (hhi : c.val < 25)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p001_b012 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

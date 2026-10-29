-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c315053_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:55:13.499547+00:00
-- url     : https://prove2.me/submissions/4d704581-a0ad-4c00-8c70-274ecd434abc

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
theorem collision_support_c315053_s1_s1_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-14284883/80000000 : ℝ)*x 0 + (1036034529/2000000000 : ℝ)*x 1 + (2673710351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14284883/80000000 : ℝ)^19 ≤ (2819701678491/25000000000000 : ℝ)^15 := by
    have hnat : (14284883 : ℕ)^19*25000000000000^15 ≤ 2819701678491^15*80000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14284883 80000000 2819701678491 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036034529/2000000000 : ℝ)^19 ≤ (21733985231593/50000000000000 : ℝ)^15 := by
    have hnat : (1036034529 : ℕ)^19*50000000000000^15 ≤ 21733985231593^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036034529 2000000000 21733985231593 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2673710351/5000000000 : ℝ)^19 ≤ (5656652850753/12500000000000 : ℝ)^15 := by
    have hnat : (2673710351 : ℕ)^19*12500000000000^15 ≤ 5656652850753^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673710351 5000000000 5656652850753 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14284883/80000000 : ℝ), (1036034529/2000000000 : ℝ), (2673710351/5000000000 : ℝ)] ![(2819701678491/25000000000000 : ℝ), (21733985231593/50000000000000 : ℝ), (5656652850753/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14284883/80000000 : ℝ)|^19 ≤ (2819701678491/25000000000000 : ℝ)^15
        have hw : |(-14284883/80000000 : ℝ)|=(14284883/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036034529/2000000000 : ℝ)|^19 ≤ (21733985231593/50000000000000 : ℝ)^15
        have hw : |(1036034529/2000000000 : ℝ)|=(1036034529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2673710351/5000000000 : ℝ)|^19 ≤ (5656652850753/12500000000000 : ℝ)^15
        have hw : |(2673710351/5000000000 : ℝ)|=(2673710351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s1_s1_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2256909151/5000000000 : ℝ)*x 0 + (-17585673/156250000 : ℝ)*x 1 + (1608533743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2256909151/5000000000 : ℝ)^19 ≤ (36510896141777/100000000000000 : ℝ)^15 := by
    have hnat : (2256909151 : ℕ)^19*100000000000000^15 ≤ 36510896141777^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256909151 5000000000 36510896141777 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17585673/156250000 : ℝ)^19 ≤ (6285830876599/100000000000000 : ℝ)^15 := by
    have hnat : (17585673 : ℕ)^19*100000000000000^15 ≤ 6285830876599^15*156250000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17585673 156250000 6285830876599 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1608533743/2500000000 : ℝ)^19 ≤ (3575204560477/6250000000000 : ℝ)^15 := by
    have hnat : (1608533743 : ℕ)^19*6250000000000^15 ≤ 3575204560477^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1608533743 2500000000 3575204560477 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2256909151/5000000000 : ℝ), (-17585673/156250000 : ℝ), (1608533743/2500000000 : ℝ)] ![(36510896141777/100000000000000 : ℝ), (6285830876599/100000000000000 : ℝ), (3575204560477/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2256909151/5000000000 : ℝ)|^19 ≤ (36510896141777/100000000000000 : ℝ)^15
        have hw : |(2256909151/5000000000 : ℝ)|=(2256909151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17585673/156250000 : ℝ)|^19 ≤ (6285830876599/100000000000000 : ℝ)^15
        have hw : |(-17585673/156250000 : ℝ)|=(17585673/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1608533743/2500000000 : ℝ)|^19 ≤ (3575204560477/6250000000000 : ℝ)^15
        have hw : |(1608533743/2500000000 : ℝ)|=(1608533743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s1_s1_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4539577459/10000000000 : ℝ)*x 0 + (6450689587/10000000000 : ℝ)*x 1 + (-1061291137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4539577459/10000000000 : ℝ)^19 ≤ (1149219273197/3125000000000 : ℝ)^15 := by
    have hnat : (4539577459 : ℕ)^19*3125000000000^15 ≤ 1149219273197^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539577459 10000000000 1149219273197 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6450689587/10000000000 : ℝ)^19 ≤ (28694882655761/50000000000000 : ℝ)^15 := by
    have hnat : (6450689587 : ℕ)^19*50000000000000^15 ≤ 28694882655761^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6450689587 10000000000 28694882655761 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061291137/10000000000 : ℝ)^19 ≤ (2917608966697/50000000000000 : ℝ)^15 := by
    have hnat : (1061291137 : ℕ)^19*50000000000000^15 ≤ 2917608966697^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061291137 10000000000 2917608966697 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4539577459/10000000000 : ℝ), (6450689587/10000000000 : ℝ), (-1061291137/10000000000 : ℝ)] ![(1149219273197/3125000000000 : ℝ), (28694882655761/50000000000000 : ℝ), (2917608966697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4539577459/10000000000 : ℝ)|^19 ≤ (1149219273197/3125000000000 : ℝ)^15
        have hw : |(4539577459/10000000000 : ℝ)|=(4539577459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6450689587/10000000000 : ℝ)|^19 ≤ (28694882655761/50000000000000 : ℝ)^15
        have hw : |(6450689587/10000000000 : ℝ)|=(6450689587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1061291137/10000000000 : ℝ)|^19 ≤ (2917608966697/50000000000000 : ℝ)^15
        have hw : |(-1061291137/10000000000 : ℝ)|=(1061291137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s1_s1_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3677342393/5000000000 : ℝ)*x 0 + (2476496117/10000000000 : ℝ)*x 1 + (1128202689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3677342393/5000000000 : ℝ)^19 ≤ (67761209266441/100000000000000 : ℝ)^15 := by
    have hnat : (3677342393 : ℕ)^19*100000000000000^15 ≤ 67761209266441^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3677342393 5000000000 67761209266441 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2476496117/10000000000 : ℝ)^19 ≤ (682738430961/4000000000000 : ℝ)^15 := by
    have hnat : (2476496117 : ℕ)^19*4000000000000^15 ≤ 682738430961^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2476496117 10000000000 682738430961 4000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1128202689/5000000000 : ℝ)^19 ≤ (23703640537/156250000000 : ℝ)^15 := by
    have hnat : (1128202689 : ℕ)^19*156250000000^15 ≤ 23703640537^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128202689 5000000000 23703640537 156250000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3677342393/5000000000 : ℝ), (2476496117/10000000000 : ℝ), (1128202689/5000000000 : ℝ)] ![(67761209266441/100000000000000 : ℝ), (682738430961/4000000000000 : ℝ), (23703640537/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3677342393/5000000000 : ℝ)|^19 ≤ (67761209266441/100000000000000 : ℝ)^15
        have hw : |(3677342393/5000000000 : ℝ)|=(3677342393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2476496117/10000000000 : ℝ)|^19 ≤ (682738430961/4000000000000 : ℝ)^15
        have hw : |(2476496117/10000000000 : ℝ)|=(2476496117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1128202689/5000000000 : ℝ)|^19 ≤ (23703640537/156250000000 : ℝ)^15
        have hw : |(1128202689/5000000000 : ℝ)|=(1128202689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s1_s1_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-44032257/250000000 : ℝ)*x 0 + (795344683/2000000000 : ℝ)*x 1 + (6488611149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44032257/250000000 : ℝ)^19 ≤ (5542289316811/50000000000000 : ℝ)^15 := by
    have hnat : (44032257 : ℕ)^19*50000000000000^15 ≤ 5542289316811^15*250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44032257 250000000 5542289316811 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (795344683/2000000000 : ℝ)^19 ≤ (15548989148947/50000000000000 : ℝ)^15 := by
    have hnat : (795344683 : ℕ)^19*50000000000000^15 ≤ 15548989148947^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      795344683 2000000000 15548989148947 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6488611149/10000000000 : ℝ)^19 ≤ (2890872152967/5000000000000 : ℝ)^15 := by
    have hnat : (6488611149 : ℕ)^19*5000000000000^15 ≤ 2890872152967^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6488611149 10000000000 2890872152967 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-44032257/250000000 : ℝ), (795344683/2000000000 : ℝ), (6488611149/10000000000 : ℝ)] ![(5542289316811/50000000000000 : ℝ), (15548989148947/50000000000000 : ℝ), (2890872152967/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-44032257/250000000 : ℝ)|^19 ≤ (5542289316811/50000000000000 : ℝ)^15
        have hw : |(-44032257/250000000 : ℝ)|=(44032257/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(795344683/2000000000 : ℝ)|^19 ≤ (15548989148947/50000000000000 : ℝ)^15
        have hw : |(795344683/2000000000 : ℝ)|=(795344683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6488611149/10000000000 : ℝ)|^19 ≤ (2890872152967/5000000000000 : ℝ)^15
        have hw : |(6488611149/10000000000 : ℝ)|=(6488611149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s1_s1_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (464486643/1250000000 : ℝ)*x 0 + (-56634601/1000000000 : ℝ)*x 1 + (930753237/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (464486643/1250000000 : ℝ)^19 ≤ (14268667315637/50000000000000 : ℝ)^15 := by
    have hnat : (464486643 : ℕ)^19*50000000000000^15 ≤ 14268667315637^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464486643 1250000000 14268667315637 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56634601/1000000000 : ℝ)^19 ≤ (329215557557/12500000000000 : ℝ)^15 := by
    have hnat : (56634601 : ℕ)^19*12500000000000^15 ≤ 329215557557^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56634601 1000000000 329215557557 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (930753237/1250000000 : ℝ)^19 ≤ (68828940894297/100000000000000 : ℝ)^15 := by
    have hnat : (930753237 : ℕ)^19*100000000000000^15 ≤ 68828940894297^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930753237 1250000000 68828940894297 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(464486643/1250000000 : ℝ), (-56634601/1000000000 : ℝ), (930753237/1250000000 : ℝ)] ![(14268667315637/50000000000000 : ℝ), (329215557557/12500000000000 : ℝ), (68828940894297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(464486643/1250000000 : ℝ)|^19 ≤ (14268667315637/50000000000000 : ℝ)^15
        have hw : |(464486643/1250000000 : ℝ)|=(464486643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-56634601/1000000000 : ℝ)|^19 ≤ (329215557557/12500000000000 : ℝ)^15
        have hw : |(-56634601/1000000000 : ℝ)|=(56634601/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(930753237/1250000000 : ℝ)|^19 ≤ (68828940894297/100000000000000 : ℝ)^15
        have hw : |(930753237/1250000000 : ℝ)|=(930753237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s1_s1_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3742811411/10000000000 : ℝ)*x 0 + (7584799273/10000000000 : ℝ)*x 1 + (-20848867/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3742811411/10000000000 : ℝ)^19 ≤ (14399720677887/50000000000000 : ℝ)^15 := by
    have hnat : (3742811411 : ℕ)^19*50000000000000^15 ≤ 14399720677887^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3742811411 10000000000 14399720677887 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7584799273/10000000000 : ℝ)^19 ≤ (70457816975897/100000000000000 : ℝ)^15 := by
    have hnat : (7584799273 : ℕ)^19*100000000000000^15 ≤ 70457816975897^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7584799273 10000000000 70457816975897 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20848867/1000000000 : ℝ)^19 ≤ (371370827683/50000000000000 : ℝ)^15 := by
    have hnat : (20848867 : ℕ)^19*50000000000000^15 ≤ 371370827683^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20848867 1000000000 371370827683 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3742811411/10000000000 : ℝ), (7584799273/10000000000 : ℝ), (-20848867/1000000000 : ℝ)] ![(14399720677887/50000000000000 : ℝ), (70457816975897/100000000000000 : ℝ), (371370827683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3742811411/10000000000 : ℝ)|^19 ≤ (14399720677887/50000000000000 : ℝ)^15
        have hw : |(3742811411/10000000000 : ℝ)|=(3742811411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7584799273/10000000000 : ℝ)|^19 ≤ (70457816975897/100000000000000 : ℝ)^15
        have hw : |(7584799273/10000000000 : ℝ)|=(7584799273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-20848867/1000000000 : ℝ)|^19 ≤ (371370827683/50000000000000 : ℝ)^15
        have hw : |(-20848867/1000000000 : ℝ)|=(20848867/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s1_s1_13 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6451323967/10000000000 : ℝ)*x 0 + (19181919/39062500 : ℝ)*x 1 + (226112243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6451323967/10000000000 : ℝ)^19 ≤ (11479382864039/20000000000000 : ℝ)^15 := by
    have hnat : (6451323967 : ℕ)^19*20000000000000^15 ≤ 11479382864039^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6451323967 10000000000 11479382864039 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19181919/39062500 : ℝ)^19 ≤ (40622553833343/100000000000000 : ℝ)^15 := by
    have hnat : (19181919 : ℕ)^19*100000000000000^15 ≤ 40622553833343^15*39062500^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19181919 39062500 40622553833343 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226112243/5000000000 : ℝ)^19 ≤ (247566478919/12500000000000 : ℝ)^15 := by
    have hnat : (226112243 : ℕ)^19*12500000000000^15 ≤ 247566478919^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226112243 5000000000 247566478919 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6451323967/10000000000 : ℝ), (19181919/39062500 : ℝ), (226112243/5000000000 : ℝ)] ![(11479382864039/20000000000000 : ℝ), (40622553833343/100000000000000 : ℝ), (247566478919/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6451323967/10000000000 : ℝ)|^19 ≤ (11479382864039/20000000000000 : ℝ)^15
        have hw : |(6451323967/10000000000 : ℝ)|=(6451323967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(19181919/39062500 : ℝ)|^19 ≤ (40622553833343/100000000000000 : ℝ)^15
        have hw : |(19181919/39062500 : ℝ)|=(19181919/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226112243/5000000000 : ℝ)|^19 ≤ (247566478919/12500000000000 : ℝ)^15
        have hw : |(226112243/5000000000 : ℝ)|=(226112243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s1_s1_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-994236777/10000000000 : ℝ)*x 0 + (818302327/2000000000 : ℝ)*x 1 + (3445165647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (994236777/10000000000 : ℝ)^19 ≤ (1074443968813/20000000000000 : ℝ)^15 := by
    have hnat : (994236777 : ℕ)^19*20000000000000^15 ≤ 1074443968813^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994236777 10000000000 1074443968813 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (818302327/2000000000 : ℝ)^19 ≤ (32239339424877/100000000000000 : ℝ)^15 := by
    have hnat : (818302327 : ℕ)^19*100000000000000^15 ≤ 32239339424877^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818302327 2000000000 32239339424877 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3445165647/5000000000 : ℝ)^19 ≤ (31194220358287/50000000000000 : ℝ)^15 := by
    have hnat : (3445165647 : ℕ)^19*50000000000000^15 ≤ 31194220358287^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3445165647 5000000000 31194220358287 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-994236777/10000000000 : ℝ), (818302327/2000000000 : ℝ), (3445165647/5000000000 : ℝ)] ![(1074443968813/20000000000000 : ℝ), (32239339424877/100000000000000 : ℝ), (31194220358287/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-994236777/10000000000 : ℝ)|^19 ≤ (1074443968813/20000000000000 : ℝ)^15
        have hw : |(-994236777/10000000000 : ℝ)|=(994236777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(818302327/2000000000 : ℝ)|^19 ≤ (32239339424877/100000000000000 : ℝ)^15
        have hw : |(818302327/2000000000 : ℝ)|=(818302327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3445165647/5000000000 : ℝ)|^19 ≤ (31194220358287/50000000000000 : ℝ)^15
        have hw : |(3445165647/5000000000 : ℝ)|=(3445165647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s1_s1_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (276778029/1000000000 : ℝ)*x 0 + (-528462523/5000000000 : ℝ)*x 1 + (3965041271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (276778029/1000000000 : ℝ)^19 ≤ (19650187960619/100000000000000 : ℝ)^15 := by
    have hnat : (276778029 : ℕ)^19*100000000000000^15 ≤ 19650187960619^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276778029 1000000000 19650187960619 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528462523/5000000000 : ℝ)^19 ≤ (725603417839/12500000000000 : ℝ)^15 := by
    have hnat : (528462523 : ℕ)^19*12500000000000^15 ≤ 725603417839^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528462523 5000000000 725603417839 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3965041271/5000000000 : ℝ)^19 ≤ (74544984686997/100000000000000 : ℝ)^15 := by
    have hnat : (3965041271 : ℕ)^19*100000000000000^15 ≤ 74544984686997^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3965041271 5000000000 74544984686997 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(276778029/1000000000 : ℝ), (-528462523/5000000000 : ℝ), (3965041271/5000000000 : ℝ)] ![(19650187960619/100000000000000 : ℝ), (725603417839/12500000000000 : ℝ), (74544984686997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(276778029/1000000000 : ℝ)|^19 ≤ (19650187960619/100000000000000 : ℝ)^15
        have hw : |(276778029/1000000000 : ℝ)|=(276778029/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-528462523/5000000000 : ℝ)|^19 ≤ (725603417839/12500000000000 : ℝ)^15
        have hw : |(-528462523/5000000000 : ℝ)|=(528462523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3965041271/5000000000 : ℝ)|^19 ≤ (74544984686997/100000000000000 : ℝ)^15
        have hw : |(3965041271/5000000000 : ℝ)|=(3965041271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s1_s1_16 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6184013759/10000000000 : ℝ)*x 0 + (5229746619/10000000000 : ℝ)*x 1 + (-382713721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6184013759/10000000000 : ℝ)^19 ≤ (54401294384147/100000000000000 : ℝ)^15 := by
    have hnat : (6184013759 : ℕ)^19*100000000000000^15 ≤ 54401294384147^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6184013759 10000000000 54401294384147 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229746619/10000000000 : ℝ)^19 ≤ (10998889254621/25000000000000 : ℝ)^15 := by
    have hnat : (5229746619 : ℕ)^19*25000000000000^15 ≤ 10998889254621^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229746619 10000000000 10998889254621 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (382713721/10000000000 : ℝ)^19 ≤ (801574290293/50000000000000 : ℝ)^15 := by
    have hnat : (382713721 : ℕ)^19*50000000000000^15 ≤ 801574290293^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382713721 10000000000 801574290293 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6184013759/10000000000 : ℝ), (5229746619/10000000000 : ℝ), (-382713721/10000000000 : ℝ)] ![(54401294384147/100000000000000 : ℝ), (10998889254621/25000000000000 : ℝ), (801574290293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6184013759/10000000000 : ℝ)|^19 ≤ (54401294384147/100000000000000 : ℝ)^15
        have hw : |(6184013759/10000000000 : ℝ)|=(6184013759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229746619/10000000000 : ℝ)|^19 ≤ (10998889254621/25000000000000 : ℝ)^15
        have hw : |(5229746619/10000000000 : ℝ)|=(5229746619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-382713721/10000000000 : ℝ)|^19 ≤ (801574290293/50000000000000 : ℝ)^15
        have hw : |(-382713721/10000000000 : ℝ)|=(382713721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s1_s1_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (8823279161/10000000000 : ℝ)*x 0 + (929968829/5000000000 : ℝ)*x 1 + (59228191/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8823279161/10000000000 : ℝ)^19 ≤ (10666977324039/12500000000000 : ℝ)^15 := by
    have hnat : (8823279161 : ℕ)^19*12500000000000^15 ≤ 10666977324039^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8823279161 10000000000 10666977324039 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (929968829/5000000000 : ℝ)^19 ≤ (2969189843659/25000000000000 : ℝ)^15 := by
    have hnat : (929968829 : ℕ)^19*25000000000000^15 ≤ 2969189843659^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929968829 5000000000 2969189843659 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59228191/1000000000 : ℝ)^19 ≤ (43553469051/1562500000000 : ℝ)^15 := by
    have hnat : (59228191 : ℕ)^19*1562500000000^15 ≤ 43553469051^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59228191 1000000000 43553469051 1562500000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8823279161/10000000000 : ℝ), (929968829/5000000000 : ℝ), (59228191/1000000000 : ℝ)] ![(10666977324039/12500000000000 : ℝ), (2969189843659/25000000000000 : ℝ), (43553469051/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8823279161/10000000000 : ℝ)|^19 ≤ (10666977324039/12500000000000 : ℝ)^15
        have hw : |(8823279161/10000000000 : ℝ)|=(8823279161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(929968829/5000000000 : ℝ)|^19 ≤ (2969189843659/25000000000000 : ℝ)^15
        have hw : |(929968829/5000000000 : ℝ)|=(929968829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(59228191/1000000000 : ℝ)|^19 ≤ (43553469051/1562500000000 : ℝ)^15
        have hw : |(59228191/1000000000 : ℝ)|=(59228191/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s1_s1_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-942040829/10000000000 : ℝ)*x 0 + (6483242059/10000000000 : ℝ)*x 1 + (2291718047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (942040829/10000000000 : ℝ)^19 ≤ (5017510841463/100000000000000 : ℝ)^15 := by
    have hnat : (942040829 : ℕ)^19*100000000000000^15 ≤ 5017510841463^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942040829 10000000000 5017510841463 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6483242059/10000000000 : ℝ)^19 ≤ (57756850090577/100000000000000 : ℝ)^15 := by
    have hnat : (6483242059 : ℕ)^19*100000000000000^15 ≤ 57756850090577^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6483242059 10000000000 57756850090577 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2291718047/5000000000 : ℝ)^19 ≤ (37225639041417/100000000000000 : ℝ)^15 := by
    have hnat : (2291718047 : ℕ)^19*100000000000000^15 ≤ 37225639041417^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291718047 5000000000 37225639041417 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-942040829/10000000000 : ℝ), (6483242059/10000000000 : ℝ), (2291718047/5000000000 : ℝ)] ![(5017510841463/100000000000000 : ℝ), (57756850090577/100000000000000 : ℝ), (37225639041417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-942040829/10000000000 : ℝ)|^19 ≤ (5017510841463/100000000000000 : ℝ)^15
        have hw : |(-942040829/10000000000 : ℝ)|=(942040829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6483242059/10000000000 : ℝ)|^19 ≤ (57756850090577/100000000000000 : ℝ)^15
        have hw : |(6483242059/10000000000 : ℝ)|=(6483242059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2291718047/5000000000 : ℝ)|^19 ≤ (37225639041417/100000000000000 : ℝ)^15
        have hw : |(2291718047/5000000000 : ℝ)|=(2291718047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s1_s1_22 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (773148719/1250000000 : ℝ)*x 0 + (-299607449/10000000000 : ℝ)*x 1 + (210743653/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (773148719/1250000000 : ℝ)^19 ≤ (6801799847017/12500000000000 : ℝ)^15 := by
    have hnat : (773148719 : ℕ)^19*12500000000000^15 ≤ 6801799847017^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773148719 1250000000 6801799847017 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (299607449/10000000000 : ℝ)^19 ≤ (235141868181/20000000000000 : ℝ)^15 := by
    have hnat : (299607449 : ℕ)^19*20000000000000^15 ≤ 235141868181^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299607449 10000000000 235141868181 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210743653/400000000 : ℝ)^19 ≤ (22204945936179/50000000000000 : ℝ)^15 := by
    have hnat : (210743653 : ℕ)^19*50000000000000^15 ≤ 22204945936179^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210743653 400000000 22204945936179 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(773148719/1250000000 : ℝ), (-299607449/10000000000 : ℝ), (210743653/400000000 : ℝ)] ![(6801799847017/12500000000000 : ℝ), (235141868181/20000000000000 : ℝ), (22204945936179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(773148719/1250000000 : ℝ)|^19 ≤ (6801799847017/12500000000000 : ℝ)^15
        have hw : |(773148719/1250000000 : ℝ)|=(773148719/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-299607449/10000000000 : ℝ)|^19 ≤ (235141868181/20000000000000 : ℝ)^15
        have hw : |(-299607449/10000000000 : ℝ)|=(299607449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210743653/400000000 : ℝ)|^19 ≤ (22204945936179/50000000000000 : ℝ)^15
        have hw : |(210743653/400000000 : ℝ)|=(210743653/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s1_s1_23 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (109711023/400000000 : ℝ)*x 0 + (7969435289/10000000000 : ℝ)*x 1 + (-510825569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109711023/400000000 : ℝ)^19 ≤ (1214099732871/6250000000000 : ℝ)^15 := by
    have hnat : (109711023 : ℕ)^19*6250000000000^15 ≤ 1214099732871^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109711023 400000000 1214099732871 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7969435289/10000000000 : ℝ)^19 ≤ (75013868274139/100000000000000 : ℝ)^15 := by
    have hnat : (7969435289 : ℕ)^19*100000000000000^15 ≤ 75013868274139^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7969435289 10000000000 75013868274139 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (510825569/5000000000 : ℝ)^19 ≤ (2780267994331/50000000000000 : ℝ)^15 := by
    have hnat : (510825569 : ℕ)^19*50000000000000^15 ≤ 2780267994331^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510825569 5000000000 2780267994331 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109711023/400000000 : ℝ), (7969435289/10000000000 : ℝ), (-510825569/5000000000 : ℝ)] ![(1214099732871/6250000000000 : ℝ), (75013868274139/100000000000000 : ℝ), (2780267994331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109711023/400000000 : ℝ)|^19 ≤ (1214099732871/6250000000000 : ℝ)^15
        have hw : |(109711023/400000000 : ℝ)|=(109711023/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7969435289/10000000000 : ℝ)|^19 ≤ (75013868274139/100000000000000 : ℝ)^15
        have hw : |(7969435289/10000000000 : ℝ)|=(7969435289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-510825569/5000000000 : ℝ)|^19 ≤ (2780267994331/50000000000000 : ℝ)^15
        have hw : |(-510825569/5000000000 : ℝ)|=(510825569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315053_s1_s1_27 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2242211963/2500000000 : ℝ)*x 0 + (1237735029/10000000000 : ℝ)*x 1 + (1054317247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2242211963/2500000000 : ℝ)^19 ≤ (10890381944331/12500000000000 : ℝ)^15 := by
    have hnat : (2242211963 : ℕ)^19*12500000000000^15 ≤ 10890381944331^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242211963 2500000000 10890381944331 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1237735029/10000000000 : ℝ)^19 ≤ (3545126485957/50000000000000 : ℝ)^15 := by
    have hnat : (1237735029 : ℕ)^19*50000000000000^15 ≤ 3545126485957^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237735029 10000000000 3545126485957 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054317247/10000000000 : ℝ)^19 ≤ (723336433067/12500000000000 : ℝ)^15 := by
    have hnat : (1054317247 : ℕ)^19*12500000000000^15 ≤ 723336433067^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054317247 10000000000 723336433067 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2242211963/2500000000 : ℝ), (1237735029/10000000000 : ℝ), (1054317247/10000000000 : ℝ)] ![(10890381944331/12500000000000 : ℝ), (3545126485957/50000000000000 : ℝ), (723336433067/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2242211963/2500000000 : ℝ)|^19 ≤ (10890381944331/12500000000000 : ℝ)^15
        have hw : |(2242211963/2500000000 : ℝ)|=(2242211963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1237735029/10000000000 : ℝ)|^19 ≤ (3545126485957/50000000000000 : ℝ)^15
        have hw : |(1237735029/10000000000 : ℝ)|=(1237735029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054317247/10000000000 : ℝ)|^19 ≤ (723336433067/12500000000000 : ℝ)^15
        have hw : |(1054317247/10000000000 : ℝ)|=(1054317247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315053_s1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((2486/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2486/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79829/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79829/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(78673/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(78673/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((27017/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27017/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14819/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14819/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14383/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14383/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (34911/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (2486/3125 : ℝ) ^ (75/16 : ℝ) ≤ (34221736544154700659/100000000000000000000 : ℝ) := by
    have hpowers : (2486/3125 : ℝ)^75 ≤ (34221736544154700659/100000000000000000000 : ℝ)^16 := by
      have hnat : (2486 : ℕ)^75*100000000000000000000^16 ≤ 34221736544154700659^16*3125^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2486 3125 34221736544154700659 100000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2486/3125 : ℝ)) (X := (34221736544154700659/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (134221736544154700659/100000000000000000000 : ℝ) ≤ (1064802042143777/1000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (134221736544154700659/100000000000000000000 : ℝ)^16 ≤ (1064802042143777/1000000000000000 : ℝ)^75 := by
      have hnat : (134221736544154700659 : ℕ)^16*1000000000000000^75 ≤ 1064802042143777^75*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        134221736544154700659 100000000000000000000 1064802042143777 1000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1064802042143777/1000000000000000 : ℝ)) (X := (134221736544154700659/100000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (84221736544154700659/50000000000000000000 : ℝ) ≤ (111766133419583/100000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (84221736544154700659/50000000000000000000 : ℝ)^16 ≤ (111766133419583/100000000000000 : ℝ)^75 := by
      have hnat : (84221736544154700659 : ℕ)^16*100000000000000^75 ≤ 111766133419583^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        84221736544154700659 50000000000000000000 111766133419583 100000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (111766133419583/100000000000000 : ℝ)) (X := (84221736544154700659/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(64802042143777/795520000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(52859292052053/795520000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (2486/3125 : ℝ)) (alpha := (64802042143777/795520000000000 : ℝ)) (beta := (52859292052053/795520000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2486/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(64802042143777/795520000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(52859292052053/795520000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (79829/100000 : ℝ) ^ (75/16 : ℝ) ≤ (6956779292113653641/20000000000000000000 : ℝ) := by
    have hpowers : (79829/100000 : ℝ)^75 ≤ (6956779292113653641/20000000000000000000 : ℝ)^16 := by
      have hnat : (79829 : ℕ)^75*20000000000000000000^16 ≤ 6956779292113653641^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79829 100000 6956779292113653641 20000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79829/100000 : ℝ)) (X := (6956779292113653641/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (26956779292113653641/20000000000000000000 : ℝ) ≤ (2664379704813827/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (26956779292113653641/20000000000000000000 : ℝ)^16 ≤ (2664379704813827/2500000000000000 : ℝ)^75 := by
      have hnat : (26956779292113653641 : ℕ)^16*2500000000000000^75 ≤ 2664379704813827^75*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26956779292113653641 20000000000000000000 2664379704813827 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2664379704813827/2500000000000000 : ℝ)) (X := (26956779292113653641/20000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (16956779292113653641/10000000000000000000 : ℝ) ≤ (699530415649013/625000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (16956779292113653641/10000000000000000000 : ℝ)^16 ≤ (699530415649013/625000000000000 : ℝ)^75 := by
      have hnat : (16956779292113653641 : ℕ)^16*625000000000000^75 ≤ 699530415649013^75*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16956779292113653641 10000000000000000000 699530415649013 625000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (699530415649013/625000000000000 : ℝ)) (X := (16956779292113653641/10000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(164379704813827/1995725000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(5349678311289/79829000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (79829/100000 : ℝ)) (alpha := (164379704813827/1995725000000000 : ℝ)) (beta := (5349678311289/79829000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (79829/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(164379704813827/1995725000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(5349678311289/79829000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (78673/100000 : ℝ) ^ (75/16 : ℝ) ≤ (16242505620658153773/50000000000000000000 : ℝ) := by
    have hpowers : (78673/100000 : ℝ)^75 ≤ (16242505620658153773/50000000000000000000 : ℝ)^16 := by
      have hnat : (78673 : ℕ)^75*50000000000000000000^16 ≤ 16242505620658153773^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78673 100000 16242505620658153773 50000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (78673/100000 : ℝ)) (X := (16242505620658153773/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (66242505620658153773/50000000000000000000 : ℝ) ≤ (2654619302910223/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (66242505620658153773/50000000000000000000 : ℝ)^16 ≤ (2654619302910223/2500000000000000 : ℝ)^75 := by
      have hnat : (66242505620658153773 : ℕ)^16*2500000000000000^75 ≤ 2654619302910223^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66242505620658153773 50000000000000000000 2654619302910223 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2654619302910223/2500000000000000 : ℝ)) (X := (66242505620658153773/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (41242505620658153773/25000000000000000000 : ℝ) ≤ (1390880292161713/1250000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (41242505620658153773/25000000000000000000 : ℝ)^16 ≤ (1390880292161713/1250000000000000 : ℝ)^75 := by
      have hnat : (41242505620658153773 : ℕ)^16*1250000000000000^75 ≤ 1390880292161713^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41242505620658153773 25000000000000000000 1390880292161713 1250000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1390880292161713/1250000000000000 : ℝ)) (X := (41242505620658153773/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(154619302910223/1966825000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(127141281413203/1966825000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (78673/100000 : ℝ)) (alpha := (154619302910223/1966825000000000 : ℝ)) (beta := (127141281413203/1966825000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (78673/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(154619302910223/1966825000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(127141281413203/1966825000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-14284883/80000000 : ℝ)*X 0 0+(1036034529/2000000000 : ℝ)*X 0 1+(2673710351/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2256909151/5000000000 : ℝ)*X 1 0+(-17585673/156250000 : ℝ)*X 1 1+(1608533743/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4539577459/10000000000 : ℝ)*X 2 0+(6450689587/10000000000 : ℝ)*X 2 1+(-1061291137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3677342393/5000000000 : ℝ)*X 0 0+(2476496117/10000000000 : ℝ)*X 0 1+(1128202689/5000000000 : ℝ)*X 0 2+(3677342393/5000000000 : ℝ)*X 1 0+(2476496117/10000000000 : ℝ)*X 1 1+(1128202689/5000000000 : ℝ)*X 1 2+(3677342393/5000000000 : ℝ)*X 2 0+(2476496117/10000000000 : ℝ)*X 2 1+(1128202689/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-44032257/250000000 : ℝ)*X 0 0+(795344683/2000000000 : ℝ)*X 0 1+(6488611149/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((464486643/1250000000 : ℝ)*X 1 0+(-56634601/1000000000 : ℝ)*X 1 1+(930753237/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((3742811411/10000000000 : ℝ)*X 2 0+(7584799273/10000000000 : ℝ)*X 2 1+(-20848867/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((6451323967/10000000000 : ℝ)*X 0 0+(19181919/39062500 : ℝ)*X 0 1+(226112243/5000000000 : ℝ)*X 0 2+(6451323967/10000000000 : ℝ)*X 1 0+(19181919/39062500 : ℝ)*X 1 1+(226112243/5000000000 : ℝ)*X 1 2+(6451323967/10000000000 : ℝ)*X 2 0+(19181919/39062500 : ℝ)*X 2 1+(226112243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-994236777/10000000000 : ℝ)*X 0 0+(818302327/2000000000 : ℝ)*X 0 1+(3445165647/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((276778029/1000000000 : ℝ)*X 1 0+(-528462523/5000000000 : ℝ)*X 1 1+(3965041271/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6184013759/10000000000 : ℝ)*X 2 0+(5229746619/10000000000 : ℝ)*X 2 1+(-382713721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((8823279161/10000000000 : ℝ)*X 0 0+(929968829/5000000000 : ℝ)*X 0 1+(59228191/1000000000 : ℝ)*X 0 2+(8823279161/10000000000 : ℝ)*X 1 0+(929968829/5000000000 : ℝ)*X 1 1+(59228191/1000000000 : ℝ)*X 1 2+(8823279161/10000000000 : ℝ)*X 2 0+(929968829/5000000000 : ℝ)*X 2 1+(59228191/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-942040829/10000000000 : ℝ)*X 0 0+(6483242059/10000000000 : ℝ)*X 0 1+(2291718047/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((773148719/1250000000 : ℝ)*X 1 0+(-299607449/10000000000 : ℝ)*X 1 1+(210743653/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((109711023/400000000 : ℝ)*X 2 0+(7969435289/10000000000 : ℝ)*X 2 1+(-510825569/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((2242211963/2500000000 : ℝ)*X 0 0+(1237735029/10000000000 : ℝ)*X 0 1+(1054317247/10000000000 : ℝ)*X 0 2+(2242211963/2500000000 : ℝ)*X 1 0+(1237735029/10000000000 : ℝ)*X 1 1+(1054317247/10000000000 : ℝ)*X 1 2+(2242211963/2500000000 : ℝ)*X 2 0+(1237735029/10000000000 : ℝ)*X 2 1+(1054317247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315053_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((27017/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27017/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (46430461027697229733410605144781/12490433500529600000000000000000000000 : ℝ) := by norm_num
    linear_combination (10088392277/50000000000 : ℝ)*(base7) + (62751578627/250000000000 : ℝ)*(base59) + (3505672504171/1000000000000 : ℝ)*(major_s1_0) + (3505672504171/1000000000000 : ℝ)*(major_s1_1) + (3505672504171/1000000000000 : ℝ)*(major_s1_2) + (7213241/1000000000000 : ℝ)*(sp_s1_0) + (49129/100000000000 : ℝ)*(sp_s1_6) + (4886765067619/1000000000000 : ℝ)*(sp_s1_7) + (488679190529/100000000000 : ℝ)*(sp_s1_8) + (4886792195299/1000000000000 : ℝ)*(sp_s1_9) + (2208919865241/1000000000000 : ℝ)*(sp_s1_13) + (1272279/62500000000 : ℝ)*(sp_s1_14) + (732033/1000000000000 : ℝ)*(sp_s1_22) + (55253/125000000000 : ℝ)*(sp_s1_23) + (2007152510991/1000000000000 : ℝ)*(f.failure) + (1221698159331/250000000000 : ℝ)*(f.sum) + (4414129301214044259/19626209115625000000000000000000 : ℝ)*base62 + (959085323943843/1966825000000000000000000000 : ℝ)*base64 + (121258859618773/159658000000000000000000000 : ℝ)*base66 + (1755172232614229/3933650000000000000000000000 : ℝ)*base68 + (18467513854028269543/312929724800000000000000000000000 : ℝ)*base71 + (94741102631609/795520000000000000000000000 : ℝ)*base72 + (967662132401093/1995725000000000000000000000 : ℝ)*base74 + (198040999529717/795520000000000000000000000 : ℝ)*base76 + (246940222829325577/12701113216000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (77069/100000000000000000 : ℝ)*base87 + (77069/100000000000000000 : ℝ)*base89 + (77069/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14819/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14819/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15906198971215137/1250000000000000000000 : ℝ) := by norm_num
    linear_combination (22750630007/40000000000 : ℝ)*(base7) + (2110223/1000000000000 : ℝ)*(base59) + (287525887737/125000000000 : ℝ)*(major_s1_0) + (287525887737/125000000000 : ℝ)*(major_s1_1) + (287525887737/125000000000 : ℝ)*(major_s1_2) + (4745519/250000000000 : ℝ)*(sp_s1_0) + (14855631/500000000000 : ℝ)*(sp_s1_2) + (25129123/1000000000000 : ℝ)*(sp_s1_7) + (1084519/12500000000 : ℝ)*(sp_s1_8) + (2952459230331/1000000000000 : ℝ)*(sp_s1_14) + (2952416580009/1000000000000 : ℝ)*(sp_s1_15) + (738118407567/250000000000 : ℝ)*(sp_s1_16) + (942834449649/500000000000 : ℝ)*(sp_s1_20) + (33559871/500000000000 : ℝ)*(sp_s1_27) + (263394053773/200000000000 : ℝ)*(f.failure) + (2952503341529/1000000000000 : ℝ)*(f.sum) + (19231337523396681421/314019345850000000000000000000000 : ℝ)*base63 + (57402791414439/983412500000000000000000000 : ℝ)*base64 + (507847527336003/798290000000000000000000000 : ℝ)*base66 + (193920985917091/983412500000000000000000000 : ℝ)*base68 + (1596647554405840551/3556019600000000000000000000000 : ℝ)*base71 + (59920595257/9040000000000000000000000 : ℝ)*base72 + (296732731936457/498931250000000000000000000 : ℝ)*base74 + (5947571214293/9040000000000000000000000 : ℝ)*base76 + (25729735742013907/721654160000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (18407/20000000000000000 : ℝ)*base87 + (18407/20000000000000000 : ℝ)*base89 + (18407/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14383/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14383/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9197222951617171185683249698353/624521675026480000000000000000000000 : ℝ) := by norm_num
    linear_combination (10762585243/20000000000 : ℝ)*(base7) + (698891/125000000000 : ℝ)*(base11) + (7397571/500000000000 : ℝ)*(base27) + (698793/1000000000000 : ℝ)*(base34) + (101226696727/1000000000000 : ℝ)*(base40) + (111866925831/50000000000 : ℝ)*(major_s1_0) + (2237339215413/1000000000000 : ℝ)*(major_s1_1) + (2237339215413/1000000000000 : ℝ)*(major_s1_2) + (14488217/1000000000000 : ℝ)*(sp_s1_1) + (12661313/125000000000 : ℝ)*(sp_s1_9) + (2880581096609/1000000000000 : ℝ)*(sp_s1_21) + (2880572898313/1000000000000 : ℝ)*(sp_s1_22) + (2880486096027/1000000000000 : ℝ)*(sp_s1_23) + (909544696191/500000000000 : ℝ)*(sp_s1_27) + (1280975624167/1000000000000 : ℝ)*(f.failure) + (288058738653/100000000000 : ℝ)*(f.sum) + (36400426173511164967/314019345850000000000000000000000 : ℝ)*base62 + (491038574009037/3933650000000000000000000000 : ℝ)*base65 + (5009454536397/79829000000000000000000000 : ℝ)*base66 + (88959032969957/245853125000000000000000000 : ℝ)*base68 + (4407412972038658671/78232431200000000000000000000000 : ℝ)*base71 + (58227328590449/198880000000000000000000000 : ℝ)*base72 + (3120925336280183/3991450000000000000000000000 : ℝ)*base74 + (151386502700589/198880000000000000000000000 : ℝ)*base76 + (2199974726358504021/15876391520000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (84053/100000000000000000 : ℝ)*base87 + (84053/100000000000000000 : ℝ)*base89 + (84053/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((2486/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2486/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79829/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79829/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(78673/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(78673/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((27017/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27017/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14819/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14819/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14383/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14383/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c315053_s1 p hpa hpb X hX hprev0

#print axioms solution

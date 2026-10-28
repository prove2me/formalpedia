-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1056_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:59:40.687891+00:00
-- url     : https://prove2.me/submissions/6b1270d6-6483-44ed-8516-98263acbca74

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
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
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
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
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
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

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
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


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

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
theorem support_rectangle_w1056_s9_0 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-441740263/2000000000 : ℝ)*x 0 + (5394505801/10000000000 : ℝ)*x 1 + (131607337/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (441740263/2000000000 : ℝ)^8249 ≤ (13412988893419/100000000000000 : ℝ)^6201 := by
    have hnat : (441740263 : ℕ)^8249*100000000000000^6201 ≤ 13412988893419^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441740263 2000000000 13412988893419 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394505801/10000000000 : ℝ)^8249 ≤ (43997046678287/100000000000000 : ℝ)^6201 := by
    have hnat : (5394505801 : ℕ)^8249*100000000000000^6201 ≤ 43997046678287^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394505801 10000000000 43997046678287 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131607337/250000000 : ℝ)^8249 ≤ (532374555157/1250000000000 : ℝ)^6201 := by
    have hnat : (131607337 : ℕ)^8249*1250000000000^6201 ≤ 532374555157^6201*250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131607337 250000000 532374555157 1250000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-441740263/2000000000 : ℝ), (5394505801/10000000000 : ℝ), (131607337/250000000 : ℝ)] ![(13412988893419/100000000000000 : ℝ), (43997046678287/100000000000000 : ℝ), (532374555157/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-441740263/2000000000 : ℝ)|^8249 ≤ (13412988893419/100000000000000 : ℝ)^6201
        have hw : |(-441740263/2000000000 : ℝ)|=(441740263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394505801/10000000000 : ℝ)|^8249 ≤ (43997046678287/100000000000000 : ℝ)^6201
        have hw : |(5394505801/10000000000 : ℝ)|=(5394505801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131607337/250000000 : ℝ)|^8249 ≤ (532374555157/1250000000000 : ℝ)^6201
        have hw : |(131607337/250000000 : ℝ)|=(131607337/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s9_1 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (133624893/250000000 : ℝ)*x 0 + (-2274769269/10000000000 : ℝ)*x 1 + (2632146747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133624893/250000000 : ℝ)^8249 ≤ (21730350364677/50000000000000 : ℝ)^6201 := by
    have hnat : (133624893 : ℕ)^8249*50000000000000^6201 ≤ 21730350364677^6201*250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133624893 250000000 21730350364677 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2274769269/10000000000 : ℝ)^8249 ≤ (3487333674169/25000000000000 : ℝ)^6201 := by
    have hnat : (2274769269 : ℕ)^8249*25000000000000^6201 ≤ 3487333674169^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274769269 10000000000 3487333674169 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632146747/5000000000 : ℝ)^8249 ≤ (42589964563233/100000000000000 : ℝ)^6201 := by
    have hnat : (2632146747 : ℕ)^8249*100000000000000^6201 ≤ 42589964563233^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632146747 5000000000 42589964563233 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133624893/250000000 : ℝ), (-2274769269/10000000000 : ℝ), (2632146747/5000000000 : ℝ)] ![(21730350364677/50000000000000 : ℝ), (3487333674169/25000000000000 : ℝ), (42589964563233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133624893/250000000 : ℝ)|^8249 ≤ (21730350364677/50000000000000 : ℝ)^6201
        have hw : |(133624893/250000000 : ℝ)|=(133624893/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2274769269/10000000000 : ℝ)|^8249 ≤ (3487333674169/25000000000000 : ℝ)^6201
        have hw : |(-2274769269/10000000000 : ℝ)|=(2274769269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632146747/5000000000 : ℝ)|^8249 ≤ (42589964563233/100000000000000 : ℝ)^6201
        have hw : |(2632146747/5000000000 : ℝ)|=(2632146747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s9_2 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-220870613/1000000000 : ℝ)*x 0 + (5264619039/10000000000 : ℝ)*x 1 + (5394179267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (220870613/1000000000 : ℝ)^8249 ≤ (13413027791179/100000000000000 : ℝ)^6201 := by
    have hnat : (220870613 : ℕ)^8249*100000000000000^6201 ≤ 13413027791179^6201*1000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220870613 1000000000 13413027791179 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264619039/10000000000 : ℝ)^8249 ≤ (42593468225381/100000000000000 : ℝ)^6201 := by
    have hnat : (5264619039 : ℕ)^8249*100000000000000^6201 ≤ 42593468225381^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264619039 10000000000 42593468225381 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394179267/10000000000 : ℝ)^8249 ≤ (43993503969127/100000000000000 : ℝ)^6201 := by
    have hnat : (5394179267 : ℕ)^8249*100000000000000^6201 ≤ 43993503969127^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394179267 10000000000 43993503969127 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-220870613/1000000000 : ℝ), (5264619039/10000000000 : ℝ), (5394179267/10000000000 : ℝ)] ![(13413027791179/100000000000000 : ℝ), (42593468225381/100000000000000 : ℝ), (43993503969127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-220870613/1000000000 : ℝ)|^8249 ≤ (13413027791179/100000000000000 : ℝ)^6201
        have hw : |(-220870613/1000000000 : ℝ)|=(220870613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264619039/10000000000 : ℝ)|^8249 ≤ (42593468225381/100000000000000 : ℝ)^6201
        have hw : |(5264619039/10000000000 : ℝ)|=(5264619039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394179267/10000000000 : ℝ)|^8249 ≤ (43993503969127/100000000000000 : ℝ)^6201
        have hw : |(5394179267/10000000000 : ℝ)|=(5394179267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s9_3 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312223337/10000000000 : ℝ)*x 0 + (-2144884007/10000000000 : ℝ)*x 1 + (674272413/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312223337/10000000000 : ℝ)^8249 ≤ (2155328794009/5000000000000 : ℝ)^6201 := by
    have hnat : (5312223337 : ℕ)^8249*5000000000000^6201 ≤ 2155328794009^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312223337 10000000000 2155328794009 5000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2144884007/10000000000 : ℝ)^8249 ≤ (6449959866883/50000000000000 : ℝ)^6201 := by
    have hnat : (2144884007 : ℕ)^8249*50000000000000^6201 ≤ 6449959866883^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144884007 10000000000 6449959866883 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674272413/1250000000 : ℝ)^8249 ≤ (5499188046319/12500000000000 : ℝ)^6201 := by
    have hnat : (674272413 : ℕ)^8249*12500000000000^6201 ≤ 5499188046319^6201*1250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674272413 1250000000 5499188046319 12500000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312223337/10000000000 : ℝ), (-2144884007/10000000000 : ℝ), (674272413/1250000000 : ℝ)] ![(2155328794009/5000000000000 : ℝ), (6449959866883/50000000000000 : ℝ), (5499188046319/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312223337/10000000000 : ℝ)|^8249 ≤ (2155328794009/5000000000000 : ℝ)^6201
        have hw : |(5312223337/10000000000 : ℝ)|=(5312223337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2144884007/10000000000 : ℝ)|^8249 ≤ (6449959866883/50000000000000 : ℝ)^6201
        have hw : |(-2144884007/10000000000 : ℝ)|=(2144884007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674272413/1250000000 : ℝ)|^8249 ≤ (5499188046319/12500000000000 : ℝ)^6201
        have hw : |(674272413/1250000000 : ℝ)|=(674272413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s9_4 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106244481/200000000 : ℝ)*x 0 + (5394178337/10000000000 : ℝ)*x 1 + (-2144884357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106244481/200000000 : ℝ)^8249 ≤ (21553291788367/50000000000000 : ℝ)^6201 := by
    have hnat : (106244481 : ℕ)^8249*50000000000000^6201 ≤ 21553291788367^6201*200000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106244481 200000000 21553291788367 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394178337/10000000000 : ℝ)^8249 ≤ (21996746939627/50000000000000 : ℝ)^6201 := by
    have hnat : (5394178337 : ℕ)^8249*50000000000000^6201 ≤ 21996746939627^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394178337 10000000000 21996746939627 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2144884357/10000000000 : ℝ)^8249 ≤ (12899922533977/100000000000000 : ℝ)^6201 := by
    have hnat : (2144884357 : ℕ)^8249*100000000000000^6201 ≤ 12899922533977^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144884357 10000000000 12899922533977 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106244481/200000000 : ℝ), (5394178337/10000000000 : ℝ), (-2144884357/10000000000 : ℝ)] ![(21553291788367/50000000000000 : ℝ), (21996746939627/50000000000000 : ℝ), (12899922533977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106244481/200000000 : ℝ)|^8249 ≤ (21553291788367/50000000000000 : ℝ)^6201
        have hw : |(106244481/200000000 : ℝ)|=(106244481/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394178337/10000000000 : ℝ)|^8249 ≤ (21996746939627/50000000000000 : ℝ)^6201
        have hw : |(5394178337/10000000000 : ℝ)|=(5394178337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2144884357/10000000000 : ℝ)|^8249 ≤ (12899922533977/100000000000000 : ℝ)^6201
        have hw : |(-2144884357/10000000000 : ℝ)|=(2144884357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_s9_5 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2188472063/5000000000 : ℝ)*x 0 + (4505522759/10000000000 : ℝ)*x 1 + (4252108909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188472063/5000000000 : ℝ)^8249 ≤ (8329152341221/25000000000000 : ℝ)^6201 := by
    have hnat : (2188472063 : ℕ)^8249*25000000000000^6201 ≤ 8329152341221^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188472063 5000000000 8329152341221 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4505522759/10000000000 : ℝ)^8249 ≤ (34624845915349/100000000000000 : ℝ)^6201 := by
    have hnat : (4505522759 : ℕ)^8249*100000000000000^6201 ≤ 34624845915349^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505522759 10000000000 34624845915349 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4252108909/10000000000 : ℝ)^8249 ≤ (16029272353413/50000000000000 : ℝ)^6201 := by
    have hnat : (4252108909 : ℕ)^8249*50000000000000^6201 ≤ 16029272353413^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252108909 10000000000 16029272353413 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188472063/5000000000 : ℝ), (4505522759/10000000000 : ℝ), (4252108909/10000000000 : ℝ)] ![(8329152341221/25000000000000 : ℝ), (34624845915349/100000000000000 : ℝ), (16029272353413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188472063/5000000000 : ℝ)|^8249 ≤ (8329152341221/25000000000000 : ℝ)^6201
        have hw : |(2188472063/5000000000 : ℝ)|=(2188472063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4505522759/10000000000 : ℝ)|^8249 ≤ (34624845915349/100000000000000 : ℝ)^6201
        have hw : |(4505522759/10000000000 : ℝ)|=(4505522759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4252108909/10000000000 : ℝ)|^8249 ≤ (16029272353413/50000000000000 : ℝ)^6201
        have hw : |(4252108909/10000000000 : ℝ)|=(4252108909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1056_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13997/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5619/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3499/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13997/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5619/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13997/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5619/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13997/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5619/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13997/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5619/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13997/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5619/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13997/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5619/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (5619/50000 : ℝ) ^ (1031/256 : ℝ) ≤ (7512221651015079/50000000000000000000 : ℝ) := by
    have hpowers : (5619/50000 : ℝ)^1031 ≤ (7512221651015079/50000000000000000000 : ℝ)^256 := by
      have hnat : (5619 : ℕ)^1031*50000000000000000000^256 ≤ 7512221651015079^256*50000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5619 50000 7512221651015079 50000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5619/50000 : ℝ)) (X := (7512221651015079/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hpowhi : (13997/100000 : ℝ) ^ (1031/256 : ℝ) ≤ (18186923844784029/50000000000000000000 : ℝ) := by
    have hpowers : (13997/100000 : ℝ)^1031 ≤ (18186923844784029/50000000000000000000 : ℝ)^256 := by
      have hnat : (13997 : ℕ)^1031*50000000000000000000^256 ≤ 18186923844784029^256*100000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13997 100000 18186923844784029 50000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13997/100000 : ℝ)) (X := (18186923844784029/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007512221651015079/25000000000000000000 : ℝ) ≤ (500037301873633/500000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (25007512221651015079/25000000000000000000 : ℝ)^256 ≤ (500037301873633/500000000000000 : ℝ)^1031 := by
      have hnat : (25007512221651015079 : ℕ)^256*500000000000000^1031 ≤ 500037301873633^1031*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007512221651015079 25000000000000000000 500037301873633 500000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500037301873633/500000000000000 : ℝ)) (X := (25007512221651015079/25000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506424786373949777/12500000000000000000 : ℝ) ≤ (10001275986557111/10000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (12506424786373949777/12500000000000000000 : ℝ)^256 ≤ (10001275986557111/10000000000000000 : ℝ)^1031 := by
      have hnat : (12506424786373949777 : ℕ)^256*10000000000000000^1031 ≤ 10001275986557111^1031*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506424786373949777 12500000000000000000 10001275986557111 10000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001275986557111/10000000000000000 : ℝ)) (X := (12506424786373949777/12500000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018186923844784029/25000000000000000000 : ℝ) ≤ (5000902967820781/5000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (25018186923844784029/25000000000000000000 : ℝ)^256 ≤ (5000902967820781/5000000000000000 : ℝ)^1031 := by
      have hnat : (25018186923844784029 : ℕ)^256*5000000000000000^1031 ≤ 5000902967820781^1031*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018186923844784029 25000000000000000000 5000902967820781 5000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000902967820781/5000000000000000 : ℝ)) (X := (25018186923844784029/25000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7512221651015079/50000000000000000000 : ℝ) ≤ ((3447518397720618533/3448750000000000000 : ℝ)+2*(529949084451/275900000000000 : ℝ)*(5619/50000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (3447518397720618533/3448750000000000000 : ℝ)+2*(529949084451/275900000000000 : ℝ)*(5619/50000 : ℝ)=(500037301873633/500000000000000 : ℝ) by norm_num, show 1+2*(7512221651015079/50000000000000000000 : ℝ)=(25007512221651015079/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18186923844784029/50000000000000000000 : ℝ)+(7512221651015079/50000000000000000000 : ℝ) ≤ ((3447518397720618533/3448750000000000000 : ℝ)+(529949084451/275900000000000 : ℝ)*((13997/100000 : ℝ)+(5619/50000 : ℝ)))^(1031/256 : ℝ) := by
    rw [show (3447518397720618533/3448750000000000000 : ℝ)+(529949084451/275900000000000 : ℝ)*((13997/100000 : ℝ)+(5619/50000 : ℝ))=(10001275986557111/10000000000000000 : ℝ) by norm_num, show 1+(18186923844784029/50000000000000000000 : ℝ)+(7512221651015079/50000000000000000000 : ℝ)=(12506424786373949777/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18186923844784029/50000000000000000000 : ℝ) ≤ ((3447518397720618533/3448750000000000000 : ℝ)+2*(529949084451/275900000000000 : ℝ)*(13997/100000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (3447518397720618533/3448750000000000000 : ℝ)+2*(529949084451/275900000000000 : ℝ)*(13997/100000 : ℝ)=(5000902967820781/5000000000000000 : ℝ) by norm_num, show 1+2*(18186923844784029/50000000000000000000 : ℝ)=(25018186923844784029/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3447518397720618533/3448750000000000000 : ℝ)*(X 1 0+X 2 0)+(529949084451/275900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (5619/50000 : ℝ)) (hi := (13997/100000 : ℝ)) (c := (3447518397720618533/3448750000000000000 : ℝ)) (alpha := (529949084451/275900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3447518397720618533/3448750000000000000 : ℝ)*(X 0 1+X 2 1)+(529949084451/275900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (5619/50000 : ℝ)) (hi := (13997/100000 : ℝ)) (c := (3447518397720618533/3448750000000000000 : ℝ)) (alpha := (529949084451/275900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3447518397720618533/3448750000000000000 : ℝ)*(X 0 2+X 1 2)+(529949084451/275900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (5619/50000 : ℝ)) (hi := (13997/100000 : ℝ)) (c := (3447518397720618533/3448750000000000000 : ℝ)) (alpha := (529949084451/275900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-441740263/2000000000 : ℝ)*X 0 0+(5394505801/10000000000 : ℝ)*X 0 1+(131607337/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133624893/250000000 : ℝ)*X 1 0+(-2274769269/10000000000 : ℝ)*X 1 1+(2632146747/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-220870613/1000000000 : ℝ)*X 0 0+(5264619039/10000000000 : ℝ)*X 0 1+(5394179267/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s9_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312223337/10000000000 : ℝ)*X 1 0+(-2144884007/10000000000 : ℝ)*X 1 1+(674272413/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s9_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((106244481/200000000 : ℝ)*X 2 0+(5394178337/10000000000 : ℝ)*X 2 1+(-2144884357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s9_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2188472063/5000000000 : ℝ)*X 0 0+(4505522759/10000000000 : ℝ)*X 0 1+(4252108909/10000000000 : ℝ)*X 0 2+(2188472063/5000000000 : ℝ)*X 1 0+(4505522759/10000000000 : ℝ)*X 1 1+(4252108909/10000000000 : ℝ)*X 1 2+(2188472063/5000000000 : ℝ)*X 2 0+(4505522759/10000000000 : ℝ)*X 2 1+(4252108909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1090029551587164370170703263/172437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41502239/5000000000000 : ℝ)*(base23) + (239553481/100000000000000 : ℝ)*(lower2) + (21646529/50000000000000 : ℝ)*(upper3) + (51847573/25000000000000 : ℝ)*(lower4) + (3575453/1562500000000 : ℝ)*(upper5) + (5832300957693937/100000000000000 : ℝ)*(major0) + (5832300957693937/100000000000000 : ℝ)*(major1) + (5832300957693937/100000000000000 : ℝ)*(major2) + (12349472861/50000000000000 : ℝ)*(sp0) + (11782254777/50000000000000 : ℝ)*(sp1) + (1543692330502867/20000000000000 : ℝ)*(sp2) + (1543692557390101/20000000000000 : ℝ)*(sp3) + (3859242760707639/50000000000000 : ℝ)*(sp4) + (1973057676608859/50000000000000 : ℝ)*(sp5) + (1973057676608859/50000000000000 : ℝ)*(f.failure) + (3859243175730029/50000000000000 : ℝ)*(f.sum) + (433167397728373/13795000000000000000000000000 : ℝ)*base66 + (5690055430372603079/344875000000000000000000000000000 : ℝ)*base68 + (2974365654082146921/344875000000000000000000000000000 : ℝ)*base69 + (40378433800454603079/344875000000000000000000000000000 : ℝ)*base72 + (4900127730513/862187500000000000000000000 : ℝ)*base74 + (3333606811163978079/344875000000000000000000000000000 : ℝ)*base76 + (5227046609550228079/344875000000000000000000000000000 : ℝ)*base78 + (2589056825884771921/344875000000000000000000000000000 : ℝ)*base79 + (74976711749867/13795000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (7241789/2500000000000000000000 : ℝ)*base89 + (7241789/2500000000000000000000 : ℝ)*base91 + (7241789/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1056_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13997/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1056_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1056_box_0 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2078896893/10000000000 : ℝ)*x 0 + (5377501061/10000000000 : ℝ)*x 1 + (5377502721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2078896893/10000000000 : ℝ)^8249 ≤ (12374683736841/100000000000000 : ℝ)^6201 := by
    have hnat : (2078896893 : ℕ)^8249*100000000000000^6201 ≤ 12374683736841^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078896893 10000000000 12374683736841 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377501061/10000000000 : ℝ)^8249 ≤ (10953162282559/25000000000000 : ℝ)^6201 := by
    have hnat : (5377501061 : ℕ)^8249*25000000000000^6201 ≤ 10953162282559^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377501061 10000000000 10953162282559 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377502721/10000000000 : ℝ)^8249 ≤ (10953166780427/25000000000000 : ℝ)^6201 := by
    have hnat : (5377502721 : ℕ)^8249*25000000000000^6201 ≤ 10953166780427^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377502721 10000000000 10953166780427 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2078896893/10000000000 : ℝ), (5377501061/10000000000 : ℝ), (5377502721/10000000000 : ℝ)] ![(12374683736841/100000000000000 : ℝ), (10953162282559/25000000000000 : ℝ), (10953166780427/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2078896893/10000000000 : ℝ)|^8249 ≤ (12374683736841/100000000000000 : ℝ)^6201
        have hw : |(-2078896893/10000000000 : ℝ)|=(2078896893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377501061/10000000000 : ℝ)|^8249 ≤ (10953162282559/25000000000000 : ℝ)^6201
        have hw : |(5377501061/10000000000 : ℝ)|=(5377501061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377502721/10000000000 : ℝ)|^8249 ≤ (10953166780427/25000000000000 : ℝ)^6201
        have hw : |(5377502721/10000000000 : ℝ)|=(5377502721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_box_1 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647544357/5000000000 : ℝ)*x 0 + (-219043521/1000000000 : ℝ)*x 1 + (2688750943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647544357/5000000000 : ℝ)^8249 ≤ (8584342594961/20000000000000 : ℝ)^6201 := by
    have hnat : (2647544357 : ℕ)^8249*20000000000000^6201 ≤ 8584342594961^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647544357 5000000000 8584342594961 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219043521/1000000000 : ℝ)^8249 ≤ (2653125787243/20000000000000 : ℝ)^6201 := by
    have hnat : (219043521 : ℕ)^8249*20000000000000^6201 ≤ 2653125787243^6201*1000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219043521 1000000000 2653125787243 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688750943/5000000000 : ℝ)^8249 ≤ (2190632903589/5000000000000 : ℝ)^6201 := by
    have hnat : (2688750943 : ℕ)^8249*5000000000000^6201 ≤ 2190632903589^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688750943 5000000000 2190632903589 5000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647544357/5000000000 : ℝ), (-219043521/1000000000 : ℝ), (2688750943/5000000000 : ℝ)] ![(8584342594961/20000000000000 : ℝ), (2653125787243/20000000000000 : ℝ), (2190632903589/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647544357/5000000000 : ℝ)|^8249 ≤ (8584342594961/20000000000000 : ℝ)^6201
        have hw : |(2647544357/5000000000 : ℝ)|=(2647544357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219043521/1000000000 : ℝ)|^8249 ≤ (2653125787243/20000000000000 : ℝ)^6201
        have hw : |(-219043521/1000000000 : ℝ)|=(219043521/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688750943/5000000000 : ℝ)|^8249 ≤ (2190632903589/5000000000000 : ℝ)^6201
        have hw : |(2688750943/5000000000 : ℝ)|=(2688750943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_box_2 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1059017797/2000000000 : ℝ)*x 0 + (2688751221/5000000000 : ℝ)*x 1 + (-2190434099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059017797/2000000000 : ℝ)^8249 ≤ (42921715897023/100000000000000 : ℝ)^6201 := by
    have hnat : (1059017797 : ℕ)^8249*100000000000000^6201 ≤ 42921715897023^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059017797 2000000000 42921715897023 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688751221/5000000000 : ℝ)^8249 ≤ (547658301223/1250000000000 : ℝ)^6201 := by
    have hnat : (2688751221 : ℕ)^8249*1250000000000^6201 ≤ 547658301223^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688751221 5000000000 547658301223 1250000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2190434099/10000000000 : ℝ)^8249 ≤ (6632809992819/50000000000000 : ℝ)^6201 := by
    have hnat : (2190434099 : ℕ)^8249*50000000000000^6201 ≤ 6632809992819^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190434099 10000000000 6632809992819 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059017797/2000000000 : ℝ), (2688751221/5000000000 : ℝ), (-2190434099/10000000000 : ℝ)] ![(42921715897023/100000000000000 : ℝ), (547658301223/1250000000000 : ℝ), (6632809992819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059017797/2000000000 : ℝ)|^8249 ≤ (42921715897023/100000000000000 : ℝ)^6201
        have hw : |(1059017797/2000000000 : ℝ)|=(1059017797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688751221/5000000000 : ℝ)|^8249 ≤ (547658301223/1250000000000 : ℝ)^6201
        have hw : |(2688751221/5000000000 : ℝ)|=(2688751221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2190434099/10000000000 : ℝ)|^8249 ≤ (6632809992819/50000000000000 : ℝ)^6201
        have hw : |(-2190434099/10000000000 : ℝ)|=(2190434099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_box_3 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (140169841/312500000 : ℝ)*x 0 + (2162426331/5000000000 : ℝ)*x 1 + (2162426361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140169841/312500000 : ℝ)^8249 ≤ (34419637371443/100000000000000 : ℝ)^6201 := by
    have hnat : (140169841 : ℕ)^8249*100000000000000^6201 ≤ 34419637371443^6201*312500000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140169841 312500000 34419637371443 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2162426331/5000000000 : ℝ)^8249 ≤ (32790181005133/100000000000000 : ℝ)^6201 := by
    have hnat : (2162426331 : ℕ)^8249*100000000000000^6201 ≤ 32790181005133^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162426331 5000000000 32790181005133 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2162426361/5000000000 : ℝ)^8249 ≤ (32790181610283/100000000000000 : ℝ)^6201 := by
    have hnat : (2162426361 : ℕ)^8249*100000000000000^6201 ≤ 32790181610283^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162426361 5000000000 32790181610283 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(140169841/312500000 : ℝ), (2162426331/5000000000 : ℝ), (2162426361/5000000000 : ℝ)] ![(34419637371443/100000000000000 : ℝ), (32790181005133/100000000000000 : ℝ), (32790181610283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(140169841/312500000 : ℝ)|^8249 ≤ (34419637371443/100000000000000 : ℝ)^6201
        have hw : |(140169841/312500000 : ℝ)|=(140169841/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2162426331/5000000000 : ℝ)|^8249 ≤ (32790181005133/100000000000000 : ℝ)^6201
        have hw : |(2162426331/5000000000 : ℝ)|=(2162426331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2162426361/5000000000 : ℝ)|^8249 ≤ (32790181610283/100000000000000 : ℝ)^6201
        have hw : |(2162426361/5000000000 : ℝ)|=(2162426361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_box_4 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2339899103/10000000000 : ℝ)*x 0 + (1319984933/2500000000 : ℝ)*x 1 + (1055987939/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2339899103/10000000000 : ℝ)^8249 ≤ (14483125759039/100000000000000 : ℝ)^6201 := by
    have hnat : (2339899103 : ℕ)^8249*100000000000000^6201 ≤ 14483125759039^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2339899103 10000000000 14483125759039 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319984933/2500000000 : ℝ)^8249 ≤ (42758437307087/100000000000000 : ℝ)^6201 := by
    have hnat : (1319984933 : ℕ)^8249*100000000000000^6201 ≤ 42758437307087^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319984933 2500000000 42758437307087 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055987939/2000000000 : ℝ)^8249 ≤ (4275843690849/10000000000000 : ℝ)^6201 := by
    have hnat : (1055987939 : ℕ)^8249*10000000000000^6201 ≤ 4275843690849^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055987939 2000000000 4275843690849 10000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2339899103/10000000000 : ℝ), (1319984933/2500000000 : ℝ), (1055987939/2000000000 : ℝ)] ![(14483125759039/100000000000000 : ℝ), (42758437307087/100000000000000 : ℝ), (4275843690849/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2339899103/10000000000 : ℝ)|^8249 ≤ (14483125759039/100000000000000 : ℝ)^6201
        have hw : |(-2339899103/10000000000 : ℝ)|=(2339899103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1319984933/2500000000 : ℝ)|^8249 ≤ (42758437307087/100000000000000 : ℝ)^6201
        have hw : |(1319984933/2500000000 : ℝ)|=(1319984933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055987939/2000000000 : ℝ)|^8249 ≤ (4275843690849/10000000000000 : ℝ)^6201
        have hw : |(1055987939/2000000000 : ℝ)|=(1055987939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_box_5 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1341037827/2500000000 : ℝ)*x 0 + (-2228546331/10000000000 : ℝ)*x 1 + (5279939609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341037827/2500000000 : ℝ)^8249 ≤ (43668020711793/100000000000000 : ℝ)^6201 := by
    have hnat : (1341037827 : ℕ)^8249*100000000000000^6201 ≤ 43668020711793^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341037827 2500000000 43668020711793 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2228546331/10000000000 : ℝ)^8249 ≤ (6786771646363/50000000000000 : ℝ)^6201 := by
    have hnat : (2228546331 : ℕ)^8249*50000000000000^6201 ≤ 6786771646363^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2228546331 10000000000 6786771646363 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279939609/10000000000 : ℝ)^8249 ≤ (42758435982021/100000000000000 : ℝ)^6201 := by
    have hnat : (5279939609 : ℕ)^8249*100000000000000^6201 ≤ 42758435982021^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279939609 10000000000 42758435982021 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341037827/2500000000 : ℝ), (-2228546331/10000000000 : ℝ), (5279939609/10000000000 : ℝ)] ![(43668020711793/100000000000000 : ℝ), (6786771646363/50000000000000 : ℝ), (42758435982021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341037827/2500000000 : ℝ)|^8249 ≤ (43668020711793/100000000000000 : ℝ)^6201
        have hw : |(1341037827/2500000000 : ℝ)|=(1341037827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2228546331/10000000000 : ℝ)|^8249 ≤ (6786771646363/50000000000000 : ℝ)^6201
        have hw : |(-2228546331/10000000000 : ℝ)|=(2228546331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279939609/10000000000 : ℝ)|^8249 ≤ (42758435982021/100000000000000 : ℝ)^6201
        have hw : |(5279939609/10000000000 : ℝ)|=(5279939609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_box_6 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5364150987/10000000000 : ℝ)*x 0 + (2639969959/5000000000 : ℝ)*x 1 + (-44570927/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364150987/10000000000 : ℝ)^8249 ≤ (21834008617787/50000000000000 : ℝ)^6201 := by
    have hnat : (5364150987 : ℕ)^8249*50000000000000^6201 ≤ 21834008617787^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364150987 10000000000 21834008617787 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639969959/5000000000 : ℝ)^8249 ≤ (8551687862169/20000000000000 : ℝ)^6201 := by
    have hnat : (2639969959 : ℕ)^8249*20000000000000^6201 ≤ 8551687862169^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639969959 5000000000 8551687862169 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44570927/200000000 : ℝ)^8249 ≤ (1357354344667/10000000000000 : ℝ)^6201 := by
    have hnat : (44570927 : ℕ)^8249*10000000000000^6201 ≤ 1357354344667^6201*200000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44570927 200000000 1357354344667 10000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364150987/10000000000 : ℝ), (2639969959/5000000000 : ℝ), (-44570927/200000000 : ℝ)] ![(21834008617787/50000000000000 : ℝ), (8551687862169/20000000000000 : ℝ), (1357354344667/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364150987/10000000000 : ℝ)|^8249 ≤ (21834008617787/50000000000000 : ℝ)^6201
        have hw : |(5364150987/10000000000 : ℝ)|=(5364150987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639969959/5000000000 : ℝ)|^8249 ≤ (8551687862169/20000000000000 : ℝ)^6201
        have hw : |(2639969959/5000000000 : ℝ)|=(2639969959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44570927/200000000 : ℝ)|^8249 ≤ (1357354344667/10000000000000 : ℝ)^6201
        have hw : |(-44570927/200000000 : ℝ)|=(44570927/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_box_7 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (853621447/2000000000 : ℝ)*x 0 + (4433495173/10000000000 : ℝ)*x 1 + (554186849/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853621447/2000000000 : ℝ)^8249 ≤ (32219099420443/100000000000000 : ℝ)^6201 := by
    have hnat : (853621447 : ℕ)^8249*100000000000000^6201 ≤ 32219099420443^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853621447 2000000000 32219099420443 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4433495173/10000000000 : ℝ)^8249 ≤ (33890452217003/100000000000000 : ℝ)^6201 := by
    have hnat : (4433495173 : ℕ)^8249*100000000000000^6201 ≤ 33890452217003^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4433495173 10000000000 33890452217003 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554186849/1250000000 : ℝ)^8249 ≤ (16945224171341/50000000000000 : ℝ)^6201 := by
    have hnat : (554186849 : ℕ)^8249*50000000000000^6201 ≤ 16945224171341^6201*1250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554186849 1250000000 16945224171341 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(853621447/2000000000 : ℝ), (4433495173/10000000000 : ℝ), (554186849/1250000000 : ℝ)] ![(32219099420443/100000000000000 : ℝ), (33890452217003/100000000000000 : ℝ), (16945224171341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(853621447/2000000000 : ℝ)|^8249 ≤ (32219099420443/100000000000000 : ℝ)^6201
        have hw : |(853621447/2000000000 : ℝ)|=(853621447/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4433495173/10000000000 : ℝ)|^8249 ≤ (33890452217003/100000000000000 : ℝ)^6201
        have hw : |(4433495173/10000000000 : ℝ)|=(4433495173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(554186849/1250000000 : ℝ)|^8249 ≤ (16945224171341/50000000000000 : ℝ)^6201
        have hw : |(554186849/1250000000 : ℝ)|=(554186849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_box_8 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2285425281/10000000000 : ℝ)*x 0 + (2606878783/5000000000 : ℝ)*x 1 + (538710119/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2285425281/10000000000 : ℝ)^8249 ≤ (7018164006703/50000000000000 : ℝ)^6201 := by
    have hnat : (2285425281 : ℕ)^8249*50000000000000^6201 ≤ 7018164006703^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285425281 10000000000 7018164006703 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606878783/5000000000 : ℝ)^8249 ≤ (2627933982031/6250000000000 : ℝ)^6201 := by
    have hnat : (2606878783 : ℕ)^8249*6250000000000^6201 ≤ 2627933982031^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606878783 5000000000 2627933982031 6250000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538710119/1000000000 : ℝ)^8249 ≤ (21958364125199/50000000000000 : ℝ)^6201 := by
    have hnat : (538710119 : ℕ)^8249*50000000000000^6201 ≤ 21958364125199^6201*1000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538710119 1000000000 21958364125199 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2285425281/10000000000 : ℝ), (2606878783/5000000000 : ℝ), (538710119/1000000000 : ℝ)] ![(7018164006703/50000000000000 : ℝ), (2627933982031/6250000000000 : ℝ), (21958364125199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2285425281/10000000000 : ℝ)|^8249 ≤ (7018164006703/50000000000000 : ℝ)^6201
        have hw : |(-2285425281/10000000000 : ℝ)|=(2285425281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606878783/5000000000 : ℝ)|^8249 ≤ (2627933982031/6250000000000 : ℝ)^6201
        have hw : |(2606878783/5000000000 : ℝ)|=(2606878783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538710119/1000000000 : ℝ)|^8249 ≤ (21958364125199/50000000000000 : ℝ)^6201
        have hw : |(538710119/1000000000 : ℝ)|=(538710119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_box_9 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644145007/5000000000 : ℝ)*x 0 + (-437322849/2000000000 : ℝ)*x 1 + (1346775283/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644145007/5000000000 : ℝ)^8249 ≤ (2678026094017/6250000000000 : ℝ)^6201 := by
    have hnat : (2644145007 : ℕ)^8249*6250000000000^6201 ≤ 2678026094017^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644145007 5000000000 2678026094017 6250000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437322849/2000000000 : ℝ)^8249 ≤ (13234854869141/100000000000000 : ℝ)^6201 := by
    have hnat : (437322849 : ℕ)^8249*100000000000000^6201 ≤ 13234854869141^6201*2000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437322849 2000000000 13234854869141 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346775283/2500000000 : ℝ)^8249 ≤ (4391672762141/10000000000000 : ℝ)^6201 := by
    have hnat : (1346775283 : ℕ)^8249*10000000000000^6201 ≤ 4391672762141^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346775283 2500000000 4391672762141 10000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644145007/5000000000 : ℝ), (-437322849/2000000000 : ℝ), (1346775283/2500000000 : ℝ)] ![(2678026094017/6250000000000 : ℝ), (13234854869141/100000000000000 : ℝ), (4391672762141/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644145007/5000000000 : ℝ)|^8249 ≤ (2678026094017/6250000000000 : ℝ)^6201
        have hw : |(2644145007/5000000000 : ℝ)|=(2644145007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-437322849/2000000000 : ℝ)|^8249 ≤ (13234854869141/100000000000000 : ℝ)^6201
        have hw : |(-437322849/2000000000 : ℝ)|=(437322849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346775283/2500000000 : ℝ)|^8249 ≤ (4391672762141/10000000000000 : ℝ)^6201
        have hw : |(1346775283/2500000000 : ℝ)|=(1346775283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_box_10 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322072521/2500000000 : ℝ)*x 0 + (5387101149/10000000000 : ℝ)*x 1 + (-136663383/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322072521/2500000000 : ℝ)^8249 ≤ (42848418258769/100000000000000 : ℝ)^6201 := by
    have hnat : (1322072521 : ℕ)^8249*100000000000000^6201 ≤ 42848418258769^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322072521 2500000000 42848418258769 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387101149/10000000000 : ℝ)^8249 ≤ (43916727805769/100000000000000 : ℝ)^6201 := by
    have hnat : (5387101149 : ℕ)^8249*100000000000000^6201 ≤ 43916727805769^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387101149 10000000000 43916727805769 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136663383/625000000 : ℝ)^8249 ≤ (6617426963547/50000000000000 : ℝ)^6201 := by
    have hnat : (136663383 : ℕ)^8249*50000000000000^6201 ≤ 6617426963547^6201*625000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136663383 625000000 6617426963547 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322072521/2500000000 : ℝ), (5387101149/10000000000 : ℝ), (-136663383/625000000 : ℝ)] ![(42848418258769/100000000000000 : ℝ), (43916727805769/100000000000000 : ℝ), (6617426963547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322072521/2500000000 : ℝ)|^8249 ≤ (42848418258769/100000000000000 : ℝ)^6201
        have hw : |(1322072521/2500000000 : ℝ)|=(1322072521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387101149/10000000000 : ℝ)|^8249 ≤ (43916727805769/100000000000000 : ℝ)^6201
        have hw : |(5387101149/10000000000 : ℝ)|=(5387101149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-136663383/625000000 : ℝ)|^8249 ≤ (6617426963547/50000000000000 : ℝ)^6201
        have hw : |(-136663383/625000000 : ℝ)|=(136663383/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_box_11 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4506544711/10000000000 : ℝ)*x 0 + (4314157213/10000000000 : ℝ)*x 1 + (4314157329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4506544711/10000000000 : ℝ)^8249 ≤ (432941172689/1250000000000 : ℝ)^6201 := by
    have hnat : (4506544711 : ℕ)^8249*1250000000000^6201 ≤ 432941172689^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506544711 10000000000 432941172689 1250000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4314157213/10000000000 : ℝ)^8249 ≤ (6536470499289/20000000000000 : ℝ)^6201 := by
    have hnat : (4314157213 : ℕ)^8249*20000000000000^6201 ≤ 6536470499289^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314157213 10000000000 6536470499289 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4314157329/10000000000 : ℝ)^8249 ≤ (16341176832723/50000000000000 : ℝ)^6201 := by
    have hnat : (4314157329 : ℕ)^8249*50000000000000^6201 ≤ 16341176832723^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314157329 10000000000 16341176832723 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4506544711/10000000000 : ℝ), (4314157213/10000000000 : ℝ), (4314157329/10000000000 : ℝ)] ![(432941172689/1250000000000 : ℝ), (6536470499289/20000000000000 : ℝ), (16341176832723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4506544711/10000000000 : ℝ)|^8249 ≤ (432941172689/1250000000000 : ℝ)^6201
        have hw : |(4506544711/10000000000 : ℝ)|=(4506544711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4314157213/10000000000 : ℝ)|^8249 ≤ (6536470499289/20000000000000 : ℝ)^6201
        have hw : |(4314157213/10000000000 : ℝ)|=(4314157213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4314157329/10000000000 : ℝ)|^8249 ≤ (16341176832723/50000000000000 : ℝ)^6201
        have hw : |(4314157329/10000000000 : ℝ)|=(4314157329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_box_12 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2133745523/10000000000 : ℝ)*x 0 + (5442340667/10000000000 : ℝ)*x 1 + (210877779/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133745523/10000000000 : ℝ)^8249 ≤ (3202720411121/25000000000000 : ℝ)^6201 := by
    have hnat : (2133745523 : ℕ)^8249*25000000000000^6201 ≤ 3202720411121^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133745523 10000000000 3202720411121 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442340667/10000000000 : ℝ)^8249 ≤ (44516791553933/100000000000000 : ℝ)^6201 := by
    have hnat : (5442340667 : ℕ)^8249*100000000000000^6201 ≤ 44516791553933^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442340667 10000000000 44516791553933 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210877779/400000000 : ℝ)^8249 ≤ (21336163393671/50000000000000 : ℝ)^6201 := by
    have hnat : (210877779 : ℕ)^8249*50000000000000^6201 ≤ 21336163393671^6201*400000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210877779 400000000 21336163393671 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2133745523/10000000000 : ℝ), (5442340667/10000000000 : ℝ), (210877779/400000000 : ℝ)] ![(3202720411121/25000000000000 : ℝ), (44516791553933/100000000000000 : ℝ), (21336163393671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2133745523/10000000000 : ℝ)|^8249 ≤ (3202720411121/25000000000000 : ℝ)^6201
        have hw : |(-2133745523/10000000000 : ℝ)|=(2133745523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442340667/10000000000 : ℝ)|^8249 ≤ (44516791553933/100000000000000 : ℝ)^6201
        have hw : |(5442340667/10000000000 : ℝ)|=(5442340667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210877779/400000000 : ℝ)|^8249 ≤ (21336163393671/50000000000000 : ℝ)^6201
        have hw : |(210877779/400000000 : ℝ)|=(210877779/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_box_13 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369808979/10000000000 : ℝ)*x 0 + (-34868913/156250000 : ℝ)*x 1 + (1317986063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369808979/10000000000 : ℝ)^8249 ≤ (2186465011671/5000000000000 : ℝ)^6201 := by
    have hnat : (5369808979 : ℕ)^8249*5000000000000^6201 ≤ 2186465011671^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369808979 10000000000 2186465011671 5000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34868913/156250000 : ℝ)^8249 ≤ (679918767721/5000000000000 : ℝ)^6201 := by
    have hnat : (34868913 : ℕ)^8249*5000000000000^6201 ≤ 679918767721^6201*156250000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34868913 156250000 679918767721 5000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1317986063/2500000000 : ℝ)^8249 ≤ (10668081096547/25000000000000 : ℝ)^6201 := by
    have hnat : (1317986063 : ℕ)^8249*25000000000000^6201 ≤ 10668081096547^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317986063 2500000000 10668081096547 25000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369808979/10000000000 : ℝ), (-34868913/156250000 : ℝ), (1317986063/2500000000 : ℝ)] ![(2186465011671/5000000000000 : ℝ), (679918767721/5000000000000 : ℝ), (10668081096547/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369808979/10000000000 : ℝ)|^8249 ≤ (2186465011671/5000000000000 : ℝ)^6201
        have hw : |(5369808979/10000000000 : ℝ)|=(5369808979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34868913/156250000 : ℝ)|^8249 ≤ (679918767721/5000000000000 : ℝ)^6201
        have hw : |(-34868913/156250000 : ℝ)|=(34868913/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1317986063/2500000000 : ℝ)|^8249 ≤ (10668081096547/25000000000000 : ℝ)^6201
        have hw : |(1317986063/2500000000 : ℝ)|=(1317986063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_box_14 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684904243/5000000000 : ℝ)*x 0 + (527194449/1000000000 : ℝ)*x 1 + (-278951347/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684904243/5000000000 : ℝ)^8249 ≤ (5466161861587/12500000000000 : ℝ)^6201 := by
    have hnat : (2684904243 : ℕ)^8249*12500000000000^6201 ≤ 5466161861587^6201*5000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684904243 5000000000 5466161861587 12500000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527194449/1000000000 : ℝ)^8249 ≤ (21336163474427/50000000000000 : ℝ)^6201 := by
    have hnat : (527194449 : ℕ)^8249*50000000000000^6201 ≤ 21336163474427^6201*1000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527194449 1000000000 21336163474427 50000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (278951347/1250000000 : ℝ)^8249 ≤ (2719675628579/20000000000000 : ℝ)^6201 := by
    have hnat : (278951347 : ℕ)^8249*20000000000000^6201 ≤ 2719675628579^6201*1250000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278951347 1250000000 2719675628579 20000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684904243/5000000000 : ℝ), (527194449/1000000000 : ℝ), (-278951347/1250000000 : ℝ)] ![(5466161861587/12500000000000 : ℝ), (21336163474427/50000000000000 : ℝ), (2719675628579/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684904243/5000000000 : ℝ)|^8249 ≤ (5466161861587/12500000000000 : ℝ)^6201
        have hw : |(2684904243/5000000000 : ℝ)|=(2684904243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527194449/1000000000 : ℝ)|^8249 ≤ (21336163474427/50000000000000 : ℝ)^6201
        have hw : |(527194449/1000000000 : ℝ)|=(527194449/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-278951347/1250000000 : ℝ)|^8249 ≤ (2719675628579/20000000000000 : ℝ)^6201
        have hw : |(-278951347/1250000000 : ℝ)|=(278951347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1056_box_15 (p : ℝ) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062516759/2500000000 : ℝ)*x 0 + (4442393857/10000000000 : ℝ)*x 1 + (4442392867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062516759/2500000000 : ℝ)^8249 ≤ (32038067379187/100000000000000 : ℝ)^6201 := by
    have hnat : (1062516759 : ℕ)^8249*100000000000000^6201 ≤ 32038067379187^6201*2500000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062516759 2500000000 32038067379187 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4442393857/10000000000 : ℝ)^8249 ≤ (265476338597/781250000000 : ℝ)^6201 := by
    have hnat : (4442393857 : ℕ)^8249*781250000000^6201 ≤ 265476338597^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4442393857 10000000000 265476338597 781250000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4442392867/10000000000 : ℝ)^8249 ≤ (33980961266613/100000000000000 : ℝ)^6201 := by
    have hnat : (4442392867 : ℕ)^8249*100000000000000^6201 ≤ 33980961266613^6201*10000000000^8249 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4442392867 10000000000 33980961266613 100000000000000 8249 6201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8249/2048 : ℝ)) 8249 6201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062516759/2500000000 : ℝ), (4442393857/10000000000 : ℝ), (4442392867/10000000000 : ℝ)] ![(32038067379187/100000000000000 : ℝ), (265476338597/781250000000 : ℝ), (33980961266613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062516759/2500000000 : ℝ)|^8249 ≤ (32038067379187/100000000000000 : ℝ)^6201
        have hw : |(1062516759/2500000000 : ℝ)|=(1062516759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4442393857/10000000000 : ℝ)|^8249 ≤ (265476338597/781250000000 : ℝ)^6201
        have hw : |(4442393857/10000000000 : ℝ)|=(4442393857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4442392867/10000000000 : ℝ)|^8249 ≤ (33980961266613/100000000000000 : ℝ)^6201
        have hw : |(4442392867/10000000000 : ℝ)|=(4442392867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1056_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59233/100000 : ℝ) ∧ (79541/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (8293/10000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3499/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5619/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3499/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5619/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3499/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5619/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3499/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5619/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3499/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5619/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3499/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5619/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (5619/50000 : ℝ) ^ (1031/256 : ℝ) ≤ (7512221651015079/50000000000000000000 : ℝ) := by
    have hpowers : (5619/50000 : ℝ)^1031 ≤ (7512221651015079/50000000000000000000 : ℝ)^256 := by
      have hnat : (5619 : ℕ)^1031*50000000000000000000^256 ≤ 7512221651015079^256*50000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5619 50000 7512221651015079 50000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5619/50000 : ℝ)) (X := (7512221651015079/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3499/25000 : ℝ) ^ (1031/256 : ℝ) ≤ (9090845752014189/25000000000000000000 : ℝ) := by
    have hpowers : (3499/25000 : ℝ)^1031 ≤ (9090845752014189/25000000000000000000 : ℝ)^256 := by
      have hnat : (3499 : ℕ)^1031*25000000000000000000^256 ≤ 9090845752014189^256*25000^1031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3499 25000 9090845752014189 25000000000000000000 1031 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3499/25000 : ℝ)) (X := (9090845752014189/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007512221651015079/25000000000000000000 : ℝ) ≤ (500037301873633/500000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (25007512221651015079/25000000000000000000 : ℝ)^256 ≤ (500037301873633/500000000000000 : ℝ)^1031 := by
      have hnat : (25007512221651015079 : ℕ)^256*500000000000000^1031 ≤ 500037301873633^1031*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007512221651015079 25000000000000000000 500037301873633 500000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500037301873633/500000000000000 : ℝ)) (X := (25007512221651015079/25000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025693913155043457/50000000000000000000 : ℝ) ≤ (5000637863408333/5000000000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (50025693913155043457/50000000000000000000 : ℝ)^256 ≤ (5000637863408333/5000000000000000 : ℝ)^1031 := by
      have hnat : (50025693913155043457 : ℕ)^256*5000000000000000^1031 ≤ 5000637863408333^1031*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025693913155043457 50000000000000000000 5000637863408333 5000000000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000637863408333/5000000000000000 : ℝ)) (X := (50025693913155043457/50000000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509090845752014189/12500000000000000000 : ℝ) ≤ (312556419255021/312500000000000 : ℝ) ^ (1031/256 : ℝ) := by
    have hpowers : (12509090845752014189/12500000000000000000 : ℝ)^256 ≤ (312556419255021/312500000000000 : ℝ)^1031 := by
      have hnat : (12509090845752014189 : ℕ)^256*312500000000000^1031 ≤ 312556419255021^1031*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509090845752014189 12500000000000000000 312556419255021 312500000000000 256 1031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312556419255021/312500000000000 : ℝ)) (X := (12509090845752014189/12500000000000000000 : ℝ)) (by norm_num) 1031 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7512221651015079/50000000000000000000 : ℝ) ≤ ((1723134517103357339/1723750000000000000 : ℝ)+2*(264844672003/137900000000000 : ℝ)*(5619/50000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (1723134517103357339/1723750000000000000 : ℝ)+2*(264844672003/137900000000000 : ℝ)*(5619/50000 : ℝ)=(500037301873633/500000000000000 : ℝ) by norm_num, show 1+2*(7512221651015079/50000000000000000000 : ℝ)=(25007512221651015079/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9090845752014189/25000000000000000000 : ℝ)+(7512221651015079/50000000000000000000 : ℝ) ≤ ((1723134517103357339/1723750000000000000 : ℝ)+(264844672003/137900000000000 : ℝ)*((3499/25000 : ℝ)+(5619/50000 : ℝ)))^(1031/256 : ℝ) := by
    rw [show (1723134517103357339/1723750000000000000 : ℝ)+(264844672003/137900000000000 : ℝ)*((3499/25000 : ℝ)+(5619/50000 : ℝ))=(5000637863408333/5000000000000000 : ℝ) by norm_num, show 1+(9090845752014189/25000000000000000000 : ℝ)+(7512221651015079/50000000000000000000 : ℝ)=(50025693913155043457/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9090845752014189/25000000000000000000 : ℝ) ≤ ((1723134517103357339/1723750000000000000 : ℝ)+2*(264844672003/137900000000000 : ℝ)*(3499/25000 : ℝ))^(1031/256 : ℝ) := by
    rw [show (1723134517103357339/1723750000000000000 : ℝ)+2*(264844672003/137900000000000 : ℝ)*(3499/25000 : ℝ)=(312556419255021/312500000000000 : ℝ) by norm_num, show 1+2*(9090845752014189/25000000000000000000 : ℝ)=(12509090845752014189/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1723134517103357339/1723750000000000000 : ℝ)*(X 1 0+X 2 0)+(264844672003/137900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (5619/50000 : ℝ)) (hi := (3499/25000 : ℝ)) (c := (1723134517103357339/1723750000000000000 : ℝ)) (alpha := (264844672003/137900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1723134517103357339/1723750000000000000 : ℝ)*(X 0 1+X 2 1)+(264844672003/137900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (5619/50000 : ℝ)) (hi := (3499/25000 : ℝ)) (c := (1723134517103357339/1723750000000000000 : ℝ)) (alpha := (264844672003/137900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1723134517103357339/1723750000000000000 : ℝ)*(X 0 2+X 1 2)+(264844672003/137900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1031/256 : ℝ)) (lo := (5619/50000 : ℝ)) (hi := (3499/25000 : ℝ)) (c := (1723134517103357339/1723750000000000000 : ℝ)) (alpha := (264844672003/137900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2078896893/10000000000 : ℝ)*X 0 0+(5377501061/10000000000 : ℝ)*X 0 1+(5377502721/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2647544357/5000000000 : ℝ)*X 1 0+(-219043521/1000000000 : ℝ)*X 1 1+(2688750943/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1059017797/2000000000 : ℝ)*X 2 0+(2688751221/5000000000 : ℝ)*X 2 1+(-2190434099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((140169841/312500000 : ℝ)*X 0 0+(2162426331/5000000000 : ℝ)*X 0 1+(2162426361/5000000000 : ℝ)*X 0 2+(140169841/312500000 : ℝ)*X 1 0+(2162426331/5000000000 : ℝ)*X 1 1+(2162426361/5000000000 : ℝ)*X 1 2+(140169841/312500000 : ℝ)*X 2 0+(2162426331/5000000000 : ℝ)*X 2 1+(2162426361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2339899103/10000000000 : ℝ)*X 0 0+(1319984933/2500000000 : ℝ)*X 0 1+(1055987939/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1341037827/2500000000 : ℝ)*X 1 0+(-2228546331/10000000000 : ℝ)*X 1 1+(5279939609/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5364150987/10000000000 : ℝ)*X 2 0+(2639969959/5000000000 : ℝ)*X 2 1+(-44570927/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((853621447/2000000000 : ℝ)*X 0 0+(4433495173/10000000000 : ℝ)*X 0 1+(554186849/1250000000 : ℝ)*X 0 2+(853621447/2000000000 : ℝ)*X 1 0+(4433495173/10000000000 : ℝ)*X 1 1+(554186849/1250000000 : ℝ)*X 1 2+(853621447/2000000000 : ℝ)*X 2 0+(4433495173/10000000000 : ℝ)*X 2 1+(554186849/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2285425281/10000000000 : ℝ)*X 0 0+(2606878783/5000000000 : ℝ)*X 0 1+(538710119/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644145007/5000000000 : ℝ)*X 1 0+(-437322849/2000000000 : ℝ)*X 1 1+(1346775283/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322072521/2500000000 : ℝ)*X 2 0+(5387101149/10000000000 : ℝ)*X 2 1+(-136663383/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4506544711/10000000000 : ℝ)*X 0 0+(4314157213/10000000000 : ℝ)*X 0 1+(4314157329/10000000000 : ℝ)*X 0 2+(4506544711/10000000000 : ℝ)*X 1 0+(4314157213/10000000000 : ℝ)*X 1 1+(4314157329/10000000000 : ℝ)*X 1 2+(4506544711/10000000000 : ℝ)*X 2 0+(4314157213/10000000000 : ℝ)*X 2 1+(4314157329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2133745523/10000000000 : ℝ)*X 0 0+(5442340667/10000000000 : ℝ)*X 0 1+(210877779/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369808979/10000000000 : ℝ)*X 1 0+(-34868913/156250000 : ℝ)*X 1 1+(1317986063/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684904243/5000000000 : ℝ)*X 2 0+(527194449/1000000000 : ℝ)*X 2 1+(-278951347/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1062516759/2500000000 : ℝ)*X 0 0+(4442393857/10000000000 : ℝ)*X 0 1+(4442392867/10000000000 : ℝ)*X 0 2+(1062516759/2500000000 : ℝ)*X 1 0+(4442393857/10000000000 : ℝ)*X 1 1+(4442392867/10000000000 : ℝ)*X 1 2+(1062516759/2500000000 : ℝ)*X 2 0+(4442393857/10000000000 : ℝ)*X 2 1+(4442392867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1056_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-26813597816948778796433505392373/43093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15144527/12500000000000 : ℝ)*(upper0) + (97453011/50000000000000 : ℝ)*(upper1) + (48834703/100000000000000 : ℝ)*(upper2) + (30186149/20000000000000 : ℝ)*(upper3) + (1665957/3125000000000 : ℝ)*(upper5) + (1924078217872831/50000000000000 : ℝ)*(major0) + (1924078217872831/50000000000000 : ℝ)*(major1) + (1924078217872831/50000000000000 : ℝ)*(major2) + (15926371187/100000000000000 : ℝ)*(sp3) + (1278350898029949/25000000000000 : ℝ)*(sp4) + (1278350898029949/25000000000000 : ℝ)*(sp5) + (2556599891001893/50000000000000 : ℝ)*(sp6) + (1301816934297381/50000000000000 : ℝ)*(sp7) + (203810116011/100000000000000 : ℝ)*(sp14) + (52072995899319/2000000000000 : ℝ)*(f.failure) + (1278350898029949/25000000000000 : ℝ)*(f.sum) + (3184243746179/1723750000000000000000000000 : ℝ)*base65 + (8387592285233030791/86187500000000000000000000000000 : ℝ)*base68 + (195852345952344209/86187500000000000000000000000000 : ℝ)*base69 + (701115966964905791/86187500000000000000000000000000 : ℝ)*base72 + (14153547466553/3447500000000000000000000000 : ℝ)*base73 + (5068281711121155791/86187500000000000000000000000000 : ℝ)*base76 + (1547116346454905791/86187500000000000000000000000000 : ℝ)*base78 + (1508747410841094209/86187500000000000000000000000000 : ℝ)*base79 + (49120440665101/1723750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1496449/100000000000000000000 : ℝ)*base89 + (1496449/100000000000000000000 : ℝ)*base91 + (1496449/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59233/100000 : ℝ) ≤ (816861991366569128444560479/1379000000000000000000000000 : ℝ) := by norm_num
    linear_combination (381191721/100000000000000 : ℝ)*(lower3) + (81610699/20000000000000 : ℝ)*(upper4) + (5942997/10000000000000 : ℝ)*(upper5) + (78217951888033/2000000000000 : ℝ)*(major0) + (78217951888033/2000000000000 : ℝ)*(major1) + (78217951888033/2000000000000 : ℝ)*(major2) + (5155930712975167/100000000000000 : ℝ)*(sp0) + (5155934216285919/100000000000000 : ℝ)*(sp1) + (5155895363057567/100000000000000 : ℝ)*(sp2) + (1323041359425959/50000000000000 : ℝ)*(sp3) + (15444960389/100000000000000 : ℝ)*(sp5) + (2714909437/5000000000000 : ℝ)*(sp6) + (8767280179/50000000000000 : ℝ)*(sp7) + (947413557/5000000000000 : ℝ)*(sp12) + (661525063353069/25000000000000 : ℝ)*(f.failure) + (5155949661246307/100000000000000 : ℝ)*(f.sum) + (1260048275377/275800000000000000000000000 : ℝ)*base65 + (5395357519954187/3447500000000000000000000000000 : ℝ)*base67 + (22325695536609187/3447500000000000000000000000000 : ℝ)*base69 + (18000232828928313/3447500000000000000000000000000 : ℝ)*base72 + (11521993244511/1379000000000000000000000000 : ℝ)*base73 + (14845284724420813/3447500000000000000000000000000 : ℝ)*base76 + (4169505798664187/3447500000000000000000000000000 : ℝ)*base77 + (11771811297778313/3447500000000000000000000000000 : ℝ)*base80 + (5427043126569/1379000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (10287301/1250000000000000000000 : ℝ)*base90 + (10287301/1250000000000000000000 : ℝ)*base92 + (10287301/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79541/100000 : ℝ) ≤ (5484504003296700567303995433/6895000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35237671/100000000000000 : ℝ)*(upper0) + (11321527/20000000000000 : ℝ)*(lower3) + (29111649/50000000000000 : ℝ)*(upper4) + (4379167927635451/100000000000000 : ℝ)*(major0) + (4379167927635451/100000000000000 : ℝ)*(major1) + (4379167927635451/100000000000000 : ℝ)*(major2) + (1259968627/4000000000000 : ℝ)*(sp1) + (57739379233/100000000000000 : ℝ)*(sp2) + (30756503663/100000000000000 : ℝ)*(sp3) + (82688327/12500000000000 : ℝ)*(sp4) + (5768890394740933/100000000000000 : ℝ)*(sp8) + (2884429778515937/50000000000000 : ℝ)*(sp9) + (5768833316868317/100000000000000 : ℝ)*(sp10) + (740724910190837/25000000000000 : ℝ)*(sp11) + (740732599316753/25000000000000 : ℝ)*(f.failure) + (5768891056247549/100000000000000 : ℝ)*(f.sum) + (65347532781/53867187500000000000000000 : ℝ)*base65 + (1815859078809337389/172375000000000000000000000000000 : ℝ)*base67 + (2496374682652162611/172375000000000000000000000000000 : ℝ)*base70 + (508327951590587389/172375000000000000000000000000000 : ℝ)*base71 + (298301125584103/6895000000000000000000000000 : ℝ)*base73 + (184690105978662611/172375000000000000000000000000000 : ℝ)*base76 + (322970989398537611/172375000000000000000000000000000 : ℝ)*base78 + (2543959490210462389/172375000000000000000000000000000 : ℝ)*base79 + (378517419829/215468750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (7287063/1250000000000000000000 : ℝ)*base89 + (7287063/1250000000000000000000 : ℝ)*base91 + (7287063/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-8293/10000 : ℝ) ≤ (-71472801836058008473485773812179/86187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67746973/50000000000000 : ℝ)*(lower0) + (125550653/50000000000000 : ℝ)*(upper1) + (22236371/20000000000000 : ℝ)*(upper3) + (288838299/100000000000000 : ℝ)*(lower4) + (4413648795075771/100000000000000 : ℝ)*(major0) + (4413648795075771/100000000000000 : ℝ)*(major1) + (4413648795075771/100000000000000 : ℝ)*(major2) + (1217851309/10000000000000 : ℝ)*(sp4) + (430938063/50000000000000 : ℝ)*(sp5) + (38232358537/25000000000000 : ℝ)*(sp7) + (1467166936043381/25000000000000 : ℝ)*(sp12) + (5868679060810489/100000000000000 : ℝ)*(sp13) + (2934339961343307/50000000000000 : ℝ)*(sp14) + (3732633884509/125000000000 : ℝ)*(sp15) + (746565009260337/25000000000000 : ℝ)*(f.failure) + (2934339961343307/50000000000000 : ℝ)*(f.sum) + (26057169257597/6895000000000000000000000000 : ℝ)*base66 + (1456382789585654131/172375000000000000000000000000000 : ℝ)*base68 + (1929872208766404131/172375000000000000000000000000000 : ℝ)*base70 + (2987321548602279131/172375000000000000000000000000000 : ℝ)*base72 + (13445013909563/6895000000000000000000000000 : ℝ)*base73 + (3378261163772404131/172375000000000000000000000000000 : ℝ)*base76 + (2006396248706654131/172375000000000000000000000000000 : ℝ)*base78 + (1134225027946654131/172375000000000000000000000000000 : ℝ)*base80 + (8740389226273/6895000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (16014327/1250000000000000000000 : ℝ)*base89 + (16014327/1250000000000000000000 : ℝ)*base91 + (16014327/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1056_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3499/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59233/100000 : ℝ) else (79541/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8293/10000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1056_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1056_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13997/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59233/100000 : ℝ) else (79541/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8293/10000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1056_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1056_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1031/256 : ℝ) ≤ p) (hpb : p ≤ (8249/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73899271/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13997/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5619/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59233/100000 : ℝ) else (79541/100000 : ℝ) ≤ X j i ∧ X j i ≤ (8293/10000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1056_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

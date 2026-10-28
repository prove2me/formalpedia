-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1041_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:47:29.666784+00:00
-- url     : https://prove2.me/submissions/964e00f3-8475-4716-941d-842134a4bc72

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
theorem support_rectangle_w1041_s0_0 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5492441027/10000000000 : ℝ)*x 0 + (-41962527/156250000 : ℝ)*x 1 + (119844439/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5492441027/10000000000 : ℝ)^4117 ≤ (5630144043729/12500000000000 : ℝ)^3093 := by
    have hnat : (5492441027 : ℕ)^4117*12500000000000^3093 ≤ 5630144043729^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492441027 10000000000 5630144043729 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41962527/156250000 : ℝ)^4117 ≤ (868929069679/5000000000000 : ℝ)^3093 := by
    have hnat : (41962527 : ℕ)^4117*5000000000000^3093 ≤ 868929069679^3093*156250000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41962527 156250000 868929069679 5000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119844439/250000000 : ℝ)^4117 ≤ (37580266245613/100000000000000 : ℝ)^3093 := by
    have hnat : (119844439 : ℕ)^4117*100000000000000^3093 ≤ 37580266245613^3093*250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119844439 250000000 37580266245613 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5492441027/10000000000 : ℝ), (-41962527/156250000 : ℝ), (119844439/250000000 : ℝ)] ![(5630144043729/12500000000000 : ℝ), (868929069679/5000000000000 : ℝ), (37580266245613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5492441027/10000000000 : ℝ)|^4117 ≤ (5630144043729/12500000000000 : ℝ)^3093
        have hw : |(5492441027/10000000000 : ℝ)|=(5492441027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41962527/156250000 : ℝ)|^4117 ≤ (868929069679/5000000000000 : ℝ)^3093
        have hw : |(-41962527/156250000 : ℝ)|=(41962527/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119844439/250000000 : ℝ)|^4117 ≤ (37580266245613/100000000000000 : ℝ)^3093
        have hw : |(119844439/250000000 : ℝ)|=(119844439/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s0_1 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5497941253/10000000000 : ℝ)*x 0 + (1194855717/2500000000 : ℝ)*x 1 + (-674001279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5497941253/10000000000 : ℝ)^4117 ≤ (45101200211019/100000000000000 : ℝ)^3093 := by
    have hnat : (5497941253 : ℕ)^4117*100000000000000^3093 ≤ 45101200211019^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497941253 10000000000 45101200211019 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1194855717/2500000000 : ℝ)^4117 ≤ (37430552619481/100000000000000 : ℝ)^3093 := by
    have hnat : (1194855717 : ℕ)^4117*100000000000000^3093 ≤ 37430552619481^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194855717 2500000000 37430552619481 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674001279/2500000000 : ℝ)^4117 ≤ (8734123575053/50000000000000 : ℝ)^3093 := by
    have hnat : (674001279 : ℕ)^4117*50000000000000^3093 ≤ 8734123575053^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674001279 2500000000 8734123575053 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5497941253/10000000000 : ℝ), (1194855717/2500000000 : ℝ), (-674001279/2500000000 : ℝ)] ![(45101200211019/100000000000000 : ℝ), (37430552619481/100000000000000 : ℝ), (8734123575053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5497941253/10000000000 : ℝ)|^4117 ≤ (45101200211019/100000000000000 : ℝ)^3093
        have hw : |(5497941253/10000000000 : ℝ)|=(5497941253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1194855717/2500000000 : ℝ)|^4117 ≤ (37430552619481/100000000000000 : ℝ)^3093
        have hw : |(1194855717/2500000000 : ℝ)|=(1194855717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-674001279/2500000000 : ℝ)|^4117 ≤ (8734123575053/50000000000000 : ℝ)^3093
        have hw : |(-674001279/2500000000 : ℝ)|=(674001279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s0_2 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-241205523/1250000000 : ℝ)*x 0 + (96028261/200000000 : ℝ)*x 1 + (377683853/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (241205523/1250000000 : ℝ)^4117 ≤ (11192318741679/100000000000000 : ℝ)^3093 := by
    have hnat : (241205523 : ℕ)^4117*100000000000000^3093 ≤ 11192318741679^3093*1250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241205523 1250000000 11192318741679 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96028261/200000000 : ℝ)^4117 ≤ (9414990458707/25000000000000 : ℝ)^3093 := by
    have hnat : (96028261 : ℕ)^4117*25000000000000^3093 ≤ 9414990458707^3093*200000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96028261 200000000 9414990458707 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (377683853/625000000 : ℝ)^4117 ≤ (25573859701299/50000000000000 : ℝ)^3093 := by
    have hnat : (377683853 : ℕ)^4117*50000000000000^3093 ≤ 25573859701299^3093*625000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377683853 625000000 25573859701299 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-241205523/1250000000 : ℝ), (96028261/200000000 : ℝ), (377683853/625000000 : ℝ)] ![(11192318741679/100000000000000 : ℝ), (9414990458707/25000000000000 : ℝ), (25573859701299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-241205523/1250000000 : ℝ)|^4117 ≤ (11192318741679/100000000000000 : ℝ)^3093
        have hw : |(-241205523/1250000000 : ℝ)|=(241205523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(96028261/200000000 : ℝ)|^4117 ≤ (9414990458707/25000000000000 : ℝ)^3093
        have hw : |(96028261/200000000 : ℝ)|=(96028261/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(377683853/625000000 : ℝ)|^4117 ≤ (25573859701299/50000000000000 : ℝ)^3093
        have hw : |(377683853/625000000 : ℝ)|=(377683853/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s0_3 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5166958511/10000000000 : ℝ)*x 0 + (-5615381/40000000 : ℝ)*x 1 + (1510735459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5166958511/10000000000 : ℝ)^4117 ≤ (5190457565679/12500000000000 : ℝ)^3093 := by
    have hnat : (5166958511 : ℕ)^4117*12500000000000^3093 ≤ 5190457565679^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5166958511 10000000000 5190457565679 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5615381/40000000 : ℝ)^4117 ≤ (293144717709/4000000000000 : ℝ)^3093 := by
    have hnat : (5615381 : ℕ)^4117*4000000000000^3093 ≤ 293144717709^3093*40000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5615381 40000000 293144717709 4000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1510735459/2500000000 : ℝ)^4117 ≤ (1022954430413/2000000000000 : ℝ)^3093 := by
    have hnat : (1510735459 : ℕ)^4117*2000000000000^3093 ≤ 1022954430413^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510735459 2500000000 1022954430413 2000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5166958511/10000000000 : ℝ), (-5615381/40000000 : ℝ), (1510735459/2500000000 : ℝ)] ![(5190457565679/12500000000000 : ℝ), (293144717709/4000000000000 : ℝ), (1022954430413/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5166958511/10000000000 : ℝ)|^4117 ≤ (5190457565679/12500000000000 : ℝ)^3093
        have hw : |(5166958511/10000000000 : ℝ)|=(5166958511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5615381/40000000 : ℝ)|^4117 ≤ (293144717709/4000000000000 : ℝ)^3093
        have hw : |(-5615381/40000000 : ℝ)|=(5615381/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1510735459/2500000000 : ℝ)|^4117 ≤ (1022954430413/2000000000000 : ℝ)^3093
        have hw : |(1510735459/2500000000 : ℝ)|=(1510735459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s0_4 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5166954327/10000000000 : ℝ)*x 0 + (1208589163/2000000000 : ℝ)*x 1 + (-35096131/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5166954327/10000000000 : ℝ)^4117 ≤ (4152361576923/10000000000000 : ℝ)^3093 := by
    have hnat : (5166954327 : ℕ)^4117*10000000000000^3093 ≤ 4152361576923^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5166954327 10000000000 4152361576923 10000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1208589163/2000000000 : ℝ)^4117 ≤ (25573883174503/50000000000000 : ℝ)^3093 := by
    have hnat : (1208589163 : ℕ)^4117*50000000000000^3093 ≤ 25573883174503^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208589163 2000000000 25573883174503 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35096131/250000000 : ℝ)^4117 ≤ (3664308936619/50000000000000 : ℝ)^3093 := by
    have hnat : (35096131 : ℕ)^4117*50000000000000^3093 ≤ 3664308936619^3093*250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35096131 250000000 3664308936619 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5166954327/10000000000 : ℝ), (1208589163/2000000000 : ℝ), (-35096131/250000000 : ℝ)] ![(4152361576923/10000000000000 : ℝ), (25573883174503/50000000000000 : ℝ), (3664308936619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5166954327/10000000000 : ℝ)|^4117 ≤ (4152361576923/10000000000000 : ℝ)^3093
        have hw : |(5166954327/10000000000 : ℝ)|=(5166954327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1208589163/2000000000 : ℝ)|^4117 ≤ (25573883174503/50000000000000 : ℝ)^3093
        have hw : |(1208589163/2000000000 : ℝ)|=(1208589163/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35096131/250000000 : ℝ)|^4117 ≤ (3664308936619/50000000000000 : ℝ)^3093
        have hw : |(-35096131/250000000 : ℝ)|=(35096131/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s0_5 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263744403/625000000 : ℝ)*x 0 + (2807848709/5000000000 : ℝ)*x 1 + (3194538583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263744403/625000000 : ℝ)^4117 ≤ (31714094601643/100000000000000 : ℝ)^3093 := by
    have hnat : (263744403 : ℕ)^4117*100000000000000^3093 ≤ 31714094601643^3093*625000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263744403 625000000 31714094601643 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2807848709/5000000000 : ℝ)^4117 ≤ (46391534968309/100000000000000 : ℝ)^3093 := by
    have hnat : (2807848709 : ℕ)^4117*100000000000000^3093 ≤ 46391534968309^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2807848709 5000000000 46391534968309 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3194538583/10000000000 : ℝ)^4117 ≤ (21894370423753/100000000000000 : ℝ)^3093 := by
    have hnat : (3194538583 : ℕ)^4117*100000000000000^3093 ≤ 21894370423753^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3194538583 10000000000 21894370423753 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263744403/625000000 : ℝ), (2807848709/5000000000 : ℝ), (3194538583/10000000000 : ℝ)] ![(31714094601643/100000000000000 : ℝ), (46391534968309/100000000000000 : ℝ), (21894370423753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263744403/625000000 : ℝ)|^4117 ≤ (31714094601643/100000000000000 : ℝ)^3093
        have hw : |(263744403/625000000 : ℝ)|=(263744403/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2807848709/5000000000 : ℝ)|^4117 ≤ (46391534968309/100000000000000 : ℝ)^3093
        have hw : |(2807848709/5000000000 : ℝ)|=(2807848709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3194538583/10000000000 : ℝ)|^4117 ≤ (21894370423753/100000000000000 : ℝ)^3093
        have hw : |(3194538583/10000000000 : ℝ)|=(3194538583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1041_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (0 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28207/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base43 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*X 2 1) ≤ (0 : ℝ) := by
    linarith only [sign0]
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
  have hpowlo : (0 : ℝ) ^ (8233/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8233 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8233*1^2048 ≤ 0^2048*1^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8233/2048 : ℝ) ≤ (1256734093918782357/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8233 ≤ (1256734093918782357/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8233*50000000000000000000^2048 ≤ 1256734093918782357^2048*5^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1256734093918782357 50000000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1256734093918782357/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8233 := by
      have hnat : (1 : ℕ)^2048*1^8233 ≤ 1^8233*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51256734093918782357/50000000000000000000 : ℝ) ≤ (10061941998053311/10000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (51256734093918782357/50000000000000000000 : ℝ)^2048 ≤ (10061941998053311/10000000000000000 : ℝ)^8233 := by
      have hnat : (51256734093918782357 : ℕ)^2048*10000000000000000^8233 ≤ 10061941998053311^8233*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51256734093918782357 50000000000000000000 10061941998053311 10000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10061941998053311/10000000000000000 : ℝ)) (X := (51256734093918782357/50000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26256734093918782357/25000000000000000000 : ℝ) ≤ (5061941998053311/5000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (26256734093918782357/25000000000000000000 : ℝ)^2048 ≤ (5061941998053311/5000000000000000 : ℝ)^8233 := by
      have hnat : (26256734093918782357 : ℕ)^2048*5000000000000000^8233 ≤ 5061941998053311^8233*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26256734093918782357 25000000000000000000 5061941998053311 5000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5061941998053311/5000000000000000 : ℝ)) (X := (26256734093918782357/25000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(61941998053311/4000000000000000 : ℝ)*(0 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(61941998053311/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1256734093918782357/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(61941998053311/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8233/2048 : ℝ) := by
    rw [show (1 : ℝ)+(61941998053311/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10061941998053311/10000000000000000 : ℝ) by norm_num, show 1+(1256734093918782357/50000000000000000000 : ℝ)+(0 : ℝ)=(51256734093918782357/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1256734093918782357/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(61941998053311/4000000000000000 : ℝ)*(2/5 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(61941998053311/4000000000000000 : ℝ)*(2/5 : ℝ)=(5061941998053311/5000000000000000 : ℝ) by norm_num, show 1+2*(1256734093918782357/50000000000000000000 : ℝ)=(26256734093918782357/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(61941998053311/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61941998053311/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(61941998053311/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61941998053311/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(61941998053311/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61941998053311/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5492441027/10000000000 : ℝ)*X 1 0+(-41962527/156250000 : ℝ)*X 1 1+(119844439/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s0_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5497941253/10000000000 : ℝ)*X 2 0+(1194855717/2500000000 : ℝ)*X 2 1+(-674001279/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s0_1 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-241205523/1250000000 : ℝ)*X 0 0+(96028261/200000000 : ℝ)*X 0 1+(377683853/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s0_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5166958511/10000000000 : ℝ)*X 1 0+(-5615381/40000000 : ℝ)*X 1 1+(1510735459/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s0_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5166954327/10000000000 : ℝ)*X 2 0+(1208589163/2000000000 : ℝ)*X 2 1+(-35096131/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s0_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((263744403/625000000 : ℝ)*X 0 0+(2807848709/5000000000 : ℝ)*X 0 1+(3194538583/10000000000 : ℝ)*X 0 2+(263744403/625000000 : ℝ)*X 1 0+(2807848709/5000000000 : ℝ)*X 1 1+(3194538583/10000000000 : ℝ)*X 1 2+(263744403/625000000 : ℝ)*X 2 0+(2807848709/5000000000 : ℝ)*X 2 1+(3194538583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s0_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(base43) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41165295501155824209027/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (815131317/100000000000000 : ℝ)*(base19) + (549332243/50000000000000 : ℝ)*(base23) + (97621357/12500000000000 : ℝ)*(base39) + (59044121/50000000000000 : ℝ)*(upper2) + (13398507/4000000000000 : ℝ)*(upper5) + (30461959446373/5000000000000 : ℝ)*(major0) + (30461959446373/5000000000000 : ℝ)*(major1) + (152309601989151/25000000000000 : ℝ)*(major2) + (2703365229/100000000000000 : ℝ)*(sp0) + (1872366071/100000000000000 : ℝ)*(sp1) + (402726693041411/50000000000000 : ℝ)*(sp2) + (201362466896569/25000000000000 : ℝ)*(sp3) + (805451196023121/100000000000000 : ℝ)*(sp4) + (413024073583587/100000000000000 : ℝ)*(sp5) + (413024073583587/100000000000000 : ℝ)*(f.failure) + (402727083526839/50000000000000 : ℝ)*(f.sum) + (77172391652003/12500000000000000000000000000 : ℝ)*base66 + (218984795028961/100000000000000000000000000000 : ℝ)*base67 + (92770857948997/20000000000000000000000000000 : ℝ)*base70 + (46790877871039/100000000000000000000000000000 : ℝ)*base72 + (10205559272997/12500000000000000000000000000 : ℝ)*base73 + (96833524348997/20000000000000000000000000000 : ℝ)*base76 + (170887470528997/20000000000000000000000000000 : ℝ)*base78 + (9366272588997/20000000000000000000000000000 : ℝ)*base80 + (4610939858997/10000000000000000000000000000 : ℝ)*base82 + (183313/39062500000000000000 : ℝ)*base89 + (183313/39062500000000000000 : ℝ)*base91 + (183313/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1041_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28207/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1041_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1041_s1_0 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2136095017/10000000000 : ℝ)*x 0 + (5729310647/10000000000 : ℝ)*x 1 + (622563417/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136095017/10000000000 : ℝ)^4117 ≤ (800862501171/6250000000000 : ℝ)^3093 := by
    have hnat : (2136095017 : ℕ)^4117*6250000000000^3093 ≤ 800862501171^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136095017 10000000000 800862501171 6250000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5729310647/10000000000 : ℝ)^4117 ≤ (23822497414033/50000000000000 : ℝ)^3093 := by
    have hnat : (5729310647 : ℕ)^4117*50000000000000^3093 ≤ 23822497414033^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5729310647 10000000000 23822497414033 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (622563417/1250000000 : ℝ)^4117 ≤ (39541205142047/100000000000000 : ℝ)^3093 := by
    have hnat : (622563417 : ℕ)^4117*100000000000000^3093 ≤ 39541205142047^3093*1250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622563417 1250000000 39541205142047 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2136095017/10000000000 : ℝ), (5729310647/10000000000 : ℝ), (622563417/1250000000 : ℝ)] ![(800862501171/6250000000000 : ℝ), (23822497414033/50000000000000 : ℝ), (39541205142047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2136095017/10000000000 : ℝ)|^4117 ≤ (800862501171/6250000000000 : ℝ)^3093
        have hw : |(-2136095017/10000000000 : ℝ)|=(2136095017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5729310647/10000000000 : ℝ)|^4117 ≤ (23822497414033/50000000000000 : ℝ)^3093
        have hw : |(5729310647/10000000000 : ℝ)|=(5729310647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(622563417/1250000000 : ℝ)|^4117 ≤ (39541205142047/100000000000000 : ℝ)^3093
        have hw : |(622563417/1250000000 : ℝ)|=(622563417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s1_1 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21698777/40000000 : ℝ)*x 0 + (-2542337029/10000000000 : ℝ)*x 1 + (4980507657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21698777/40000000 : ℝ)^4117 ≤ (2768948380339/6250000000000 : ℝ)^3093 := by
    have hnat : (21698777 : ℕ)^4117*6250000000000^3093 ≤ 2768948380339^3093*40000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21698777 40000000 2768948380339 6250000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2542337029/10000000000 : ℝ)^4117 ≤ (16155617370111/100000000000000 : ℝ)^3093 := by
    have hnat : (2542337029 : ℕ)^4117*100000000000000^3093 ≤ 16155617370111^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542337029 10000000000 16155617370111 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4980507657/10000000000 : ℝ)^4117 ≤ (19770604267127/50000000000000 : ℝ)^3093 := by
    have hnat : (4980507657 : ℕ)^4117*50000000000000^3093 ≤ 19770604267127^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4980507657 10000000000 19770604267127 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21698777/40000000 : ℝ), (-2542337029/10000000000 : ℝ), (4980507657/10000000000 : ℝ)] ![(2768948380339/6250000000000 : ℝ), (16155617370111/100000000000000 : ℝ), (19770604267127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21698777/40000000 : ℝ)|^4117 ≤ (2768948380339/6250000000000 : ℝ)^3093
        have hw : |(21698777/40000000 : ℝ)|=(21698777/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2542337029/10000000000 : ℝ)|^4117 ≤ (16155617370111/100000000000000 : ℝ)^3093
        have hw : |(-2542337029/10000000000 : ℝ)|=(2542337029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4980507657/10000000000 : ℝ)|^4117 ≤ (19770604267127/50000000000000 : ℝ)^3093
        have hw : |(4980507657/10000000000 : ℝ)|=(4980507657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s1_2 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5424694627/10000000000 : ℝ)*x 0 + (4980507183/10000000000 : ℝ)*x 1 + (-2542337137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5424694627/10000000000 : ℝ)^4117 ≤ (22151589091853/50000000000000 : ℝ)^3093 := by
    have hnat : (5424694627 : ℕ)^4117*50000000000000^3093 ≤ 22151589091853^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424694627 10000000000 22151589091853 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4980507183/10000000000 : ℝ)^4117 ≤ (39541203525201/100000000000000 : ℝ)^3093 := by
    have hnat : (4980507183 : ℕ)^4117*100000000000000^3093 ≤ 39541203525201^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4980507183 10000000000 39541203525201 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2542337137/10000000000 : ℝ)^4117 ≤ (2019452285453/12500000000000 : ℝ)^3093 := by
    have hnat : (2542337137 : ℕ)^4117*12500000000000^3093 ≤ 2019452285453^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542337137 10000000000 2019452285453 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5424694627/10000000000 : ℝ), (4980507183/10000000000 : ℝ), (-2542337137/10000000000 : ℝ)] ![(22151589091853/50000000000000 : ℝ), (39541203525201/100000000000000 : ℝ), (2019452285453/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5424694627/10000000000 : ℝ)|^4117 ≤ (22151589091853/50000000000000 : ℝ)^3093
        have hw : |(5424694627/10000000000 : ℝ)|=(5424694627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4980507183/10000000000 : ℝ)|^4117 ≤ (39541203525201/100000000000000 : ℝ)^3093
        have hw : |(4980507183/10000000000 : ℝ)|=(4980507183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2542337137/10000000000 : ℝ)|^4117 ≤ (2019452285453/12500000000000 : ℝ)^3093
        have hw : |(-2542337137/10000000000 : ℝ)|=(2542337137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s1_3 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2162943811/5000000000 : ℝ)*x 0 + (3657846189/10000000000 : ℝ)*x 1 + (5118115329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162943811/5000000000 : ℝ)^4117 ≤ (32778615272541/100000000000000 : ℝ)^3093 := by
    have hnat : (2162943811 : ℕ)^4117*100000000000000^3093 ≤ 32778615272541^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162943811 5000000000 32778615272541 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3657846189/10000000000 : ℝ)^4117 ≤ (13109689964821/50000000000000 : ℝ)^3093 := by
    have hnat : (3657846189 : ℕ)^4117*50000000000000^3093 ≤ 13109689964821^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3657846189 10000000000 13109689964821 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5118115329/10000000000 : ℝ)^4117 ≤ (41002004777709/100000000000000 : ℝ)^3093 := by
    have hnat : (5118115329 : ℕ)^4117*100000000000000^3093 ≤ 41002004777709^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5118115329 10000000000 41002004777709 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162943811/5000000000 : ℝ), (3657846189/10000000000 : ℝ), (5118115329/10000000000 : ℝ)] ![(32778615272541/100000000000000 : ℝ), (13109689964821/50000000000000 : ℝ), (41002004777709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162943811/5000000000 : ℝ)|^4117 ≤ (32778615272541/100000000000000 : ℝ)^3093
        have hw : |(2162943811/5000000000 : ℝ)|=(2162943811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3657846189/10000000000 : ℝ)|^4117 ≤ (13109689964821/50000000000000 : ℝ)^3093
        have hw : |(3657846189/10000000000 : ℝ)|=(3657846189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5118115329/10000000000 : ℝ)|^4117 ≤ (41002004777709/100000000000000 : ℝ)^3093
        have hw : |(5118115329/10000000000 : ℝ)|=(5118115329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s1_4 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2137056473/10000000000 : ℝ)*x 0 + (623890951/1250000000 : ℝ)*x 1 + (1429617759/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2137056473/10000000000 : ℝ)^4117 ≤ (12821477523411/100000000000000 : ℝ)^3093 := by
    have hnat : (2137056473 : ℕ)^4117*100000000000000^3093 ≤ 12821477523411^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137056473 10000000000 12821477523411 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623890951/1250000000 : ℝ)^4117 ≤ (39653475757251/100000000000000 : ℝ)^3093 := by
    have hnat : (623890951 : ℕ)^4117*100000000000000^3093 ≤ 39653475757251^3093*1250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623890951 1250000000 39653475757251 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1429617759/2500000000 : ℝ)^4117 ≤ (23762523351457/50000000000000 : ℝ)^3093 := by
    have hnat : (1429617759 : ℕ)^4117*50000000000000^3093 ≤ 23762523351457^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1429617759 2500000000 23762523351457 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2137056473/10000000000 : ℝ), (623890951/1250000000 : ℝ), (1429617759/2500000000 : ℝ)] ![(12821477523411/100000000000000 : ℝ), (39653475757251/100000000000000 : ℝ), (23762523351457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2137056473/10000000000 : ℝ)|^4117 ≤ (12821477523411/100000000000000 : ℝ)^3093
        have hw : |(-2137056473/10000000000 : ℝ)|=(2137056473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623890951/1250000000 : ℝ)|^4117 ≤ (39653475757251/100000000000000 : ℝ)^3093
        have hw : |(623890951/1250000000 : ℝ)|=(623890951/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1429617759/2500000000 : ℝ)|^4117 ≤ (23762523351457/50000000000000 : ℝ)^3093
        have hw : |(1429617759/2500000000 : ℝ)|=(1429617759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s1_5 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (130842773/250000000 : ℝ)*x 0 + (-1804372107/10000000000 : ℝ)*x 1 + (5718472177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130842773/250000000 : ℝ)^4117 ≤ (1319976033323/3125000000000 : ℝ)^3093 := by
    have hnat : (130842773 : ℕ)^4117*3125000000000^3093 ≤ 1319976033323^3093*250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130842773 250000000 1319976033323 3125000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1804372107/10000000000 : ℝ)^4117 ≤ (5117853795263/50000000000000 : ℝ)^3093 := by
    have hnat : (1804372107 : ℕ)^4117*50000000000000^3093 ≤ 5117853795263^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1804372107 10000000000 5117853795263 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5718472177/10000000000 : ℝ)^4117 ≤ (9505011864989/20000000000000 : ℝ)^3093 := by
    have hnat : (5718472177 : ℕ)^4117*20000000000000^3093 ≤ 9505011864989^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5718472177 10000000000 9505011864989 20000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(130842773/250000000 : ℝ), (-1804372107/10000000000 : ℝ), (5718472177/10000000000 : ℝ)] ![(1319976033323/3125000000000 : ℝ), (5117853795263/50000000000000 : ℝ), (9505011864989/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(130842773/250000000 : ℝ)|^4117 ≤ (1319976033323/3125000000000 : ℝ)^3093
        have hw : |(130842773/250000000 : ℝ)|=(130842773/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1804372107/10000000000 : ℝ)|^4117 ≤ (5117853795263/50000000000000 : ℝ)^3093
        have hw : |(-1804372107/10000000000 : ℝ)|=(1804372107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5718472177/10000000000 : ℝ)|^4117 ≤ (9505011864989/20000000000000 : ℝ)^3093
        have hw : |(5718472177/10000000000 : ℝ)|=(5718472177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s1_6 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1046741809/2000000000 : ℝ)*x 0 + (1143694847/2000000000 : ℝ)*x 1 + (-22554647/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046741809/2000000000 : ℝ)^4117 ≤ (21119606462031/50000000000000 : ℝ)^3093 := by
    have hnat : (1046741809 : ℕ)^4117*50000000000000^3093 ≤ 21119606462031^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046741809 2000000000 21119606462031 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1143694847/2000000000 : ℝ)^4117 ≤ (5940635261383/12500000000000 : ℝ)^3093 := by
    have hnat : (1143694847 : ℕ)^4117*12500000000000^3093 ≤ 5940635261383^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143694847 2000000000 5940635261383 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22554647/125000000 : ℝ)^4117 ≤ (12794631213/125000000000 : ℝ)^3093 := by
    have hnat : (22554647 : ℕ)^4117*125000000000^3093 ≤ 12794631213^3093*125000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22554647 125000000 12794631213 125000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046741809/2000000000 : ℝ), (1143694847/2000000000 : ℝ), (-22554647/125000000 : ℝ)] ![(21119606462031/50000000000000 : ℝ), (5940635261383/12500000000000 : ℝ), (12794631213/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046741809/2000000000 : ℝ)|^4117 ≤ (21119606462031/50000000000000 : ℝ)^3093
        have hw : |(1046741809/2000000000 : ℝ)|=(1046741809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1143694847/2000000000 : ℝ)|^4117 ≤ (5940635261383/12500000000000 : ℝ)^3093
        have hw : |(1143694847/2000000000 : ℝ)|=(1143694847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-22554647/125000000 : ℝ)|^4117 ≤ (12794631213/125000000000 : ℝ)^3093
        have hw : |(-22554647/125000000 : ℝ)|=(22554647/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s1_7 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2163879783/5000000000 : ℝ)*x 0 + (5097401007/10000000000 : ℝ)*x 1 + (3678982437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163879783/5000000000 : ℝ)^4117 ≤ (16398748468477/50000000000000 : ℝ)^3093 := by
    have hnat : (2163879783 : ℕ)^4117*50000000000000^3093 ≤ 16398748468477^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163879783 5000000000 16398748468477 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5097401007/10000000000 : ℝ)^4117 ≤ (20390633828787/50000000000000 : ℝ)^3093 := by
    have hnat : (5097401007 : ℕ)^4117*50000000000000^3093 ≤ 20390633828787^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5097401007 10000000000 20390633828787 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3678982437/10000000000 : ℝ)^4117 ≤ (26421235388187/100000000000000 : ℝ)^3093 := by
    have hnat : (3678982437 : ℕ)^4117*100000000000000^3093 ≤ 26421235388187^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3678982437 10000000000 26421235388187 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163879783/5000000000 : ℝ), (5097401007/10000000000 : ℝ), (3678982437/10000000000 : ℝ)] ![(16398748468477/50000000000000 : ℝ), (20390633828787/50000000000000 : ℝ), (26421235388187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163879783/5000000000 : ℝ)|^4117 ≤ (16398748468477/50000000000000 : ℝ)^3093
        have hw : |(2163879783/5000000000 : ℝ)|=(2163879783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5097401007/10000000000 : ℝ)|^4117 ≤ (20390633828787/50000000000000 : ℝ)^3093
        have hw : |(5097401007/10000000000 : ℝ)|=(5097401007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3678982437/10000000000 : ℝ)|^4117 ≤ (26421235388187/100000000000000 : ℝ)^3093
        have hw : |(3678982437/10000000000 : ℝ)|=(3678982437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1041_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28207/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5067/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2091/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28207/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28207/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28207/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28207/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28207/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28207/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
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
  have hpowlo : (0 : ℝ) ^ (8233/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8233 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8233*1^2048 ≤ 0^2048*1^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (28207/100000 : ℝ) ^ (8233/2048 : ℝ) ≤ (308598635344663537/50000000000000000000 : ℝ) := by
    have hpowers : (28207/100000 : ℝ)^8233 ≤ (308598635344663537/50000000000000000000 : ℝ)^2048 := by
      have hnat : (28207 : ℕ)^8233*50000000000000000000^2048 ≤ 308598635344663537^2048*100000^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28207 100000 308598635344663537 50000000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28207/100000 : ℝ)) (X := (308598635344663537/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8233 := by
      have hnat : (1 : ℕ)^2048*1^8233 ≤ 1^8233*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50308598635344663537/50000000000000000000 : ℝ) ≤ (10015317625481959/10000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (50308598635344663537/50000000000000000000 : ℝ)^2048 ≤ (10015317625481959/10000000000000000 : ℝ)^8233 := by
      have hnat : (50308598635344663537 : ℕ)^2048*10000000000000000^8233 ≤ 10015317625481959^8233*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50308598635344663537 50000000000000000000 10015317625481959 10000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015317625481959/10000000000000000 : ℝ)) (X := (50308598635344663537/50000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25308598635344663537/25000000000000000000 : ℝ) ≤ (5015317625481959/5000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (25308598635344663537/25000000000000000000 : ℝ)^2048 ≤ (5015317625481959/5000000000000000 : ℝ)^8233 := by
      have hnat : (25308598635344663537 : ℕ)^2048*5000000000000000^8233 ≤ 5015317625481959^8233*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25308598635344663537 25000000000000000000 5015317625481959 5000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015317625481959/5000000000000000 : ℝ)) (X := (25308598635344663537/25000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15317625481959/2820700000000000 : ℝ)*(0 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(15317625481959/2820700000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(308598635344663537/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15317625481959/2820700000000000 : ℝ)*((28207/100000 : ℝ)+(0 : ℝ)))^(8233/2048 : ℝ) := by
    rw [show (1 : ℝ)+(15317625481959/2820700000000000 : ℝ)*((28207/100000 : ℝ)+(0 : ℝ))=(10015317625481959/10000000000000000 : ℝ) by norm_num, show 1+(308598635344663537/50000000000000000000 : ℝ)+(0 : ℝ)=(50308598635344663537/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(308598635344663537/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15317625481959/2820700000000000 : ℝ)*(28207/100000 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(15317625481959/2820700000000000 : ℝ)*(28207/100000 : ℝ)=(5015317625481959/5000000000000000 : ℝ) by norm_num, show 1+2*(308598635344663537/50000000000000000000 : ℝ)=(25308598635344663537/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15317625481959/2820700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (28207/100000 : ℝ)) (c := (1 : ℝ)) (alpha := (15317625481959/2820700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15317625481959/2820700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (28207/100000 : ℝ)) (c := (1 : ℝ)) (alpha := (15317625481959/2820700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15317625481959/2820700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (28207/100000 : ℝ)) (c := (1 : ℝ)) (alpha := (15317625481959/2820700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2136095017/10000000000 : ℝ)*X 0 0+(5729310647/10000000000 : ℝ)*X 0 1+(622563417/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((21698777/40000000 : ℝ)*X 1 0+(-2542337029/10000000000 : ℝ)*X 1 1+(4980507657/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5424694627/10000000000 : ℝ)*X 2 0+(4980507183/10000000000 : ℝ)*X 2 1+(-2542337137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2162943811/5000000000 : ℝ)*X 0 0+(3657846189/10000000000 : ℝ)*X 0 1+(5118115329/10000000000 : ℝ)*X 0 2+(2162943811/5000000000 : ℝ)*X 1 0+(3657846189/10000000000 : ℝ)*X 1 1+(5118115329/10000000000 : ℝ)*X 1 2+(2162943811/5000000000 : ℝ)*X 2 0+(3657846189/10000000000 : ℝ)*X 2 1+(5118115329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2137056473/10000000000 : ℝ)*X 0 0+(623890951/1250000000 : ℝ)*X 0 1+(1429617759/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((130842773/250000000 : ℝ)*X 1 0+(-1804372107/10000000000 : ℝ)*X 1 1+(5718472177/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1046741809/2000000000 : ℝ)*X 2 0+(1143694847/2000000000 : ℝ)*X 2 1+(-22554647/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2163879783/5000000000 : ℝ)*X 0 0+(5097401007/10000000000 : ℝ)*X 0 1+(3678982437/10000000000 : ℝ)*X 0 2+(2163879783/5000000000 : ℝ)*X 1 0+(5097401007/10000000000 : ℝ)*X 1 1+(3678982437/10000000000 : ℝ)*X 1 2+(2163879783/5000000000 : ℝ)*X 2 0+(5097401007/10000000000 : ℝ)*X 2 1+(3678982437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (390388414613643265747701/141035000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6539413/10000000000000 : ℝ)*(base1) + (318728369/50000000000000 : ℝ)*(base19) + (730267913/100000000000000 : ℝ)*(base23) + (74028473/100000000000000 : ℝ)*(upper3) + (31761541/50000000000000 : ℝ)*(upper5) + (1010139552187713/100000000000000 : ℝ)*(major0) + (1010139552187713/100000000000000 : ℝ)*(major1) + (1010139552187713/100000000000000 : ℝ)*(major2) + (5341869880937/400000000000 : ℝ)*(sp0) + (667735119830397/50000000000000 : ℝ)*(sp1) + (1335470146849619/100000000000000 : ℝ)*(sp2) + (342403290077749/50000000000000 : ℝ)*(sp3) + (868069353/25000000000000 : ℝ)*(sp4) + (1489440759/100000000000000 : ℝ)*(sp7) + (342404067495193/50000000000000 : ℝ)*(f.failure) + (333867719279383/25000000000000 : ℝ)*(f.sum) + (462626203782073/141035000000000000000000000000 : ℝ)*base66 + (1105775017489903/282070000000000000000000000000 : ℝ)*base68 + (1249456870979223/282070000000000000000000000000 : ℝ)*base70 + (2059775012889733/282070000000000000000000000000 : ℝ)*base72 + (95291949678387/35258750000000000000000000000 : ℝ)*base74 + (3042633072109043/282070000000000000000000000000 : ℝ)*base76 + (1496780954138643/282070000000000000000000000000 : ℝ)*base78 + (2367548320644073/282070000000000000000000000000 : ℝ)*base80 + (338572029052503/141035000000000000000000000000 : ℝ)*base82 + (32189/39062500000000000000 : ℝ)*base89 + (32189/39062500000000000000 : ℝ)*base91 + (32189/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26788166958455954274387/5641400000000000000000000000 : ℝ) := by norm_num
    linear_combination (2647313259/100000000000000 : ℝ)*(base19) + (154561507/6250000000000 : ℝ)*(base23) + (156431903/100000000000000 : ℝ)*(upper2) + (186056671/50000000000000 : ℝ)*(upper3) + (514572027/100000000000000 : ℝ)*(upper5) + (103993773991113/10000000000000 : ℝ)*(major0) + (103993773991113/10000000000000 : ℝ)*(major1) + (103993773991113/10000000000000 : ℝ)*(major2) + (12442514221/100000000000000 : ℝ)*(sp1) + (12972049779/100000000000000 : ℝ)*(sp2) + (42964561762879/3125000000000 : ℝ)*(sp4) + (171856360823081/12500000000000 : ℝ)*(sp5) + (1374850531378237/100000000000000 : ℝ)*(sp6) + (352504672563459/50000000000000 : ℝ)*(sp7) + (352504672563459/50000000000000 : ℝ)*(f.failure) + (42964561762879/3125000000000 : ℝ)*(f.sum) + (9706245815687/14103500000000000000000000000 : ℝ)*base66 + (330721506226617/28207000000000000000000000000 : ℝ)*base67 + (25103526257149/28207000000000000000000000000 : ℝ)*base69 + (43823969905781/28207000000000000000000000000 : ℝ)*base71 + (158220790830767/28207000000000000000000000000 : ℝ)*base73 + (26681999345077/14103500000000000000000000000 : ℝ)*base75 + (16228334092873/5641400000000000000000000000 : ℝ)*base77 + (19867491762021/28207000000000000000000000000 : ℝ)*base79 + (35538892713127/28207000000000000000000000000 : ℝ)*base82 + (8223/2441406250000000000 : ℝ)*base90 + (8223/2441406250000000000 : ℝ)*base92 + (8223/2441406250000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1041_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28207/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5067/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2091/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1041_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1041_s2_0 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-54873961/250000000 : ℝ)*x 0 + (86423657/156250000 : ℝ)*x 1 + (2570690483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54873961/250000000 : ℝ)^4117 ≤ (3321484358463/25000000000000 : ℝ)^3093 := by
    have hnat : (54873961 : ℕ)^4117*25000000000000^3093 ≤ 3321484358463^3093*250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54873961 250000000 3321484358463 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86423657/156250000 : ℝ)^4117 ≤ (9092756065637/20000000000000 : ℝ)^3093 := by
    have hnat : (86423657 : ℕ)^4117*20000000000000^3093 ≤ 9092756065637^3093*156250000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86423657 156250000 9092756065637 20000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2570690483/5000000000 : ℝ)^4117 ≤ (41250282220427/100000000000000 : ℝ)^3093 := by
    have hnat : (2570690483 : ℕ)^4117*100000000000000^3093 ≤ 41250282220427^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570690483 5000000000 41250282220427 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-54873961/250000000 : ℝ), (86423657/156250000 : ℝ), (2570690483/5000000000 : ℝ)] ![(3321484358463/25000000000000 : ℝ), (9092756065637/20000000000000 : ℝ), (41250282220427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-54873961/250000000 : ℝ)|^4117 ≤ (3321484358463/25000000000000 : ℝ)^3093
        have hw : |(-54873961/250000000 : ℝ)|=(54873961/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(86423657/156250000 : ℝ)|^4117 ≤ (9092756065637/20000000000000 : ℝ)^3093
        have hw : |(86423657/156250000 : ℝ)|=(86423657/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2570690483/5000000000 : ℝ)|^4117 ≤ (41250282220427/100000000000000 : ℝ)^3093
        have hw : |(2570690483/5000000000 : ℝ)|=(2570690483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s2_1 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378323563/10000000000 : ℝ)*x 0 + (-239842743/1000000000 : ℝ)*x 1 + (514138073/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378323563/10000000000 : ℝ)^4117 ≤ (10949950852221/25000000000000 : ℝ)^3093 := by
    have hnat : (5378323563 : ℕ)^4117*25000000000000^3093 ≤ 10949950852221^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378323563 10000000000 10949950852221 25000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (239842743/1000000000 : ℝ)^4117 ≤ (14949916872497/100000000000000 : ℝ)^3093 := by
    have hnat : (239842743 : ℕ)^4117*100000000000000^3093 ≤ 14949916872497^3093*1000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239842743 1000000000 14949916872497 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514138073/1000000000 : ℝ)^4117 ≤ (20625139850041/50000000000000 : ℝ)^3093 := by
    have hnat : (514138073 : ℕ)^4117*50000000000000^3093 ≤ 20625139850041^3093*1000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514138073 1000000000 20625139850041 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378323563/10000000000 : ℝ), (-239842743/1000000000 : ℝ), (514138073/1000000000 : ℝ)] ![(10949950852221/25000000000000 : ℝ), (14949916872497/100000000000000 : ℝ), (20625139850041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378323563/10000000000 : ℝ)|^4117 ≤ (10949950852221/25000000000000 : ℝ)^3093
        have hw : |(5378323563/10000000000 : ℝ)|=(5378323563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-239842743/1000000000 : ℝ)|^4117 ≤ (14949916872497/100000000000000 : ℝ)^3093
        have hw : |(-239842743/1000000000 : ℝ)|=(239842743/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(514138073/1000000000 : ℝ)|^4117 ≤ (20625139850041/50000000000000 : ℝ)^3093
        have hw : |(514138073/1000000000 : ℝ)|=(514138073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s2_2 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268916183/500000000 : ℝ)*x 0 + (5141380657/10000000000 : ℝ)*x 1 + (-1199213699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268916183/500000000 : ℝ)^4117 ≤ (43799804460357/100000000000000 : ℝ)^3093 := by
    have hnat : (268916183 : ℕ)^4117*100000000000000^3093 ≤ 43799804460357^3093*500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268916183 500000000 43799804460357 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5141380657/10000000000 : ℝ)^4117 ≤ (41250278920483/100000000000000 : ℝ)^3093 := by
    have hnat : (5141380657 : ℕ)^4117*100000000000000^3093 ≤ 41250278920483^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5141380657 10000000000 41250278920483 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1199213699/5000000000 : ℝ)^4117 ≤ (7474958303499/50000000000000 : ℝ)^3093 := by
    have hnat : (1199213699 : ℕ)^4117*50000000000000^3093 ≤ 7474958303499^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199213699 5000000000 7474958303499 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268916183/500000000 : ℝ), (5141380657/10000000000 : ℝ), (-1199213699/5000000000 : ℝ)] ![(43799804460357/100000000000000 : ℝ), (41250278920483/100000000000000 : ℝ), (7474958303499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268916183/500000000 : ℝ)|^4117 ≤ (43799804460357/100000000000000 : ℝ)^3093
        have hw : |(268916183/500000000 : ℝ)|=(268916183/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5141380657/10000000000 : ℝ)|^4117 ≤ (41250278920483/100000000000000 : ℝ)^3093
        have hw : |(5141380657/10000000000 : ℝ)|=(5141380657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1199213699/5000000000 : ℝ)|^4117 ≤ (7474958303499/50000000000000 : ℝ)^3093
        have hw : |(-1199213699/5000000000 : ℝ)|=(1199213699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s2_3 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (218297283/500000000 : ℝ)*x 0 + (200135209/500000000 : ℝ)*x 1 + (119068471/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218297283/500000000 : ℝ)^4117 ≤ (1327330248833/4000000000000 : ℝ)^3093 := by
    have hnat : (218297283 : ℕ)^4117*4000000000000^3093 ≤ 1327330248833^3093*500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218297283 500000000 1327330248833 4000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200135209/500000000 : ℝ)^4117 ≤ (29560011810989/100000000000000 : ℝ)^3093 := by
    have hnat : (200135209 : ℕ)^4117*100000000000000^3093 ≤ 29560011810989^3093*500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200135209 500000000 29560011810989 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119068471/250000000 : ℝ)^4117 ≤ (18628365976003/50000000000000 : ℝ)^3093 := by
    have hnat : (119068471 : ℕ)^4117*50000000000000^3093 ≤ 18628365976003^3093*250000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119068471 250000000 18628365976003 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218297283/500000000 : ℝ), (200135209/500000000 : ℝ), (119068471/250000000 : ℝ)] ![(1327330248833/4000000000000 : ℝ), (29560011810989/100000000000000 : ℝ), (18628365976003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218297283/500000000 : ℝ)|^4117 ≤ (1327330248833/4000000000000 : ℝ)^3093
        have hw : |(218297283/500000000 : ℝ)|=(218297283/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200135209/500000000 : ℝ)|^4117 ≤ (29560011810989/100000000000000 : ℝ)^3093
        have hw : |(200135209/500000000 : ℝ)|=(200135209/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119068471/250000000 : ℝ)|^4117 ≤ (18628365976003/50000000000000 : ℝ)^3093
        have hw : |(119068471/250000000 : ℝ)|=(119068471/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s2_4 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1097546707/5000000000 : ℝ)*x 0 + (5144265507/10000000000 : ℝ)*x 1 + (5528198537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097546707/5000000000 : ℝ)^4117 ≤ (106296199313/800000000000 : ℝ)^3093 := by
    have hnat : (1097546707 : ℕ)^4117*800000000000^3093 ≤ 106296199313^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097546707 5000000000 106296199313 800000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5144265507/10000000000 : ℝ)^4117 ≤ (41281090335597/100000000000000 : ℝ)^3093 := by
    have hnat : (5144265507 : ℕ)^4117*100000000000000^3093 ≤ 41281090335597^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144265507 10000000000 41281090335597 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5528198537/10000000000 : ℝ)^4117 ≤ (5678985592073/12500000000000 : ℝ)^3093 := by
    have hnat : (5528198537 : ℕ)^4117*12500000000000^3093 ≤ 5678985592073^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528198537 10000000000 5678985592073 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1097546707/5000000000 : ℝ), (5144265507/10000000000 : ℝ), (5528198537/10000000000 : ℝ)] ![(106296199313/800000000000 : ℝ), (41281090335597/100000000000000 : ℝ), (5678985592073/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1097546707/5000000000 : ℝ)|^4117 ≤ (106296199313/800000000000 : ℝ)^3093
        have hw : |(-1097546707/5000000000 : ℝ)|=(1097546707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5144265507/10000000000 : ℝ)|^4117 ≤ (41281090335597/100000000000000 : ℝ)^3093
        have hw : |(5144265507/10000000000 : ℝ)|=(5144265507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5528198537/10000000000 : ℝ)|^4117 ≤ (5678985592073/12500000000000 : ℝ)^3093
        have hw : |(5528198537/10000000000 : ℝ)|=(5528198537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s2_5 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2640062751/5000000000 : ℝ)*x 0 + (-2011609819/10000000000 : ℝ)*x 1 + (1105639719/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2640062751/5000000000 : ℝ)^4117 ≤ (42738574402507/100000000000000 : ℝ)^3093 := by
    have hnat : (2640062751 : ℕ)^4117*100000000000000^3093 ≤ 42738574402507^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640062751 5000000000 42738574402507 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2011609819/10000000000 : ℝ)^4117 ≤ (118295402079/1000000000000 : ℝ)^3093 := by
    have hnat : (2011609819 : ℕ)^4117*1000000000000^3093 ≤ 118295402079^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011609819 10000000000 118295402079 1000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105639719/2000000000 : ℝ)^4117 ≤ (45431885371047/100000000000000 : ℝ)^3093 := by
    have hnat : (1105639719 : ℕ)^4117*100000000000000^3093 ≤ 45431885371047^3093*2000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105639719 2000000000 45431885371047 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2640062751/5000000000 : ℝ), (-2011609819/10000000000 : ℝ), (1105639719/2000000000 : ℝ)] ![(42738574402507/100000000000000 : ℝ), (118295402079/1000000000000 : ℝ), (45431885371047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2640062751/5000000000 : ℝ)|^4117 ≤ (42738574402507/100000000000000 : ℝ)^3093
        have hw : |(2640062751/5000000000 : ℝ)|=(2640062751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2011609819/10000000000 : ℝ)|^4117 ≤ (118295402079/1000000000000 : ℝ)^3093
        have hw : |(-2011609819/10000000000 : ℝ)|=(2011609819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1105639719/2000000000 : ℝ)|^4117 ≤ (45431885371047/100000000000000 : ℝ)^3093
        have hw : |(1105639719/2000000000 : ℝ)|=(1105639719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s2_6 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1320031429/2500000000 : ℝ)*x 0 + (5528198441/10000000000 : ℝ)*x 1 + (-2011609741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320031429/2500000000 : ℝ)^4117 ≤ (21369288354071/50000000000000 : ℝ)^3093 := by
    have hnat : (1320031429 : ℕ)^4117*50000000000000^3093 ≤ 21369288354071^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320031429 2500000000 21369288354071 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5528198441/10000000000 : ℝ)^4117 ≤ (45431883686439/100000000000000 : ℝ)^3093 := by
    have hnat : (5528198441 : ℕ)^4117*100000000000000^3093 ≤ 45431883686439^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528198441 10000000000 45431883686439 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011609741/10000000000 : ℝ)^4117 ≤ (1478692449669/12500000000000 : ℝ)^3093 := by
    have hnat : (2011609741 : ℕ)^4117*12500000000000^3093 ≤ 1478692449669^3093*10000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011609741 10000000000 1478692449669 12500000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1320031429/2500000000 : ℝ), (5528198441/10000000000 : ℝ), (-2011609741/10000000000 : ℝ)] ![(21369288354071/50000000000000 : ℝ), (45431883686439/100000000000000 : ℝ), (1478692449669/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1320031429/2500000000 : ℝ)|^4117 ≤ (21369288354071/50000000000000 : ℝ)^3093
        have hw : |(1320031429/2500000000 : ℝ)|=(1320031429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5528198441/10000000000 : ℝ)|^4117 ≤ (45431883686439/100000000000000 : ℝ)^3093
        have hw : |(5528198441/10000000000 : ℝ)|=(5528198441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2011609741/10000000000 : ℝ)|^4117 ≤ (1478692449669/12500000000000 : ℝ)^3093
        have hw : |(-2011609741/10000000000 : ℝ)|=(2011609741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1041_s2_7 (p : ℝ) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1091552211/2500000000 : ℝ)*x 0 + (2378556447/5000000000 : ℝ)*x 1 + (2004195037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091552211/2500000000 : ℝ)^4117 ≤ (1327436752713/4000000000000 : ℝ)^3093 := by
    have hnat : (1091552211 : ℕ)^4117*4000000000000^3093 ≤ 1327436752713^3093*2500000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091552211 2500000000 1327436752713 4000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2378556447/5000000000 : ℝ)^4117 ≤ (37198164066589/100000000000000 : ℝ)^3093 := by
    have hnat : (2378556447 : ℕ)^4117*100000000000000^3093 ≤ 37198164066589^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2378556447 5000000000 37198164066589 100000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2004195037/5000000000 : ℝ)^4117 ≤ (14807958549699/50000000000000 : ℝ)^3093 := by
    have hnat : (2004195037 : ℕ)^4117*50000000000000^3093 ≤ 14807958549699^3093*5000000000^4117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004195037 5000000000 14807958549699 50000000000000 4117 3093 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4117/1024 : ℝ)) 4117 3093 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091552211/2500000000 : ℝ), (2378556447/5000000000 : ℝ), (2004195037/5000000000 : ℝ)] ![(1327436752713/4000000000000 : ℝ), (37198164066589/100000000000000 : ℝ), (14807958549699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091552211/2500000000 : ℝ)|^4117 ≤ (1327436752713/4000000000000 : ℝ)^3093
        have hw : |(1091552211/2500000000 : ℝ)|=(1091552211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2378556447/5000000000 : ℝ)|^4117 ≤ (37198164066589/100000000000000 : ℝ)^3093
        have hw : |(2378556447/5000000000 : ℝ)|=(2378556447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2004195037/5000000000 : ℝ)|^4117 ≤ (14807958549699/50000000000000 : ℝ)^3093
        have hw : |(2004195037/5000000000 : ℝ)|=(2004195037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1041_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2091/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5067/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2147/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2103/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2091/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5067/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2091/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5067/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2091/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5067/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2091/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5067/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2091/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5067/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2091/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5067/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
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
  have hpowlo : (5067/100000 : ℝ) ^ (8233/2048 : ℝ) ≤ (4851358488501/781250000000000000 : ℝ) := by
    have hpowers : (5067/100000 : ℝ)^8233 ≤ (4851358488501/781250000000000000 : ℝ)^2048 := by
      have hnat : (5067 : ℕ)^8233*781250000000000000^2048 ≤ 4851358488501^2048*100000^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5067 100000 4851358488501 781250000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5067/100000 : ℝ)) (X := (4851358488501/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2091/10000 : ℝ) ^ (8233/2048 : ℝ) ≤ (185272063081974903/100000000000000000000 : ℝ) := by
    have hpowers : (2091/10000 : ℝ)^8233 ≤ (185272063081974903/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2091 : ℕ)^8233*100000000000000000000^2048 ≤ 185272063081974903^2048*10000^8233 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2091 10000 185272063081974903 100000000000000000000 8233 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2091/10000 : ℝ)) (X := (185272063081974903/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (390629851358488501/390625000000000000 : ℝ) ≤ (1000003089392899/1000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (390629851358488501/390625000000000000 : ℝ)^2048 ≤ (1000003089392899/1000000000000000 : ℝ)^8233 := by
      have hnat : (390629851358488501 : ℕ)^2048*1000000000000000^8233 ≤ 1000003089392899^8233*390625000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390629851358488501 390625000000000000 1000003089392899 1000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000003089392899/1000000000000000 : ℝ)) (X := (390629851358488501/390625000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100185893036968503031/100000000000000000000 : ℝ) ≤ (1000462095706893/1000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (100185893036968503031/100000000000000000000 : ℝ)^2048 ≤ (1000462095706893/1000000000000000 : ℝ)^8233 := by
      have hnat : (100185893036968503031 : ℕ)^2048*1000000000000000^8233 ≤ 1000462095706893^8233*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100185893036968503031 100000000000000000000 1000462095706893 1000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000462095706893/1000000000000000 : ℝ)) (X := (100185893036968503031/100000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50185272063081974903/50000000000000000000 : ℝ) ≤ (1000921102020887/1000000000000000 : ℝ) ^ (8233/2048 : ℝ) := by
    have hpowers : (50185272063081974903/50000000000000000000 : ℝ)^2048 ≤ (1000921102020887/1000000000000000 : ℝ)^8233 := by
      have hnat : (50185272063081974903 : ℕ)^2048*1000000000000000^8233 ≤ 1000921102020887^8233*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50185272063081974903 50000000000000000000 1000921102020887 1000000000000000 2048 8233 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000921102020887/1000000000000000 : ℝ)) (X := (50185272063081974903/50000000000000000000 : ℝ)) (by norm_num) 8233 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4851358488501/781250000000000000 : ℝ) ≤ ((5279465791755227887/5281000000000000000 : ℝ)+2*(229503156997/79215000000000 : ℝ)*(5067/100000 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (5279465791755227887/5281000000000000000 : ℝ)+2*(229503156997/79215000000000 : ℝ)*(5067/100000 : ℝ)=(1000003089392899/1000000000000000 : ℝ) by norm_num, show 1+2*(4851358488501/781250000000000000 : ℝ)=(390629851358488501/390625000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(185272063081974903/100000000000000000000 : ℝ)+(4851358488501/781250000000000000 : ℝ) ≤ ((5279465791755227887/5281000000000000000 : ℝ)+(229503156997/79215000000000 : ℝ)*((2091/10000 : ℝ)+(5067/100000 : ℝ)))^(8233/2048 : ℝ) := by
    rw [show (5279465791755227887/5281000000000000000 : ℝ)+(229503156997/79215000000000 : ℝ)*((2091/10000 : ℝ)+(5067/100000 : ℝ))=(1000462095706893/1000000000000000 : ℝ) by norm_num, show 1+(185272063081974903/100000000000000000000 : ℝ)+(4851358488501/781250000000000000 : ℝ)=(100185893036968503031/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(185272063081974903/100000000000000000000 : ℝ) ≤ ((5279465791755227887/5281000000000000000 : ℝ)+2*(229503156997/79215000000000 : ℝ)*(2091/10000 : ℝ))^(8233/2048 : ℝ) := by
    rw [show (5279465791755227887/5281000000000000000 : ℝ)+2*(229503156997/79215000000000 : ℝ)*(2091/10000 : ℝ)=(1000921102020887/1000000000000000 : ℝ) by norm_num, show 1+2*(185272063081974903/100000000000000000000 : ℝ)=(50185272063081974903/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5279465791755227887/5281000000000000000 : ℝ)*(X 1 0+X 2 0)+(229503156997/79215000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (5067/100000 : ℝ)) (hi := (2091/10000 : ℝ)) (c := (5279465791755227887/5281000000000000000 : ℝ)) (alpha := (229503156997/79215000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5279465791755227887/5281000000000000000 : ℝ)*(X 0 1+X 2 1)+(229503156997/79215000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (5067/100000 : ℝ)) (hi := (2091/10000 : ℝ)) (c := (5279465791755227887/5281000000000000000 : ℝ)) (alpha := (229503156997/79215000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5279465791755227887/5281000000000000000 : ℝ)*(X 0 2+X 1 2)+(229503156997/79215000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8233/2048 : ℝ)) (lo := (5067/100000 : ℝ)) (hi := (2091/10000 : ℝ)) (c := (5279465791755227887/5281000000000000000 : ℝ)) (alpha := (229503156997/79215000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-54873961/250000000 : ℝ)*X 0 0+(86423657/156250000 : ℝ)*X 0 1+(2570690483/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5378323563/10000000000 : ℝ)*X 1 0+(-239842743/1000000000 : ℝ)*X 1 1+(514138073/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((268916183/500000000 : ℝ)*X 2 0+(5141380657/10000000000 : ℝ)*X 2 1+(-1199213699/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((218297283/500000000 : ℝ)*X 0 0+(200135209/500000000 : ℝ)*X 0 1+(119068471/250000000 : ℝ)*X 0 2+(218297283/500000000 : ℝ)*X 1 0+(200135209/500000000 : ℝ)*X 1 1+(119068471/250000000 : ℝ)*X 1 2+(218297283/500000000 : ℝ)*X 2 0+(200135209/500000000 : ℝ)*X 2 1+(119068471/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1097546707/5000000000 : ℝ)*X 0 0+(5144265507/10000000000 : ℝ)*X 0 1+(5528198537/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2640062751/5000000000 : ℝ)*X 1 0+(-2011609819/10000000000 : ℝ)*X 1 1+(1105639719/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1320031429/2500000000 : ℝ)*X 2 0+(5528198441/10000000000 : ℝ)*X 2 1+(-2011609741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1091552211/2500000000 : ℝ)*X 0 0+(2378556447/5000000000 : ℝ)*X 0 1+(2004195037/5000000000 : ℝ)*X 0 2+(1091552211/2500000000 : ℝ)*X 1 0+(2378556447/5000000000 : ℝ)*X 1 1+(2004195037/5000000000 : ℝ)*X 1 2+(1091552211/2500000000 : ℝ)*X 2 0+(2378556447/5000000000 : ℝ)*X 2 1+(2004195037/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1041_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (498940531770565842493758429/66012500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64095607/100000000000000 : ℝ)*(base1) + (1516648419/100000000000000 : ℝ)*(base19) + (390731261/25000000000000 : ℝ)*(base23) + (121544331/100000000000000 : ℝ)*(upper3) + (75352417/50000000000000 : ℝ)*(upper5) + (970407425781689/50000000000000 : ℝ)*(major0) + (970407425781689/50000000000000 : ℝ)*(major1) + (970407425781689/50000000000000 : ℝ)*(major2) + (2565871288539667/100000000000000 : ℝ)*(sp0) + (64147079952399/2500000000000 : ℝ)*(sp1) + (1282941575909667/50000000000000 : ℝ)*(sp2) + (657868539608917/50000000000000 : ℝ)*(sp3) + (13490300319/100000000000000 : ℝ)*(sp4) + (7593126479/100000000000000 : ℝ)*(sp7) + (1315744736439919/100000000000000 : ℝ)*(f.failure) + (2565884714744379/100000000000000 : ℝ)*(f.sum) + (26253768437923/7921500000000000000000000000 : ℝ)*base66 + (1096612550497366571/792150000000000000000000000000000 : ℝ)*base68 + (8359082198289766571/792150000000000000000000000000000 : ℝ)*base70 + (2153008819654516571/792150000000000000000000000000000 : ℝ)*base72 + (7190476802093/7921500000000000000000000000 : ℝ)*base73 + (5506264220766016571/792150000000000000000000000000000 : ℝ)*base76 + (326736272518516571/792150000000000000000000000000000 : ℝ)*base78 + (3232896195261283429/792150000000000000000000000000000 : ℝ)*base79 + (68705775347959/7921500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (356631/39062500000000000000 : ℝ)*base89 + (356631/39062500000000000000 : ℝ)*base91 + (356631/39062500000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17925595123939748997027131/2112400000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1636512489/100000000000000 : ℝ)*(base19) + (1858053307/100000000000000 : ℝ)*(base23) + (52326767/25000000000000 : ℝ)*(upper3) + (688721/1562500000000 : ℝ)*(lower4) + (192133371/100000000000000 : ℝ)*(upper5) + (15760915670329/800000000000 : ℝ)*(major0) + (15760915670329/800000000000 : ℝ)*(major1) + (15760915670329/800000000000 : ℝ)*(major2) + (13898417461/100000000000000 : ℝ)*(sp1) + (15645858149/100000000000000 : ℝ)*(sp2) + (162788793306577/6250000000000 : ℝ)*(sp4) + (1302302578987641/50000000000000 : ℝ)*(sp5) + (2604603188993777/100000000000000 : ℝ)*(sp6) + (1335607941813997/100000000000000 : ℝ)*(sp7) + (1335607941813997/100000000000000 : ℝ)*(f.failure) + (162788793306577/6250000000000 : ℝ)*(f.sum) + (193512809143/198037500000000000000000000 : ℝ)*base65 + (4434090351509669/12674400000000000000000000000000 : ℝ)*base67 + (11188260113861669/12674400000000000000000000000000 : ℝ)*base69 + (94455858791014469/12674400000000000000000000000000 : ℝ)*base71 + (954268815709/1584300000000000000000000000 : ℝ)*base74 + (28222530315903269/12674400000000000000000000000000 : ℝ)*base75 + (29644255855621531/12674400000000000000000000000000 : ℝ)*base78 + (137609088229784731/12674400000000000000000000000000 : ℝ)*base80 + (19770195384383/15843000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (27139/19531250000000000000 : ℝ)*base89 + (27139/19531250000000000000 : ℝ)*base91 + (27139/19531250000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1041_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2091/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5067/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2147/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2103/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1041_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1041_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2147/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2103/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1041_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1041_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1041_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8233/2048 : ℝ) ≤ p) (hpb : p ≤ (4117/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (576199/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2147/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2103/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1041_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

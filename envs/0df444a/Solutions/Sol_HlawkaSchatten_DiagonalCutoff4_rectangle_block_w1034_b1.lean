-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1034_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:41:40.612793+00:00
-- url     : https://prove2.me/submissions/2944bd70-4d5e-4d5c-9296-fd5e95dcdc69

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
theorem support_rectangle_w1034_s3_0 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1107217179/5000000000 : ℝ)*x 0 + (217652427/400000000 : ℝ)*x 1 + (1305210187/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1107217179/5000000000 : ℝ)^8227 ≤ (3358870883569/25000000000000 : ℝ)^6179 := by
    have hnat : (1107217179 : ℕ)^8227*25000000000000^6179 ≤ 3358870883569^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107217179 5000000000 3358870883569 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217652427/400000000 : ℝ)^8227 ≤ (44473746836539/100000000000000 : ℝ)^6179 := by
    have hnat : (217652427 : ℕ)^8227*100000000000000^6179 ≤ 44473746836539^6179*400000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217652427 400000000 44473746836539 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1305210187/2500000000 : ℝ)^8227 ≤ (42090769618359/100000000000000 : ℝ)^6179 := by
    have hnat : (1305210187 : ℕ)^8227*100000000000000^6179 ≤ 42090769618359^6179*2500000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305210187 2500000000 42090769618359 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1107217179/5000000000 : ℝ), (217652427/400000000 : ℝ), (1305210187/2500000000 : ℝ)] ![(3358870883569/25000000000000 : ℝ), (44473746836539/100000000000000 : ℝ), (42090769618359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1107217179/5000000000 : ℝ)|^8227 ≤ (3358870883569/25000000000000 : ℝ)^6179
        have hw : |(-1107217179/5000000000 : ℝ)|=(1107217179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217652427/400000000 : ℝ)|^8227 ≤ (44473746836539/100000000000000 : ℝ)^6179
        have hw : |(217652427/400000000 : ℝ)|=(217652427/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1305210187/2500000000 : ℝ)|^8227 ≤ (42090769618359/100000000000000 : ℝ)^6179
        have hw : |(1305210187/2500000000 : ℝ)|=(1305210187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s3_1 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5356514851/10000000000 : ℝ)*x 0 + (-290927999/1250000000 : ℝ)*x 1 + (652605149/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356514851/10000000000 : ℝ)^8227 ≤ (5444169844851/12500000000000 : ℝ)^6179 := by
    have hnat : (5356514851 : ℕ)^8227*12500000000000^6179 ≤ 5444169844851^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356514851 10000000000 5444169844851 12500000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (290927999/1250000000 : ℝ)^8227 ≤ (897241677777/6250000000000 : ℝ)^6179 := by
    have hnat : (290927999 : ℕ)^8227*6250000000000^6179 ≤ 897241677777^6179*1250000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290927999 1250000000 897241677777 6250000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652605149/1250000000 : ℝ)^8227 ≤ (5261346798043/12500000000000 : ℝ)^6179 := by
    have hnat : (652605149 : ℕ)^8227*12500000000000^6179 ≤ 5261346798043^6179*1250000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652605149 1250000000 5261346798043 12500000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356514851/10000000000 : ℝ), (-290927999/1250000000 : ℝ), (652605149/1250000000 : ℝ)] ![(5444169844851/12500000000000 : ℝ), (897241677777/6250000000000 : ℝ), (5261346798043/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356514851/10000000000 : ℝ)|^8227 ≤ (5444169844851/12500000000000 : ℝ)^6179
        have hw : |(5356514851/10000000000 : ℝ)|=(5356514851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-290927999/1250000000 : ℝ)|^8227 ≤ (897241677777/6250000000000 : ℝ)^6179
        have hw : |(-290927999/1250000000 : ℝ)|=(290927999/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652605149/1250000000 : ℝ)|^8227 ≤ (5261346798043/12500000000000 : ℝ)^6179
        have hw : |(652605149/1250000000 : ℝ)|=(652605149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s3_2 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (133912877/250000000 : ℝ)*x 0 + (1044168219/2000000000 : ℝ)*x 1 + (-2327423817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133912877/250000000 : ℝ)^8227 ≤ (10888340309483/25000000000000 : ℝ)^6179 := by
    have hnat : (133912877 : ℕ)^8227*25000000000000^6179 ≤ 10888340309483^6179*250000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133912877 250000000 10888340309483 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044168219/2000000000 : ℝ)^8227 ≤ (42090773343127/100000000000000 : ℝ)^6179 := by
    have hnat : (1044168219 : ℕ)^8227*100000000000000^6179 ≤ 42090773343127^6179*2000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044168219 2000000000 42090773343127 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2327423817/10000000000 : ℝ)^8227 ≤ (7177932703619/50000000000000 : ℝ)^6179 := by
    have hnat : (2327423817 : ℕ)^8227*50000000000000^6179 ≤ 7177932703619^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2327423817 10000000000 7177932703619 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133912877/250000000 : ℝ), (1044168219/2000000000 : ℝ), (-2327423817/10000000000 : ℝ)] ![(10888340309483/25000000000000 : ℝ), (42090773343127/100000000000000 : ℝ), (7177932703619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133912877/250000000 : ℝ)|^8227 ≤ (10888340309483/25000000000000 : ℝ)^6179
        have hw : |(133912877/250000000 : ℝ)|=(133912877/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044168219/2000000000 : ℝ)|^8227 ≤ (42090773343127/100000000000000 : ℝ)^6179
        have hw : |(1044168219/2000000000 : ℝ)|=(1044168219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2327423817/10000000000 : ℝ)|^8227 ≤ (7177932703619/50000000000000 : ℝ)^6179
        have hw : |(-2327423817/10000000000 : ℝ)|=(2327423817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s3_3 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2188525617/5000000000 : ℝ)*x 0 + (833548809/2000000000 : ℝ)*x 1 + (1149272231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188525617/5000000000 : ℝ)^8227 ≤ (33285339993099/100000000000000 : ℝ)^6179 := by
    have hnat : (2188525617 : ℕ)^8227*100000000000000^6179 ≤ 33285339993099^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188525617 5000000000 33285339993099 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833548809/2000000000 : ℝ)^8227 ≤ (31183083453477/100000000000000 : ℝ)^6179 := by
    have hnat : (833548809 : ℕ)^8227*100000000000000^6179 ≤ 31183083453477^6179*2000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833548809 2000000000 31183083453477 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1149272231/2500000000 : ℝ)^8227 ≤ (4441447066183/12500000000000 : ℝ)^6179 := by
    have hnat : (1149272231 : ℕ)^8227*12500000000000^6179 ≤ 4441447066183^6179*2500000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149272231 2500000000 4441447066183 12500000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188525617/5000000000 : ℝ), (833548809/2000000000 : ℝ), (1149272231/2500000000 : ℝ)] ![(33285339993099/100000000000000 : ℝ), (31183083453477/100000000000000 : ℝ), (4441447066183/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188525617/5000000000 : ℝ)|^8227 ≤ (33285339993099/100000000000000 : ℝ)^6179
        have hw : |(2188525617/5000000000 : ℝ)|=(2188525617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833548809/2000000000 : ℝ)|^8227 ≤ (31183083453477/100000000000000 : ℝ)^6179
        have hw : |(833548809/2000000000 : ℝ)|=(833548809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1149272231/2500000000 : ℝ)|^8227 ≤ (4441447066183/12500000000000 : ℝ)^6179
        have hw : |(1149272231/2500000000 : ℝ)|=(1149272231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s3_4 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-442891871/2000000000 : ℝ)*x 0 + (326360359/625000000 : ℝ)*x 1 + (340023729/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442891871/2000000000 : ℝ)^8227 ≤ (13435685465043/100000000000000 : ℝ)^6179 := by
    have hnat : (442891871 : ℕ)^8227*100000000000000^6179 ≤ 13435685465043^6179*2000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442891871 2000000000 13435685465043 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326360359/625000000 : ℝ)^8227 ≤ (2105034950143/5000000000000 : ℝ)^6179 := by
    have hnat : (326360359 : ℕ)^8227*5000000000000^6179 ≤ 2105034950143^6179*625000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326360359 625000000 2105034950143 5000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340023729/625000000 : ℝ)^8227 ≤ (44463615517403/100000000000000 : ℝ)^6179 := by
    have hnat : (340023729 : ℕ)^8227*100000000000000^6179 ≤ 44463615517403^6179*625000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340023729 625000000 44463615517403 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-442891871/2000000000 : ℝ), (326360359/625000000 : ℝ), (340023729/625000000 : ℝ)] ![(13435685465043/100000000000000 : ℝ), (2105034950143/5000000000000 : ℝ), (44463615517403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-442891871/2000000000 : ℝ)|^8227 ≤ (13435685465043/100000000000000 : ℝ)^6179
        have hw : |(-442891871/2000000000 : ℝ)|=(442891871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326360359/625000000 : ℝ)|^8227 ≤ (2105034950143/5000000000000 : ℝ)^6179
        have hw : |(326360359/625000000 : ℝ)|=(326360359/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340023729/625000000 : ℝ)|^8227 ≤ (44463615517403/100000000000000 : ℝ)^6179
        have hw : |(340023729/625000000 : ℝ)|=(340023729/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s3_5 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2650559659/5000000000 : ℝ)*x 0 + (-105394317/500000000 : ℝ)*x 1 + (1088075803/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650559659/5000000000 : ℝ)^8227 ≤ (21477342167787/50000000000000 : ℝ)^6179 := by
    have hnat : (2650559659 : ℕ)^8227*50000000000000^6179 ≤ 21477342167787^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650559659 5000000000 21477342167787 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105394317/500000000 : ℝ)^8227 ≤ (3145426798921/25000000000000 : ℝ)^6179 := by
    have hnat : (105394317 : ℕ)^8227*25000000000000^6179 ≤ 3145426798921^6179*500000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105394317 500000000 3145426798921 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088075803/2000000000 : ℝ)^8227 ≤ (22231804227573/50000000000000 : ℝ)^6179 := by
    have hnat : (1088075803 : ℕ)^8227*50000000000000^6179 ≤ 22231804227573^6179*2000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088075803 2000000000 22231804227573 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650559659/5000000000 : ℝ), (-105394317/500000000 : ℝ), (1088075803/2000000000 : ℝ)] ![(21477342167787/50000000000000 : ℝ), (3145426798921/25000000000000 : ℝ), (22231804227573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650559659/5000000000 : ℝ)|^8227 ≤ (21477342167787/50000000000000 : ℝ)^6179
        have hw : |(2650559659/5000000000 : ℝ)|=(2650559659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-105394317/500000000 : ℝ)|^8227 ≤ (3145426798921/25000000000000 : ℝ)^6179
        have hw : |(-105394317/500000000 : ℝ)|=(105394317/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1088075803/2000000000 : ℝ)|^8227 ≤ (22231804227573/50000000000000 : ℝ)^6179
        have hw : |(1088075803/2000000000 : ℝ)|=(1088075803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s3_6 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2650559451/5000000000 : ℝ)*x 0 + (170011861/312500000 : ℝ)*x 1 + (-2107886169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650559451/5000000000 : ℝ)^8227 ≤ (8590935969501/20000000000000 : ℝ)^6179 := by
    have hnat : (2650559451 : ℕ)^8227*20000000000000^6179 ≤ 8590935969501^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650559451 5000000000 8590935969501 20000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170011861/312500000 : ℝ)^8227 ≤ (44463614298647/100000000000000 : ℝ)^6179 := by
    have hnat : (170011861 : ℕ)^8227*100000000000000^6179 ≤ 44463614298647^6179*312500000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170011861 312500000 44463614298647 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107886169/10000000000 : ℝ)^8227 ≤ (3145426459177/25000000000000 : ℝ)^6179 := by
    have hnat : (2107886169 : ℕ)^8227*25000000000000^6179 ≤ 3145426459177^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107886169 10000000000 3145426459177 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650559451/5000000000 : ℝ), (170011861/312500000 : ℝ), (-2107886169/10000000000 : ℝ)] ![(8590935969501/20000000000000 : ℝ), (44463614298647/100000000000000 : ℝ), (3145426459177/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650559451/5000000000 : ℝ)|^8227 ≤ (8590935969501/20000000000000 : ℝ)^6179
        have hw : |(2650559451/5000000000 : ℝ)|=(2650559451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(170011861/312500000 : ℝ)|^8227 ≤ (44463614298647/100000000000000 : ℝ)^6179
        have hw : |(170011861/312500000 : ℝ)|=(170011861/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2107886169/10000000000 : ℝ)|^8227 ≤ (3145426459177/25000000000000 : ℝ)^6179
        have hw : |(-2107886169/10000000000 : ℝ)|=(2107886169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s3_7 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4377098841/10000000000 : ℝ)*x 0 + (4595287367/10000000000 : ℝ)*x 1 + (4169556473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377098841/10000000000 : ℝ)^8227 ≤ (832145550361/2500000000000 : ℝ)^6179 := by
    have hnat : (4377098841 : ℕ)^8227*2500000000000^6179 ≤ 832145550361^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377098841 10000000000 832145550361 2500000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4595287367/10000000000 : ℝ)^8227 ≤ (35513038025947/100000000000000 : ℝ)^6179 := by
    have hnat : (4595287367 : ℕ)^8227*100000000000000^6179 ≤ 35513038025947^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4595287367 10000000000 35513038025947 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4169556473/10000000000 : ℝ)^8227 ≤ (6240227989071/20000000000000 : ℝ)^6179 := by
    have hnat : (4169556473 : ℕ)^8227*20000000000000^6179 ≤ 6240227989071^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169556473 10000000000 6240227989071 20000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377098841/10000000000 : ℝ), (4595287367/10000000000 : ℝ), (4169556473/10000000000 : ℝ)] ![(832145550361/2500000000000 : ℝ), (35513038025947/100000000000000 : ℝ), (6240227989071/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377098841/10000000000 : ℝ)|^8227 ≤ (832145550361/2500000000000 : ℝ)^6179
        have hw : |(4377098841/10000000000 : ℝ)|=(4377098841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4595287367/10000000000 : ℝ)|^8227 ≤ (35513038025947/100000000000000 : ℝ)^6179
        have hw : |(4595287367/10000000000 : ℝ)|=(4595287367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4169556473/10000000000 : ℝ)|^8227 ≤ (6240227989071/20000000000000 : ℝ)^6179
        have hw : |(4169556473/10000000000 : ℝ)|=(4169556473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1034_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36842731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3369/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1711/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (643/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14953/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3369/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1711/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3369/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1711/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3369/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1711/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3369/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1711/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3369/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1711/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3369/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1711/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1711/20000 : ℝ) ^ (4113/1024 : ℝ) ≤ (5142250621418093/100000000000000000000 : ℝ) := by
    have hpowers : (1711/20000 : ℝ)^4113 ≤ (5142250621418093/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1711 : ℕ)^4113*100000000000000000000^1024 ≤ 5142250621418093^1024*20000^4113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1711 20000 5142250621418093 100000000000000000000 4113 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1711/20000 : ℝ)) (X := (5142250621418093/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3369/20000 : ℝ) ^ (4113/1024 : ℝ) ≤ (78170388700814937/100000000000000000000 : ℝ) := by
    have hpowers : (3369/20000 : ℝ)^4113 ≤ (78170388700814937/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3369 : ℕ)^4113*100000000000000000000^1024 ≤ 78170388700814937^1024*20000^4113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3369 20000 78170388700814937 100000000000000000000 4113 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3369/20000 : ℝ)) (X := (78170388700814937/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005142250621418093/50000000000000000000 : ℝ) ≤ (10000256039936227/10000000000000000 : ℝ) ^ (4113/1024 : ℝ) := by
    have hpowers : (50005142250621418093/50000000000000000000 : ℝ)^1024 ≤ (10000256039936227/10000000000000000 : ℝ)^4113 := by
      have hnat : (50005142250621418093 : ℕ)^1024*10000000000000000^4113 ≤ 10000256039936227^4113*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005142250621418093 50000000000000000000 10000256039936227 10000000000000000 1024 4113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000256039936227/10000000000000000 : ℝ)) (X := (50005142250621418093/50000000000000000000 : ℝ)) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10008331263932223303/10000000000000000000 : ℝ) ≤ (2500518389651663/2500000000000000 : ℝ) ^ (4113/1024 : ℝ) := by
    have hpowers : (10008331263932223303/10000000000000000000 : ℝ)^1024 ≤ (2500518389651663/2500000000000000 : ℝ)^4113 := by
      have hnat : (10008331263932223303 : ℕ)^1024*2500000000000000^4113 ≤ 2500518389651663^4113*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10008331263932223303 10000000000000000000 2500518389651663 2500000000000000 1024 4113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500518389651663/2500000000000000 : ℝ)) (X := (10008331263932223303/10000000000000000000 : ℝ)) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50078170388700814937/50000000000000000000 : ℝ) ≤ (10003891077277077/10000000000000000 : ℝ) ^ (4113/1024 : ℝ) := by
    have hpowers : (50078170388700814937/50000000000000000000 : ℝ)^1024 ≤ (10003891077277077/10000000000000000 : ℝ)^4113 := by
      have hnat : (50078170388700814937 : ℕ)^1024*10000000000000000^4113 ≤ 10003891077277077^4113*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50078170388700814937 50000000000000000000 10003891077277077 10000000000000000 1024 4113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003891077277077/10000000000000000 : ℝ)) (X := (50078170388700814937/50000000000000000000 : ℝ)) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5142250621418093/100000000000000000000 : ℝ) ≤ ((129485976291594297/129531250000000000 : ℝ)+2*(72700746817/33160000000000 : ℝ)*(1711/20000 : ℝ))^(4113/1024 : ℝ) := by
    rw [show (129485976291594297/129531250000000000 : ℝ)+2*(72700746817/33160000000000 : ℝ)*(1711/20000 : ℝ)=(10000256039936227/10000000000000000 : ℝ) by norm_num, show 1+2*(5142250621418093/100000000000000000000 : ℝ)=(50005142250621418093/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(78170388700814937/100000000000000000000 : ℝ)+(5142250621418093/100000000000000000000 : ℝ) ≤ ((129485976291594297/129531250000000000 : ℝ)+(72700746817/33160000000000 : ℝ)*((3369/20000 : ℝ)+(1711/20000 : ℝ)))^(4113/1024 : ℝ) := by
    rw [show (129485976291594297/129531250000000000 : ℝ)+(72700746817/33160000000000 : ℝ)*((3369/20000 : ℝ)+(1711/20000 : ℝ))=(2500518389651663/2500000000000000 : ℝ) by norm_num, show 1+(78170388700814937/100000000000000000000 : ℝ)+(5142250621418093/100000000000000000000 : ℝ)=(10008331263932223303/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(78170388700814937/100000000000000000000 : ℝ) ≤ ((129485976291594297/129531250000000000 : ℝ)+2*(72700746817/33160000000000 : ℝ)*(3369/20000 : ℝ))^(4113/1024 : ℝ) := by
    rw [show (129485976291594297/129531250000000000 : ℝ)+2*(72700746817/33160000000000 : ℝ)*(3369/20000 : ℝ)=(10003891077277077/10000000000000000 : ℝ) by norm_num, show 1+2*(78170388700814937/100000000000000000000 : ℝ)=(50078170388700814937/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (129485976291594297/129531250000000000 : ℝ)*(X 1 0+X 2 0)+(72700746817/33160000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4113/1024 : ℝ)) (lo := (1711/20000 : ℝ)) (hi := (3369/20000 : ℝ)) (c := (129485976291594297/129531250000000000 : ℝ)) (alpha := (72700746817/33160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (129485976291594297/129531250000000000 : ℝ)*(X 0 1+X 2 1)+(72700746817/33160000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4113/1024 : ℝ)) (lo := (1711/20000 : ℝ)) (hi := (3369/20000 : ℝ)) (c := (129485976291594297/129531250000000000 : ℝ)) (alpha := (72700746817/33160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (129485976291594297/129531250000000000 : ℝ)*(X 0 2+X 1 2)+(72700746817/33160000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4113/1024 : ℝ)) (lo := (1711/20000 : ℝ)) (hi := (3369/20000 : ℝ)) (c := (129485976291594297/129531250000000000 : ℝ)) (alpha := (72700746817/33160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1107217179/5000000000 : ℝ)*X 0 0+(217652427/400000000 : ℝ)*X 0 1+(1305210187/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356514851/10000000000 : ℝ)*X 1 0+(-290927999/1250000000 : ℝ)*X 1 1+(652605149/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133912877/250000000 : ℝ)*X 2 0+(1044168219/2000000000 : ℝ)*X 2 1+(-2327423817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2188525617/5000000000 : ℝ)*X 0 0+(833548809/2000000000 : ℝ)*X 0 1+(1149272231/2500000000 : ℝ)*X 0 2+(2188525617/5000000000 : ℝ)*X 1 0+(833548809/2000000000 : ℝ)*X 1 1+(1149272231/2500000000 : ℝ)*X 1 2+(2188525617/5000000000 : ℝ)*X 2 0+(833548809/2000000000 : ℝ)*X 2 1+(1149272231/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-442891871/2000000000 : ℝ)*X 0 0+(326360359/625000000 : ℝ)*X 0 1+(340023729/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2650559659/5000000000 : ℝ)*X 1 0+(-105394317/500000000 : ℝ)*X 1 1+(1088075803/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2650559451/5000000000 : ℝ)*X 2 0+(170011861/312500000 : ℝ)*X 2 1+(-2107886169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4377098841/10000000000 : ℝ)*X 0 0+(4595287367/10000000000 : ℝ)*X 0 1+(4169556473/10000000000 : ℝ)*X 0 2+(4377098841/10000000000 : ℝ)*X 1 0+(4595287367/10000000000 : ℝ)*X 1 1+(4169556473/10000000000 : ℝ)*X 1 2+(4377098841/10000000000 : ℝ)*X 2 0+(4595287367/10000000000 : ℝ)*X 2 1+(4169556473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7632200690701388657367/829000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1006375373/50000000000000 : ℝ)*(base19) + (887789127/50000000000000 : ℝ)*(base23) + (130710379/50000000000000 : ℝ)*(lower2) + (34097263/25000000000000 : ℝ)*(upper3) + (30507847/100000000000000 : ℝ)*(lower4) + (85812791163373/2500000000000 : ℝ)*(major0) + (85812791163373/2500000000000 : ℝ)*(major1) + (85812791163373/2500000000000 : ℝ)*(major2) + (226790571859997/5000000000000 : ℝ)*(sp0) + (2267928100528983/50000000000000 : ℝ)*(sp1) + (2267928219115229/50000000000000 : ℝ)*(sp2) + (582286347608003/25000000000000 : ℝ)*(sp3) + (11694152193/25000000000000 : ℝ)*(sp4) + (3876389057/20000000000000 : ℝ)*(sp7) + (2329164772377297/100000000000000 : ℝ)*(f.failure) + (566982276726089/12500000000000 : ℝ)*(f.sum) + (1212837253943/829000000000000000000000000 : ℝ)*base65 + (38615290179623/2590625000000000000000000000000 : ℝ)*base67 + (2910380238951627/2590625000000000000000000000000 : ℝ)*base70 + (15982561009167123/2590625000000000000000000000000 : ℝ)*base71 + (238199538607/829000000000000000000000000 : ℝ)*base74 + (383401050751627/2590625000000000000000000000000 : ℝ)*base76 + (41885045344023373/2590625000000000000000000000000 : ℝ)*base77 + (32230742451126627/2590625000000000000000000000000 : ℝ)*base80 + (4010563204717/829000000000000000000000000 : ℝ)*base81 + (16121893/2500000000000000000000 : ℝ)*base90 + (16121893/2500000000000000000000 : ℝ)*base92 + (16121893/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (65426304711848056502066487/6476562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (248966983/12500000000000 : ℝ)*(base19) + (335076763/20000000000000 : ℝ)*(base23) + (14465863/50000000000000 : ℝ)*(upper3) + (48514497/100000000000000 : ℝ)*(lower4) + (203443219/50000000000000 : ℝ)*(upper5) + (1730794470328853/50000000000000 : ℝ)*(major0) + (1730794470328853/50000000000000 : ℝ)*(major1) + (1730794470328853/50000000000000 : ℝ)*(major2) + (2652633713/10000000000000 : ℝ)*(sp1) + (21845844799/100000000000000 : ℝ)*(sp2) + (36594256690433/800000000000 : ℝ)*(sp4) + (4574253568231131/100000000000000 : ℝ)*(sp5) + (4574258565075511/100000000000000 : ℝ)*(sp6) + (2348895458277581/100000000000000 : ℝ)*(sp7) + (2348895458277581/100000000000000 : ℝ)*(f.failure) + (36594256690433/800000000000 : ℝ)*(f.sum) + (4068783669033/829000000000000000000000000 : ℝ)*base66 + (101818605255764739/25906250000000000000000000000000 : ℝ)*base67 + (396149029824702239/25906250000000000000000000000000 : ℝ)*base69 + (356485418712702239/25906250000000000000000000000000 : ℝ)*base71 + (2713550698391/414500000000000000000000000 : ℝ)*base74 + (334599382736420989/25906250000000000000000000000000 : ℝ)*base75 + (343748052516889739/25906250000000000000000000000000 : ℝ)*base77 + (322004321851608489/25906250000000000000000000000000 : ℝ)*base79 + (1563355039679/414500000000000000000000000 : ℝ)*base82 + (9886289/2500000000000000000000 : ℝ)*base90 + (9886289/2500000000000000000000 : ℝ)*base92 + (9886289/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1034_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36842731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3369/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1711/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (643/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14953/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1034_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1034_s4_0 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2218431301/10000000000 : ℝ)*x 0 + (2703816391/5000000000 : ℝ)*x 1 + (2625954493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2218431301/10000000000 : ℝ)^8227 ≤ (6733890616603/50000000000000 : ℝ)^6179 := by
    have hnat : (2218431301 : ℕ)^8227*50000000000000^6179 ≤ 6733890616603^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218431301 10000000000 6733890616603 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703816391/5000000000 : ℝ)^8227 ≤ (22053813985691/50000000000000 : ℝ)^6179 := by
    have hnat : (2703816391 : ℕ)^8227*50000000000000^6179 ≤ 22053813985691^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703816391 5000000000 22053813985691 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2625954493/5000000000 : ℝ)^8227 ≤ (8484918155899/20000000000000 : ℝ)^6179 := by
    have hnat : (2625954493 : ℕ)^8227*20000000000000^6179 ≤ 8484918155899^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625954493 5000000000 8484918155899 20000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2218431301/10000000000 : ℝ), (2703816391/5000000000 : ℝ), (2625954493/5000000000 : ℝ)] ![(6733890616603/50000000000000 : ℝ), (22053813985691/50000000000000 : ℝ), (8484918155899/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2218431301/10000000000 : ℝ)|^8227 ≤ (6733890616603/50000000000000 : ℝ)^6179
        have hw : |(-2218431301/10000000000 : ℝ)|=(2218431301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703816391/5000000000 : ℝ)|^8227 ≤ (22053813985691/50000000000000 : ℝ)^6179
        have hw : |(2703816391/5000000000 : ℝ)|=(2703816391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2625954493/5000000000 : ℝ)|^8227 ≤ (8484918155899/20000000000000 : ℝ)^6179
        have hw : |(2625954493/5000000000 : ℝ)|=(2625954493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s4_1 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167131319/312500000 : ℝ)*x 0 + (-2297668523/10000000000 : ℝ)*x 1 + (5251909041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167131319/312500000 : ℝ)^8227 ≤ (43463390352893/100000000000000 : ℝ)^6179 := by
    have hnat : (167131319 : ℕ)^8227*100000000000000^6179 ≤ 43463390352893^6179*312500000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167131319 312500000 43463390352893 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2297668523/10000000000 : ℝ)^8227 ≤ (352800456317/2500000000000 : ℝ)^6179 := by
    have hnat : (2297668523 : ℕ)^8227*2500000000000^6179 ≤ 352800456317^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2297668523 10000000000 352800456317 2500000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5251909041/10000000000 : ℝ)^8227 ≤ (42424591371039/100000000000000 : ℝ)^6179 := by
    have hnat : (5251909041 : ℕ)^8227*100000000000000^6179 ≤ 42424591371039^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251909041 10000000000 42424591371039 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167131319/312500000 : ℝ), (-2297668523/10000000000 : ℝ), (5251909041/10000000000 : ℝ)] ![(43463390352893/100000000000000 : ℝ), (352800456317/2500000000000 : ℝ), (42424591371039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167131319/312500000 : ℝ)|^8227 ≤ (43463390352893/100000000000000 : ℝ)^6179
        have hw : |(167131319/312500000 : ℝ)|=(167131319/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2297668523/10000000000 : ℝ)|^8227 ≤ (352800456317/2500000000000 : ℝ)^6179
        have hw : |(-2297668523/10000000000 : ℝ)|=(2297668523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5251909041/10000000000 : ℝ)|^8227 ≤ (42424591371039/100000000000000 : ℝ)^6179
        have hw : |(5251909041/10000000000 : ℝ)|=(5251909041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s4_2 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1337050577/2500000000 : ℝ)*x 0 + (5251908923/10000000000 : ℝ)*x 1 + (-2297668547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337050577/2500000000 : ℝ)^8227 ≤ (21731695717461/50000000000000 : ℝ)^6179 := by
    have hnat : (1337050577 : ℕ)^8227*50000000000000^6179 ≤ 21731695717461^6179*2500000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337050577 2500000000 21731695717461 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5251908923/10000000000 : ℝ)^8227 ≤ (4242459010191/10000000000000 : ℝ)^6179 := by
    have hnat : (5251908923 : ℕ)^8227*10000000000000^6179 ≤ 4242459010191^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251908923 10000000000 4242459010191 10000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2297668547/10000000000 : ℝ)^8227 ≤ (7056009224471/50000000000000 : ℝ)^6179 := by
    have hnat : (2297668547 : ℕ)^8227*50000000000000^6179 ≤ 7056009224471^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2297668547 10000000000 7056009224471 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337050577/2500000000 : ℝ), (5251908923/10000000000 : ℝ), (-2297668547/10000000000 : ℝ)] ![(21731695717461/50000000000000 : ℝ), (4242459010191/10000000000000 : ℝ), (7056009224471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337050577/2500000000 : ℝ)|^8227 ≤ (21731695717461/50000000000000 : ℝ)^6179
        have hw : |(1337050577/2500000000 : ℝ)|=(1337050577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5251908923/10000000000 : ℝ)|^8227 ≤ (4242459010191/10000000000000 : ℝ)^6179
        have hw : |(5251908923/10000000000 : ℝ)|=(5251908923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2297668547/10000000000 : ℝ)|^8227 ≤ (7056009224471/50000000000000 : ℝ)^6179
        have hw : |(-2297668547/10000000000 : ℝ)|=(2297668547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s4_3 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (547428129/1250000000 : ℝ)*x 0 + (4230473761/10000000000 : ℝ)*x 1 + (4533733171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547428129/1250000000 : ℝ)^8227 ≤ (8327344209417/25000000000000 : ℝ)^6179 := by
    have hnat : (547428129 : ℕ)^8227*25000000000000^6179 ≤ 8327344209417^6179*1250000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547428129 1250000000 8327344209417 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4230473761/10000000000 : ℝ)^8227 ≤ (3976192862811/12500000000000 : ℝ)^6179 := by
    have hnat : (4230473761 : ℕ)^8227*12500000000000^6179 ≤ 3976192862811^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230473761 10000000000 3976192862811 12500000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4533733171/10000000000 : ℝ)^8227 ≤ (8720270060097/25000000000000 : ℝ)^6179 := by
    have hnat : (4533733171 : ℕ)^8227*25000000000000^6179 ≤ 8720270060097^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533733171 10000000000 8720270060097 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547428129/1250000000 : ℝ), (4230473761/10000000000 : ℝ), (4533733171/10000000000 : ℝ)] ![(8327344209417/25000000000000 : ℝ), (3976192862811/12500000000000 : ℝ), (8720270060097/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547428129/1250000000 : ℝ)|^8227 ≤ (8327344209417/25000000000000 : ℝ)^6179
        have hw : |(547428129/1250000000 : ℝ)|=(547428129/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4230473761/10000000000 : ℝ)|^8227 ≤ (3976192862811/12500000000000 : ℝ)^6179
        have hw : |(4230473761/10000000000 : ℝ)|=(4230473761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4533733171/10000000000 : ℝ)|^8227 ≤ (8720270060097/25000000000000 : ℝ)^6179
        have hw : |(4533733171/10000000000 : ℝ)|=(4533733171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s4_4 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-443688019/2000000000 : ℝ)*x 0 + (656546399/1250000000 : ℝ)*x 1 + (5407168473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (443688019/2000000000 : ℝ)^8227 ≤ (2693570463057/20000000000000 : ℝ)^6179 := by
    have hnat : (443688019 : ℕ)^8227*20000000000000^6179 ≤ 2693570463057^6179*2000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443688019 2000000000 2693570463057 20000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656546399/1250000000 : ℝ)^8227 ≤ (10607390507607/25000000000000 : ℝ)^6179 := by
    have hnat : (656546399 : ℕ)^8227*25000000000000^6179 ≤ 10607390507607^6179*1250000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656546399 1250000000 10607390507607 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407168473/10000000000 : ℝ)^8227 ≤ (44102585647537/100000000000000 : ℝ)^6179 := by
    have hnat : (5407168473 : ℕ)^8227*100000000000000^6179 ≤ 44102585647537^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407168473 10000000000 44102585647537 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-443688019/2000000000 : ℝ), (656546399/1250000000 : ℝ), (5407168473/10000000000 : ℝ)] ![(2693570463057/20000000000000 : ℝ), (10607390507607/25000000000000 : ℝ), (44102585647537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-443688019/2000000000 : ℝ)|^8227 ≤ (2693570463057/20000000000000 : ℝ)^6179
        have hw : |(-443688019/2000000000 : ℝ)|=(443688019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(656546399/1250000000 : ℝ)|^8227 ≤ (10607390507607/25000000000000 : ℝ)^6179
        have hw : |(656546399/1250000000 : ℝ)|=(656546399/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407168473/10000000000 : ℝ)|^8227 ≤ (44102585647537/100000000000000 : ℝ)^6179
        have hw : |(5407168473/10000000000 : ℝ)|=(5407168473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s4_5 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309081353/10000000000 : ℝ)*x 0 + (-2142409253/10000000000 : ℝ)*x 1 + (5407168339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309081353/10000000000 : ℝ)^8227 ≤ (43040605150293/100000000000000 : ℝ)^6179 := by
    have hnat : (5309081353 : ℕ)^8227*100000000000000^6179 ≤ 43040605150293^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309081353 10000000000 43040605150293 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2142409253/10000000000 : ℝ)^8227 ≤ (1607101329737/12500000000000 : ℝ)^6179 := by
    have hnat : (2142409253 : ℕ)^8227*12500000000000^6179 ≤ 1607101329737^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142409253 10000000000 1607101329737 12500000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407168339/10000000000 : ℝ)^8227 ≤ (44102584192339/100000000000000 : ℝ)^6179 := by
    have hnat : (5407168339 : ℕ)^8227*100000000000000^6179 ≤ 44102584192339^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407168339 10000000000 44102584192339 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309081353/10000000000 : ℝ), (-2142409253/10000000000 : ℝ), (5407168339/10000000000 : ℝ)] ![(43040605150293/100000000000000 : ℝ), (1607101329737/12500000000000 : ℝ), (44102584192339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309081353/10000000000 : ℝ)|^8227 ≤ (43040605150293/100000000000000 : ℝ)^6179
        have hw : |(5309081353/10000000000 : ℝ)|=(5309081353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2142409253/10000000000 : ℝ)|^8227 ≤ (1607101329737/12500000000000 : ℝ)^6179
        have hw : |(-2142409253/10000000000 : ℝ)|=(2142409253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407168339/10000000000 : ℝ)|^8227 ≤ (44102584192339/100000000000000 : ℝ)^6179
        have hw : |(5407168339/10000000000 : ℝ)|=(5407168339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s4_6 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309081361/10000000000 : ℝ)*x 0 + (1351792097/2500000000 : ℝ)*x 1 + (-267801147/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309081361/10000000000 : ℝ)^8227 ≤ (8608121047329/20000000000000 : ℝ)^6179 := by
    have hnat : (5309081361 : ℕ)^8227*20000000000000^6179 ≤ 8608121047329^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309081361 10000000000 8608121047329 20000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351792097/2500000000 : ℝ)^8227 ≤ (2756411545279/6250000000000 : ℝ)^6179 := by
    have hnat : (1351792097 : ℕ)^8227*6250000000000^6179 ≤ 2756411545279^6179*2500000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351792097 2500000000 2756411545279 6250000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (267801147/1250000000 : ℝ)^8227 ≤ (50221914151/390625000000 : ℝ)^6179 := by
    have hnat : (267801147 : ℕ)^8227*390625000000^6179 ≤ 50221914151^6179*1250000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267801147 1250000000 50221914151 390625000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309081361/10000000000 : ℝ), (1351792097/2500000000 : ℝ), (-267801147/1250000000 : ℝ)] ![(8608121047329/20000000000000 : ℝ), (2756411545279/6250000000000 : ℝ), (50221914151/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309081361/10000000000 : ℝ)|^8227 ≤ (8608121047329/20000000000000 : ℝ)^6179
        have hw : |(5309081361/10000000000 : ℝ)|=(5309081361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351792097/2500000000 : ℝ)|^8227 ≤ (2756411545279/6250000000000 : ℝ)^6179
        have hw : |(1351792097/2500000000 : ℝ)|=(1351792097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-267801147/1250000000 : ℝ)|^8227 ≤ (50221914151/390625000000 : ℝ)^6179
        have hw : |(-267801147/1250000000 : ℝ)|=(267801147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s4_7 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (54743023/125000000 : ℝ)*x 0 + (90656647/200000000 : ℝ)*x 1 + (1057844607/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (54743023/125000000 : ℝ)^8227 ≤ (33309547049219/100000000000000 : ℝ)^6179 := by
    have hnat : (54743023 : ℕ)^8227*100000000000000^6179 ≤ 33309547049219^6179*125000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54743023 125000000 33309547049219 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90656647/200000000 : ℝ)^8227 ≤ (8717963198809/25000000000000 : ℝ)^6179 := by
    have hnat : (90656647 : ℕ)^8227*25000000000000^6179 ≤ 8717963198809^6179*200000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90656647 200000000 8717963198809 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057844607/2500000000 : ℝ)^8227 ≤ (15909300071113/50000000000000 : ℝ)^6179 := by
    have hnat : (1057844607 : ℕ)^8227*50000000000000^6179 ≤ 15909300071113^6179*2500000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057844607 2500000000 15909300071113 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(54743023/125000000 : ℝ), (90656647/200000000 : ℝ), (1057844607/2500000000 : ℝ)] ![(33309547049219/100000000000000 : ℝ), (8717963198809/25000000000000 : ℝ), (15909300071113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(54743023/125000000 : ℝ)|^8227 ≤ (33309547049219/100000000000000 : ℝ)^6179
        have hw : |(54743023/125000000 : ℝ)|=(54743023/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(90656647/200000000 : ℝ)|^8227 ≤ (8717963198809/25000000000000 : ℝ)^6179
        have hw : |(90656647/200000000 : ℝ)|=(90656647/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1057844607/2500000000 : ℝ)|^8227 ≤ (15909300071113/50000000000000 : ℝ)^6179
        have hw : |(1057844607/2500000000 : ℝ)|=(1057844607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1034_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36842731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14953/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (643/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (1369/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14249/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14953/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (643/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14953/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (643/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14953/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (643/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14953/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (643/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14953/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (643/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14953/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (643/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (643/6250 : ℝ) ^ (4113/1024 : ℝ) ≤ (10787653115165413/100000000000000000000 : ℝ) := by
    have hpowers : (643/6250 : ℝ)^4113 ≤ (10787653115165413/100000000000000000000 : ℝ)^1024 := by
      have hnat : (643 : ℕ)^4113*100000000000000000000^1024 ≤ 10787653115165413^1024*6250^4113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        643 6250 10787653115165413 100000000000000000000 4113 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (643/6250 : ℝ)) (X := (10787653115165413/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14953/100000 : ℝ) ^ (4113/1024 : ℝ) ≤ (12110234219906281/25000000000000000000 : ℝ) := by
    have hpowers : (14953/100000 : ℝ)^4113 ≤ (12110234219906281/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14953 : ℕ)^4113*25000000000000000000^1024 ≤ 12110234219906281^1024*100000^4113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14953 100000 12110234219906281 25000000000000000000 4113 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14953/100000 : ℝ)) (X := (12110234219906281/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010787653115165413/50000000000000000000 : ℝ) ≤ (2000107421949167/2000000000000000 : ℝ) ^ (4113/1024 : ℝ) := by
    have hpowers : (50010787653115165413/50000000000000000000 : ℝ)^1024 ≤ (2000107421949167/2000000000000000 : ℝ)^4113 := by
      have hnat : (50010787653115165413 : ℕ)^1024*2000000000000000^4113 ≤ 2000107421949167^4113*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010787653115165413 50000000000000000000 2000107421949167 2000000000000000 1024 4113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000107421949167/2000000000000000 : ℝ)) (X := (50010787653115165413/50000000000000000000 : ℝ)) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100059228589994790537/100000000000000000000 : ℝ) ≤ (10001474266750241/10000000000000000 : ℝ) ^ (4113/1024 : ℝ) := by
    have hpowers : (100059228589994790537/100000000000000000000 : ℝ)^1024 ≤ (10001474266750241/10000000000000000 : ℝ)^4113 := by
      have hnat : (100059228589994790537 : ℕ)^1024*10000000000000000^4113 ≤ 10001474266750241^4113*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100059228589994790537 100000000000000000000 10001474266750241 10000000000000000 1024 4113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001474266750241/10000000000000000 : ℝ)) (X := (100059228589994790537/100000000000000000000 : ℝ)) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12512110234219906281/12500000000000000000 : ℝ) ≤ (10002411423754647/10000000000000000 : ℝ) ^ (4113/1024 : ℝ) := by
    have hpowers : (12512110234219906281/12500000000000000000 : ℝ)^1024 ≤ (10002411423754647/10000000000000000 : ℝ)^4113 := by
      have hnat : (12512110234219906281 : ℕ)^1024*10000000000000000^4113 ≤ 10002411423754647^4113*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12512110234219906281 12500000000000000000 10002411423754647 10000000000000000 1024 4113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002411423754647/10000000000000000 : ℝ)) (X := (12512110234219906281/12500000000000000000 : ℝ)) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10787653115165413/100000000000000000000 : ℝ) ≤ ((46633222674441662419/46650000000000000000 : ℝ)+2*(468578502203/233250000000000 : ℝ)*(643/6250 : ℝ))^(4113/1024 : ℝ) := by
    rw [show (46633222674441662419/46650000000000000000 : ℝ)+2*(468578502203/233250000000000 : ℝ)*(643/6250 : ℝ)=(2000107421949167/2000000000000000 : ℝ) by norm_num, show 1+2*(10787653115165413/100000000000000000000 : ℝ)=(50010787653115165413/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12110234219906281/25000000000000000000 : ℝ)+(10787653115165413/100000000000000000000 : ℝ) ≤ ((46633222674441662419/46650000000000000000 : ℝ)+(468578502203/233250000000000 : ℝ)*((14953/100000 : ℝ)+(643/6250 : ℝ)))^(4113/1024 : ℝ) := by
    rw [show (46633222674441662419/46650000000000000000 : ℝ)+(468578502203/233250000000000 : ℝ)*((14953/100000 : ℝ)+(643/6250 : ℝ))=(10001474266750241/10000000000000000 : ℝ) by norm_num, show 1+(12110234219906281/25000000000000000000 : ℝ)+(10787653115165413/100000000000000000000 : ℝ)=(100059228589994790537/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12110234219906281/25000000000000000000 : ℝ) ≤ ((46633222674441662419/46650000000000000000 : ℝ)+2*(468578502203/233250000000000 : ℝ)*(14953/100000 : ℝ))^(4113/1024 : ℝ) := by
    rw [show (46633222674441662419/46650000000000000000 : ℝ)+2*(468578502203/233250000000000 : ℝ)*(14953/100000 : ℝ)=(10002411423754647/10000000000000000 : ℝ) by norm_num, show 1+2*(12110234219906281/25000000000000000000 : ℝ)=(12512110234219906281/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46633222674441662419/46650000000000000000 : ℝ)*(X 1 0+X 2 0)+(468578502203/233250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4113/1024 : ℝ)) (lo := (643/6250 : ℝ)) (hi := (14953/100000 : ℝ)) (c := (46633222674441662419/46650000000000000000 : ℝ)) (alpha := (468578502203/233250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46633222674441662419/46650000000000000000 : ℝ)*(X 0 1+X 2 1)+(468578502203/233250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4113/1024 : ℝ)) (lo := (643/6250 : ℝ)) (hi := (14953/100000 : ℝ)) (c := (46633222674441662419/46650000000000000000 : ℝ)) (alpha := (468578502203/233250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46633222674441662419/46650000000000000000 : ℝ)*(X 0 2+X 1 2)+(468578502203/233250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4113/1024 : ℝ)) (lo := (643/6250 : ℝ)) (hi := (14953/100000 : ℝ)) (c := (46633222674441662419/46650000000000000000 : ℝ)) (alpha := (468578502203/233250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2218431301/10000000000 : ℝ)*X 0 0+(2703816391/5000000000 : ℝ)*X 0 1+(2625954493/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167131319/312500000 : ℝ)*X 1 0+(-2297668523/10000000000 : ℝ)*X 1 1+(5251909041/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337050577/2500000000 : ℝ)*X 2 0+(5251908923/10000000000 : ℝ)*X 2 1+(-2297668547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((547428129/1250000000 : ℝ)*X 0 0+(4230473761/10000000000 : ℝ)*X 0 1+(4533733171/10000000000 : ℝ)*X 0 2+(547428129/1250000000 : ℝ)*X 1 0+(4230473761/10000000000 : ℝ)*X 1 1+(4533733171/10000000000 : ℝ)*X 1 2+(547428129/1250000000 : ℝ)*X 2 0+(4230473761/10000000000 : ℝ)*X 2 1+(4533733171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-443688019/2000000000 : ℝ)*X 0 0+(656546399/1250000000 : ℝ)*X 0 1+(5407168473/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309081353/10000000000 : ℝ)*X 1 0+(-2142409253/10000000000 : ℝ)*X 1 1+(5407168339/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309081361/10000000000 : ℝ)*X 2 0+(1351792097/2500000000 : ℝ)*X 2 1+(-267801147/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((54743023/125000000 : ℝ)*X 0 0+(90656647/200000000 : ℝ)*X 0 1+(1057844607/2500000000 : ℝ)*X 0 2+(54743023/125000000 : ℝ)*X 1 0+(90656647/200000000 : ℝ)*X 1 1+(1057844607/2500000000 : ℝ)*X 1 2+(54743023/125000000 : ℝ)*X 2 0+(90656647/200000000 : ℝ)*X 2 1+(1057844607/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4640720716423061663644223283/777500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1265985537/100000000000000 : ℝ)*(base19) + (1362525379/100000000000000 : ℝ)*(base23) + (12585407/100000000000000 : ℝ)*(lower2) + (3830639/2500000000000 : ℝ)*(upper3) + (25501247/20000000000000 : ℝ)*(upper5) + (4859613501093343/100000000000000 : ℝ)*(major0) + (4859613501093343/100000000000000 : ℝ)*(major1) + (4859613501093343/100000000000000 : ℝ)*(major2) + (3210828406023547/50000000000000 : ℝ)*(sp0) + (1605421666960613/25000000000000 : ℝ)*(sp1) + (6421686571302611/100000000000000 : ℝ)*(sp2) + (824380576182927/25000000000000 : ℝ)*(sp3) + (972555653/3125000000000 : ℝ)*(sp4) + (16564667891/100000000000000 : ℝ)*(sp7) + (8243847173499/250000000000 : ℝ)*(f.failure) + (642168793382799/10000000000000 : ℝ)*(f.sum) + (1131950394587/1457812500000000000000000000 : ℝ)*base66 + (7164578408569976717/4665000000000000000000000000000000 : ℝ)*base67 + (25227697583119976717/4665000000000000000000000000000000 : ℝ)*base69 + (35006260888540023283/4665000000000000000000000000000000 : ℝ)*base72 + (12360613087451/2915625000000000000000000000 : ℝ)*base73 + (131945496946519976717/4665000000000000000000000000000000 : ℝ)*base75 + (17904800870920023283/4665000000000000000000000000000000 : ℝ)*base78 + (14089703671924976717/4665000000000000000000000000000000 : ℝ)*base79 + (57440672502583/23325000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (48269/6250000000000000000 : ℝ)*base89 + (48269/6250000000000000000 : ℝ)*base91 + (48269/6250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (182923974067318151315115821/48593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (115494991/12500000000000 : ℝ)*(base19) + (1125158887/100000000000000 : ℝ)*(base23) + (27314663/25000000000000 : ℝ)*(upper2) + (306848007/100000000000000 : ℝ)*(upper5) + (305541416058347/6250000000000 : ℝ)*(major0) + (305541416058347/6250000000000 : ℝ)*(major1) + (305541416058347/6250000000000 : ℝ)*(major2) + (767800007/50000000000000 : ℝ)*(sp0) + (23292382029/100000000000000 : ℝ)*(sp1) + (10673724713/50000000000000 : ℝ)*(sp2) + (3230036595499557/50000000000000 : ℝ)*(sp4) + (646005051025717/10000000000000 : ℝ)*(sp5) + (3230026126995407/50000000000000 : ℝ)*(sp6) + (3317250461789567/100000000000000 : ℝ)*(sp7) + (3317250461789567/100000000000000 : ℝ)*(f.failure) + (6460074726599127/100000000000000 : ℝ)*(f.sum) + (4998553549897/5831250000000000000000000000 : ℝ)*base66 + (856871275094986393/291562500000000000000000000000000 : ℝ)*base67 + (5358437631273736393/291562500000000000000000000000000 : ℝ)*base69 + (2932073481161236393/291562500000000000000000000000000 : ℝ)*base71 + (149069073762613/23325000000000000000000000000 : ℝ)*base74 + (11223886136033423893/291562500000000000000000000000000 : ℝ)*base75 + (1485858748454986393/291562500000000000000000000000000 : ℝ)*base77 + (11298706034469361393/291562500000000000000000000000000 : ℝ)*base79 + (10552472679181/11662500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4412523/2500000000000000000000 : ℝ)*base90 + (4412523/2500000000000000000000 : ℝ)*base92 + (4412523/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1034_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36842731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14953/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (643/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1369/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14249/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1034_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1034_s5_0 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2219357039/10000000000 : ℝ)*x 0 + (1079586827/2000000000 : ℝ)*x 1 + (2630500363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2219357039/10000000000 : ℝ)^8227 ≤ (3368816126133/25000000000000 : ℝ)^6179 := by
    have hnat : (2219357039 : ℕ)^8227*25000000000000^6179 ≤ 3368816126133^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219357039 10000000000 3368816126133 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079586827/2000000000 : ℝ)^8227 ≤ (8800466397289/20000000000000 : ℝ)^6179 := by
    have hnat : (1079586827 : ℕ)^8227*20000000000000^6179 ≤ 8800466397289^6179*2000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079586827 2000000000 8800466397289 20000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630500363/5000000000 : ℝ)^8227 ≤ (5315300436647/12500000000000 : ℝ)^6179 := by
    have hnat : (2630500363 : ℕ)^8227*12500000000000^6179 ≤ 5315300436647^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630500363 5000000000 5315300436647 12500000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2219357039/10000000000 : ℝ), (1079586827/2000000000 : ℝ), (2630500363/5000000000 : ℝ)] ![(3368816126133/25000000000000 : ℝ), (8800466397289/20000000000000 : ℝ), (5315300436647/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2219357039/10000000000 : ℝ)|^8227 ≤ (3368816126133/25000000000000 : ℝ)^6179
        have hw : |(-2219357039/10000000000 : ℝ)|=(2219357039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079586827/2000000000 : ℝ)|^8227 ≤ (8800466397289/20000000000000 : ℝ)^6179
        have hw : |(1079586827/2000000000 : ℝ)|=(1079586827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630500363/5000000000 : ℝ)|^8227 ≤ (5315300436647/12500000000000 : ℝ)^6179
        have hw : |(2630500363/5000000000 : ℝ)|=(2630500363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s5_1 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345794439/10000000000 : ℝ)*x 0 + (-2288887571/10000000000 : ℝ)*x 1 + (2630500371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345794439/10000000000 : ℝ)^8227 ≤ (5429667440881/12500000000000 : ℝ)^6179 := by
    have hnat : (5345794439 : ℕ)^8227*12500000000000^6179 ≤ 5429667440881^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345794439 10000000000 5429667440881 12500000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2288887571/10000000000 : ℝ)^8227 ≤ (14040256789909/100000000000000 : ℝ)^6179 := by
    have hnat : (2288887571 : ℕ)^8227*100000000000000^6179 ≤ 14040256789909^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288887571 10000000000 14040256789909 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630500371/5000000000 : ℝ)^8227 ≤ (531530045817/1250000000000 : ℝ)^6179 := by
    have hnat : (2630500371 : ℕ)^8227*1250000000000^6179 ≤ 531530045817^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630500371 5000000000 531530045817 1250000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345794439/10000000000 : ℝ), (-2288887571/10000000000 : ℝ), (2630500371/5000000000 : ℝ)] ![(5429667440881/12500000000000 : ℝ), (14040256789909/100000000000000 : ℝ), (531530045817/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345794439/10000000000 : ℝ)|^8227 ≤ (5429667440881/12500000000000 : ℝ)^6179
        have hw : |(5345794439/10000000000 : ℝ)|=(5345794439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2288887571/10000000000 : ℝ)|^8227 ≤ (14040256789909/100000000000000 : ℝ)^6179
        have hw : |(-2288887571/10000000000 : ℝ)|=(2288887571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630500371/5000000000 : ℝ)|^8227 ≤ (531530045817/1250000000000 : ℝ)^6179
        have hw : |(2630500371/5000000000 : ℝ)|=(2630500371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s5_2 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069158887/2000000000 : ℝ)*x 0 + (5261000663/10000000000 : ℝ)*x 1 + (-3576387/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069158887/2000000000 : ℝ)^8227 ≤ (21718669741887/50000000000000 : ℝ)^6179 := by
    have hnat : (1069158887 : ℕ)^8227*50000000000000^6179 ≤ 21718669741887^6179*2000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069158887 2000000000 21718669741887 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261000663/10000000000 : ℝ)^8227 ≤ (42522402815201/100000000000000 : ℝ)^6179 := by
    have hnat : (5261000663 : ℕ)^8227*100000000000000^6179 ≤ 42522402815201^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261000663 10000000000 42522402815201 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3576387/15625000 : ℝ)^8227 ≤ (2808051536027/20000000000000 : ℝ)^6179 := by
    have hnat : (3576387 : ℕ)^8227*20000000000000^6179 ≤ 2808051536027^6179*15625000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3576387 15625000 2808051536027 20000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069158887/2000000000 : ℝ), (5261000663/10000000000 : ℝ), (-3576387/15625000 : ℝ)] ![(21718669741887/50000000000000 : ℝ), (42522402815201/100000000000000 : ℝ), (2808051536027/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069158887/2000000000 : ℝ)|^8227 ≤ (21718669741887/50000000000000 : ℝ)^6179
        have hw : |(1069158887/2000000000 : ℝ)|=(1069158887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261000663/10000000000 : ℝ)|^8227 ≤ (42522402815201/100000000000000 : ℝ)^6179
        have hw : |(5261000663/10000000000 : ℝ)|=(5261000663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3576387/15625000 : ℝ)|^8227 ≤ (2808051536027/20000000000000 : ℝ)^6179
        have hw : |(-3576387/15625000 : ℝ)|=(3576387/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s5_3 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4379961207/10000000000 : ℝ)*x 0 + (2124349573/5000000000 : ℝ)*x 1 + (112884153/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379961207/10000000000 : ℝ)^8227 ≤ (33314806690831/100000000000000 : ℝ)^6179 := by
    have hnat : (4379961207 : ℕ)^8227*100000000000000^6179 ≤ 33314806690831^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379961207 10000000000 33314806690831 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124349573/5000000000 : ℝ)^8227 ≤ (31992133367317/100000000000000 : ℝ)^6179 := by
    have hnat : (2124349573 : ℕ)^8227*100000000000000^6179 ≤ 31992133367317^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124349573 5000000000 31992133367317 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112884153/250000000 : ℝ)^8227 ≤ (2168316245567/6250000000000 : ℝ)^6179 := by
    have hnat : (112884153 : ℕ)^8227*6250000000000^6179 ≤ 2168316245567^6179*250000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112884153 250000000 2168316245567 6250000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379961207/10000000000 : ℝ), (2124349573/5000000000 : ℝ), (112884153/250000000 : ℝ)] ![(33314806690831/100000000000000 : ℝ), (31992133367317/100000000000000 : ℝ), (2168316245567/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379961207/10000000000 : ℝ)|^8227 ≤ (33314806690831/100000000000000 : ℝ)^6179
        have hw : |(4379961207/10000000000 : ℝ)|=(4379961207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2124349573/5000000000 : ℝ)|^8227 ≤ (31992133367317/100000000000000 : ℝ)^6179
        have hw : |(2124349573/5000000000 : ℝ)|=(2124349573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112884153/250000000 : ℝ)|^8227 ≤ (2168316245567/6250000000000 : ℝ)^6179
        have hw : |(112884153/250000000 : ℝ)|=(112884153/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s5_4 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1109681443/5000000000 : ℝ)*x 0 + (1315339621/2500000000 : ℝ)*x 1 + (674696881/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1109681443/5000000000 : ℝ)^8227 ≤ (3368827943119/25000000000000 : ℝ)^6179 := by
    have hnat : (1109681443 : ℕ)^8227*25000000000000^6179 ≤ 3368827943119^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109681443 5000000000 3368827943119 25000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315339621/2500000000 : ℝ)^8227 ≤ (42526253548699/100000000000000 : ℝ)^6179 := by
    have hnat : (1315339621 : ℕ)^8227*100000000000000^6179 ≤ 42526253548699^6179*2500000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315339621 2500000000 42526253548699 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674696881/1250000000 : ℝ)^8227 ≤ (8799686932853/20000000000000 : ℝ)^6179 := by
    have hnat : (674696881 : ℕ)^8227*20000000000000^6179 ≤ 8799686932853^6179*1250000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674696881 1250000000 8799686932853 20000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1109681443/5000000000 : ℝ), (1315339621/2500000000 : ℝ), (674696881/1250000000 : ℝ)] ![(3368827943119/25000000000000 : ℝ), (42526253548699/100000000000000 : ℝ), (8799686932853/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1109681443/5000000000 : ℝ)|^8227 ≤ (3368827943119/25000000000000 : ℝ)^6179
        have hw : |(-1109681443/5000000000 : ℝ)|=(1109681443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315339621/2500000000 : ℝ)|^8227 ≤ (42526253548699/100000000000000 : ℝ)^6179
        have hw : |(1315339621/2500000000 : ℝ)|=(1315339621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674696881/1250000000 : ℝ)|^8227 ≤ (8799686932853/20000000000000 : ℝ)^6179
        have hw : |(674696881/1250000000 : ℝ)|=(674696881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s5_5 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655696481/5000000000 : ℝ)*x 0 + (-269039183/1250000000 : ℝ)*x 1 + (5397575019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655696481/5000000000 : ℝ)^8227 ≤ (5383194806377/12500000000000 : ℝ)^6179 := by
    have hnat : (2655696481 : ℕ)^8227*12500000000000^6179 ≤ 5383194806377^6179*5000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655696481 5000000000 5383194806377 12500000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269039183/1250000000 : ℝ)^8227 ≤ (6468003592981/50000000000000 : ℝ)^6179 := by
    have hnat : (269039183 : ℕ)^8227*50000000000000^6179 ≤ 6468003592981^6179*1250000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269039183 1250000000 6468003592981 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397575019/10000000000 : ℝ)^8227 ≤ (43998434349519/100000000000000 : ℝ)^6179 := by
    have hnat : (5397575019 : ℕ)^8227*100000000000000^6179 ≤ 43998434349519^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397575019 10000000000 43998434349519 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655696481/5000000000 : ℝ), (-269039183/1250000000 : ℝ), (5397575019/10000000000 : ℝ)] ![(5383194806377/12500000000000 : ℝ), (6468003592981/50000000000000 : ℝ), (43998434349519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655696481/5000000000 : ℝ)|^8227 ≤ (5383194806377/12500000000000 : ℝ)^6179
        have hw : |(2655696481/5000000000 : ℝ)|=(2655696481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-269039183/1250000000 : ℝ)|^8227 ≤ (6468003592981/50000000000000 : ℝ)^6179
        have hw : |(-269039183/1250000000 : ℝ)|=(269039183/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397575019/10000000000 : ℝ)|^8227 ≤ (43998434349519/100000000000000 : ℝ)^6179
        have hw : |(5397575019/10000000000 : ℝ)|=(5397575019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s5_6 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311393099/10000000000 : ℝ)*x 0 + (1079514997/2000000000 : ℝ)*x 1 + (-86092533/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311393099/10000000000 : ℝ)^8227 ≤ (43065559930007/100000000000000 : ℝ)^6179 := by
    have hnat : (5311393099 : ℕ)^8227*100000000000000^6179 ≤ 43065559930007^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311393099 10000000000 43065559930007 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079514997/2000000000 : ℝ)^8227 ≤ (43998433980507/100000000000000 : ℝ)^6179 := by
    have hnat : (1079514997 : ℕ)^8227*100000000000000^6179 ≤ 43998433980507^6179*2000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079514997 2000000000 43998433980507 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86092533/400000000 : ℝ)^8227 ≤ (6468003036817/50000000000000 : ℝ)^6179 := by
    have hnat : (86092533 : ℕ)^8227*50000000000000^6179 ≤ 6468003036817^6179*400000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86092533 400000000 6468003036817 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311393099/10000000000 : ℝ), (1079514997/2000000000 : ℝ), (-86092533/400000000 : ℝ)] ![(43065559930007/100000000000000 : ℝ), (43998433980507/100000000000000 : ℝ), (6468003036817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311393099/10000000000 : ℝ)|^8227 ≤ (43065559930007/100000000000000 : ℝ)^6179
        have hw : |(5311393099/10000000000 : ℝ)|=(5311393099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079514997/2000000000 : ℝ)|^8227 ≤ (43998433980507/100000000000000 : ℝ)^6179
        have hw : |(1079514997/2000000000 : ℝ)|=(1079514997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86092533/400000000 : ℝ)|^8227 ≤ (6468003036817/50000000000000 : ℝ)^6179
        have hw : |(-86092533/400000000 : ℝ)|=(86092533/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1034_s5_7 (p : ℝ) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4379972267/10000000000 : ℝ)*x 0 + (1128667347/2500000000 : ℝ)*x 1 + (4249398869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379972267/10000000000 : ℝ)^8227 ≤ (16657459348977/50000000000000 : ℝ)^6179 := by
    have hnat : (4379972267 : ℕ)^8227*50000000000000^6179 ≤ 16657459348977^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379972267 10000000000 16657459348977 50000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128667347/2500000000 : ℝ)^8227 ≤ (6937186517443/20000000000000 : ℝ)^6179 := by
    have hnat : (1128667347 : ℕ)^8227*20000000000000^6179 ≤ 6937186517443^6179*2500000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128667347 2500000000 6937186517443 20000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4249398869/10000000000 : ℝ)^8227 ≤ (31999148704123/100000000000000 : ℝ)^6179 := by
    have hnat : (4249398869 : ℕ)^8227*100000000000000^6179 ≤ 31999148704123^6179*10000000000^8227 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249398869 10000000000 31999148704123 100000000000000 8227 6179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8227/2048 : ℝ)) 8227 6179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379972267/10000000000 : ℝ), (1128667347/2500000000 : ℝ), (4249398869/10000000000 : ℝ)] ![(16657459348977/50000000000000 : ℝ), (6937186517443/20000000000000 : ℝ), (31999148704123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379972267/10000000000 : ℝ)|^8227 ≤ (16657459348977/50000000000000 : ℝ)^6179
        have hw : |(4379972267/10000000000 : ℝ)|=(4379972267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1128667347/2500000000 : ℝ)|^8227 ≤ (6937186517443/20000000000000 : ℝ)^6179
        have hw : |(1128667347/2500000000 : ℝ)|=(1128667347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4249398869/10000000000 : ℝ)|^8227 ≤ (31999148704123/100000000000000 : ℝ)^6179
        have hw : |(4249398869/10000000000 : ℝ)|=(4249398869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1034_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36842731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14249/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1369/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5573/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7023/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14249/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1369/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14249/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1369/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14249/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1369/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14249/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1369/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14249/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1369/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14249/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1369/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1369/12500 : ℝ) ^ (4113/1024 : ℝ) ≤ (13868446986887389/100000000000000000000 : ℝ) := by
    have hpowers : (1369/12500 : ℝ)^4113 ≤ (13868446986887389/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1369 : ℕ)^4113*100000000000000000000^1024 ≤ 13868446986887389^1024*12500^4113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1369 12500 13868446986887389 100000000000000000000 4113 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1369/12500 : ℝ)) (X := (13868446986887389/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14249/100000 : ℝ) ^ (4113/1024 : ℝ) ≤ (19955336191049269/50000000000000000000 : ℝ) := by
    have hpowers : (14249/100000 : ℝ)^4113 ≤ (19955336191049269/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14249 : ℕ)^4113*50000000000000000000^1024 ≤ 19955336191049269^1024*100000^4113 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14249 100000 19955336191049269 50000000000000000000 4113 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14249/100000 : ℝ)) (X := (19955336191049269/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013868446986887389/50000000000000000000 : ℝ) ≤ (10000690484356681/10000000000000000 : ℝ) ^ (4113/1024 : ℝ) := by
    have hpowers : (50013868446986887389/50000000000000000000 : ℝ)^1024 ≤ (10000690484356681/10000000000000000 : ℝ)^4113 := by
      have hnat : (50013868446986887389 : ℕ)^1024*10000000000000000^4113 ≤ 10000690484356681^4113*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013868446986887389 50000000000000000000 10000690484356681 10000000000000000 1024 4113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000690484356681/10000000000000000 : ℝ)) (X := (50013868446986887389/50000000000000000000 : ℝ)) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053779119368985927/100000000000000000000 : ℝ) ≤ (400053546025187/400000000000000 : ℝ) ^ (4113/1024 : ℝ) := by
    have hpowers : (100053779119368985927/100000000000000000000 : ℝ)^1024 ≤ (400053546025187/400000000000000 : ℝ)^4113 := by
      have hnat : (100053779119368985927 : ℕ)^1024*400000000000000^4113 ≤ 400053546025187^4113*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053779119368985927 100000000000000000000 400053546025187 400000000000000 1024 4113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400053546025187/400000000000000 : ℝ)) (X := (100053779119368985927/100000000000000000000 : ℝ)) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25019955336191049269/25000000000000000000 : ℝ) ≤ (10001986816902669/10000000000000000 : ℝ) ^ (4113/1024 : ℝ) := by
    have hpowers : (25019955336191049269/25000000000000000000 : ℝ)^1024 ≤ (10001986816902669/10000000000000000 : ℝ)^4113 := by
      have hnat : (25019955336191049269 : ℕ)^1024*10000000000000000^4113 ≤ 10001986816902669^4113*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25019955336191049269 25000000000000000000 10001986816902669 10000000000000000 1024 4113 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001986816902669/10000000000000000 : ℝ)) (X := (25019955336191049269/25000000000000000000 : ℝ)) (by norm_num) 4113 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13868446986887389/100000000000000000000 : ℝ) ≤ ((32958079092880316681/32970000000000000000 : ℝ)+2*(324083136497/164850000000000 : ℝ)*(1369/12500 : ℝ))^(4113/1024 : ℝ) := by
    rw [show (32958079092880316681/32970000000000000000 : ℝ)+2*(324083136497/164850000000000 : ℝ)*(1369/12500 : ℝ)=(10000690484356681/10000000000000000 : ℝ) by norm_num, show 1+2*(13868446986887389/100000000000000000000 : ℝ)=(50013868446986887389/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19955336191049269/50000000000000000000 : ℝ)+(13868446986887389/100000000000000000000 : ℝ) ≤ ((32958079092880316681/32970000000000000000 : ℝ)+(324083136497/164850000000000 : ℝ)*((14249/100000 : ℝ)+(1369/12500 : ℝ)))^(4113/1024 : ℝ) := by
    rw [show (32958079092880316681/32970000000000000000 : ℝ)+(324083136497/164850000000000 : ℝ)*((14249/100000 : ℝ)+(1369/12500 : ℝ))=(400053546025187/400000000000000 : ℝ) by norm_num, show 1+(19955336191049269/50000000000000000000 : ℝ)+(13868446986887389/100000000000000000000 : ℝ)=(100053779119368985927/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19955336191049269/50000000000000000000 : ℝ) ≤ ((32958079092880316681/32970000000000000000 : ℝ)+2*(324083136497/164850000000000 : ℝ)*(14249/100000 : ℝ))^(4113/1024 : ℝ) := by
    rw [show (32958079092880316681/32970000000000000000 : ℝ)+2*(324083136497/164850000000000 : ℝ)*(14249/100000 : ℝ)=(10001986816902669/10000000000000000 : ℝ) by norm_num, show 1+2*(19955336191049269/50000000000000000000 : ℝ)=(25019955336191049269/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32958079092880316681/32970000000000000000 : ℝ)*(X 1 0+X 2 0)+(324083136497/164850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4113/1024 : ℝ)) (lo := (1369/12500 : ℝ)) (hi := (14249/100000 : ℝ)) (c := (32958079092880316681/32970000000000000000 : ℝ)) (alpha := (324083136497/164850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32958079092880316681/32970000000000000000 : ℝ)*(X 0 1+X 2 1)+(324083136497/164850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4113/1024 : ℝ)) (lo := (1369/12500 : ℝ)) (hi := (14249/100000 : ℝ)) (c := (32958079092880316681/32970000000000000000 : ℝ)) (alpha := (324083136497/164850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32958079092880316681/32970000000000000000 : ℝ)*(X 0 2+X 1 2)+(324083136497/164850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4113/1024 : ℝ)) (lo := (1369/12500 : ℝ)) (hi := (14249/100000 : ℝ)) (c := (32958079092880316681/32970000000000000000 : ℝ)) (alpha := (324083136497/164850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2219357039/10000000000 : ℝ)*X 0 0+(1079586827/2000000000 : ℝ)*X 0 1+(2630500363/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345794439/10000000000 : ℝ)*X 1 0+(-2288887571/10000000000 : ℝ)*X 1 1+(2630500371/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069158887/2000000000 : ℝ)*X 2 0+(5261000663/10000000000 : ℝ)*X 2 1+(-3576387/15625000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4379961207/10000000000 : ℝ)*X 0 0+(2124349573/5000000000 : ℝ)*X 0 1+(112884153/250000000 : ℝ)*X 0 2+(4379961207/10000000000 : ℝ)*X 1 0+(2124349573/5000000000 : ℝ)*X 1 1+(112884153/250000000 : ℝ)*X 1 2+(4379961207/10000000000 : ℝ)*X 2 0+(2124349573/5000000000 : ℝ)*X 2 1+(112884153/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1109681443/5000000000 : ℝ)*X 0 0+(1315339621/2500000000 : ℝ)*X 0 1+(674696881/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655696481/5000000000 : ℝ)*X 1 0+(-269039183/1250000000 : ℝ)*X 1 1+(5397575019/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311393099/10000000000 : ℝ)*X 2 0+(1079514997/2000000000 : ℝ)*X 2 1+(-86092533/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4379972267/10000000000 : ℝ)*X 0 0+(1128667347/2500000000 : ℝ)*X 0 1+(4249398869/10000000000 : ℝ)*X 0 2+(4379972267/10000000000 : ℝ)*X 1 0+(1128667347/2500000000 : ℝ)*X 1 1+(4249398869/10000000000 : ℝ)*X 1 2+(4379972267/10000000000 : ℝ)*X 2 0+(1128667347/2500000000 : ℝ)*X 2 1+(4249398869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1034_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (396384326666504196078016653/68687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (852773107/100000000000000 : ℝ)*(base19) + (775607839/100000000000000 : ℝ)*(base23) + (37809109/50000000000000 : ℝ)*(lower2) + (218454249/100000000000000 : ℝ)*(upper3) + (18644197/50000000000000 : ℝ)*(lower4) + (1381609698269187/25000000000000 : ℝ)*(major0) + (1381609698269187/25000000000000 : ℝ)*(major1) + (1381609698269187/25000000000000 : ℝ)*(major2) + (7302843167770421/100000000000000 : ℝ)*(sp0) + (1460571353139163/20000000000000 : ℝ)*(sp1) + (3651428421430541/50000000000000 : ℝ)*(sp2) + (1875002708402637/50000000000000 : ℝ)*(sp3) + (14450698501/100000000000000 : ℝ)*(sp4) + (7179259039/50000000000000 : ℝ)*(sp7) + (468752471915419/12500000000000 : ℝ)*(f.failure) + (7302857618468921/100000000000000 : ℝ)*(f.sum) + (24741679956199/5495000000000000000000000000 : ℝ)*base65 + (444436261784180551/274750000000000000000000000000000 : ℝ)*base68 + (2515320815183069449/274750000000000000000000000000000 : ℝ)*base69 + (1510334228101319449/274750000000000000000000000000000 : ℝ)*base71 + (1720346332519/5495000000000000000000000000 : ℝ)*base73 + (1688222746792069449/274750000000000000000000000000000 : ℝ)*base75 + (4850990386197569449/274750000000000000000000000000000 : ℝ)*base77 + (3979795936302569449/274750000000000000000000000000000 : ℝ)*base79 + (4969538270993/2747500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (530711/312500000000000000000 : ℝ)*base90 + (530711/312500000000000000000 : ℝ)*base92 + (530711/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42269441994672887214767/5495000000000000000000000000 : ℝ) := by norm_num
    linear_combination (102146557/20000000000000 : ℝ)*(base19) + (757504313/100000000000000 : ℝ)*(base23) + (23218931/50000000000000 : ℝ)*(upper3) + (4380559/100000000000000 : ℝ)*(lower4) + (44175079/50000000000000 : ℝ)*(upper5) + (5555496278167763/100000000000000 : ℝ)*(major0) + (5555496278167763/100000000000000 : ℝ)*(major1) + (5555496278167763/100000000000000 : ℝ)*(major2) + (3063048101/25000000000000 : ℝ)*(sp1) + (9921658299/50000000000000 : ℝ)*(sp2) + (7341255280315033/100000000000000 : ℝ)*(sp4) + (1835310629347461/25000000000000 : ℝ)*(sp5) + (7341234679494123/100000000000000 : ℝ)*(sp6) + (235608563725559/6250000000000 : ℝ)*(sp7) + (235608563725559/6250000000000 : ℝ)*(f.failure) + (7341255280315033/100000000000000 : ℝ)*(f.sum) + (8549513427607/4121250000000000000000000000 : ℝ)*base66 + (10037349731113481799/1099000000000000000000000000000000 : ℝ)*base68 + (373164409962518201/1099000000000000000000000000000000 : ℝ)*base69 + (5736939748825481799/1099000000000000000000000000000000 : ℝ)*base72 + (13278176102999/8242500000000000000000000000 : ℝ)*base74 + (15836782142182518201/1099000000000000000000000000000000 : ℝ)*base75 + (470574895897518201/1099000000000000000000000000000000 : ℝ)*base77 + (12113281226156481799/1099000000000000000000000000000000 : ℝ)*base80 + (106171854636737/16485000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1625871/156250000000000000000 : ℝ)*base90 + (1625871/156250000000000000000 : ℝ)*base92 + (1625871/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1034_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36842731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14249/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1369/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1034_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1034_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36842731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3369/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1711/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1034_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1034_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1034_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4113/1024 : ℝ) ≤ p) (hpb : p ≤ (8227/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36842731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3369/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1711/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5573/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7023/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1034_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

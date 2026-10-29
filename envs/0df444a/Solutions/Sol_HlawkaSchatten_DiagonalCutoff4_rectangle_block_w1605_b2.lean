-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1605_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:49:17.513998+00:00
-- url     : https://prove2.me/submissions/fecf19a1-e010-41ef-a0b7-c37be3075be8

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
theorem support_rectangle_w1605_box_0 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1441618959/10000000000 : ℝ)*x 0 + (2709688973/5000000000 : ℝ)*x 1 + (5419377699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1441618959/10000000000 : ℝ)^4739 ≤ (8452722696803/100000000000000 : ℝ)^3715 := by
    have hnat : (1441618959 : ℕ)^4739*100000000000000^3715 ≤ 8452722696803^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1441618959 10000000000 8452722696803 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709688973/5000000000 : ℝ)^4739 ≤ (22886819986257/50000000000000 : ℝ)^3715 := by
    have hnat : (2709688973 : ℕ)^4739*50000000000000^3715 ≤ 22886819986257^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709688973 5000000000 22886819986257 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419377699/10000000000 : ℝ)^4739 ≤ (45773637311233/100000000000000 : ℝ)^3715 := by
    have hnat : (5419377699 : ℕ)^4739*100000000000000^3715 ≤ 45773637311233^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419377699 10000000000 45773637311233 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1441618959/10000000000 : ℝ), (2709688973/5000000000 : ℝ), (5419377699/10000000000 : ℝ)] ![(8452722696803/100000000000000 : ℝ), (22886819986257/50000000000000 : ℝ), (45773637311233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1441618959/10000000000 : ℝ)|^4739 ≤ (8452722696803/100000000000000 : ℝ)^3715
        have hw : |(-1441618959/10000000000 : ℝ)|=(1441618959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709688973/5000000000 : ℝ)|^4739 ≤ (22886819986257/50000000000000 : ℝ)^3715
        have hw : |(2709688973/5000000000 : ℝ)|=(2709688973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419377699/10000000000 : ℝ)|^4739 ≤ (45773637311233/100000000000000 : ℝ)^3715
        have hw : |(5419377699/10000000000 : ℝ)|=(5419377699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_box_1 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050218409/2000000000 : ℝ)*x 0 + (-167785483/1000000000 : ℝ)*x 1 + (5419378029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050218409/2000000000 : ℝ)^4739 ≤ (21984137890201/50000000000000 : ℝ)^3715 := by
    have hnat : (1050218409 : ℕ)^4739*50000000000000^3715 ≤ 21984137890201^3715*2000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050218409 2000000000 21984137890201 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (167785483/1000000000 : ℝ)^4739 ≤ (641130208591/6250000000000 : ℝ)^3715 := by
    have hnat : (167785483 : ℕ)^4739*6250000000000^3715 ≤ 641130208591^3715*1000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167785483 1000000000 641130208591 6250000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419378029/10000000000 : ℝ)^4739 ≤ (45773640866791/100000000000000 : ℝ)^3715 := by
    have hnat : (5419378029 : ℕ)^4739*100000000000000^3715 ≤ 45773640866791^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419378029 10000000000 45773640866791 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050218409/2000000000 : ℝ), (-167785483/1000000000 : ℝ), (5419378029/10000000000 : ℝ)] ![(21984137890201/50000000000000 : ℝ), (641130208591/6250000000000 : ℝ), (45773640866791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050218409/2000000000 : ℝ)|^4739 ≤ (21984137890201/50000000000000 : ℝ)^3715
        have hw : |(1050218409/2000000000 : ℝ)|=(1050218409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-167785483/1000000000 : ℝ)|^4739 ≤ (641130208591/6250000000000 : ℝ)^3715
        have hw : |(-167785483/1000000000 : ℝ)|=(167785483/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419378029/10000000000 : ℝ)|^4739 ≤ (45773640866791/100000000000000 : ℝ)^3715
        have hw : |(5419378029/10000000000 : ℝ)|=(5419378029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_box_2 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1312773131/2500000000 : ℝ)*x 0 + (2709688763/5000000000 : ℝ)*x 1 + (-1677854869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312773131/2500000000 : ℝ)^4739 ≤ (43968280896669/100000000000000 : ℝ)^3715 := by
    have hnat : (1312773131 : ℕ)^4739*100000000000000^3715 ≤ 43968280896669^3715*2500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312773131 2500000000 43968280896669 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709688763/5000000000 : ℝ)^4739 ≤ (22886817723629/50000000000000 : ℝ)^3715 := by
    have hnat : (2709688763 : ℕ)^4739*50000000000000^3715 ≤ 22886817723629^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709688763 5000000000 22886817723629 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1677854869/10000000000 : ℝ)^4739 ≤ (10258083641617/100000000000000 : ℝ)^3715 := by
    have hnat : (1677854869 : ℕ)^4739*100000000000000^3715 ≤ 10258083641617^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1677854869 10000000000 10258083641617 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312773131/2500000000 : ℝ), (2709688763/5000000000 : ℝ), (-1677854869/10000000000 : ℝ)] ![(43968280896669/100000000000000 : ℝ), (22886817723629/50000000000000 : ℝ), (10258083641617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312773131/2500000000 : ℝ)|^4739 ≤ (43968280896669/100000000000000 : ℝ)^3715
        have hw : |(1312773131/2500000000 : ℝ)|=(1312773131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709688763/5000000000 : ℝ)|^4739 ≤ (22886817723629/50000000000000 : ℝ)^3715
        have hw : |(2709688763/5000000000 : ℝ)|=(2709688763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1677854869/10000000000 : ℝ)|^4739 ≤ (10258083641617/100000000000000 : ℝ)^3715
        have hw : |(-1677854869/10000000000 : ℝ)|=(1677854869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_box_3 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (35132743/78125000 : ℝ)*x 0 + (4089372641/10000000000 : ℝ)*x 1 + (40893727/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35132743/78125000 : ℝ)^4739 ≤ (18039467083809/50000000000000 : ℝ)^3715 := by
    have hnat : (35132743 : ℕ)^4739*50000000000000^3715 ≤ 18039467083809^3715*78125000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35132743 78125000 18039467083809 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4089372641/10000000000 : ℝ)^4739 ≤ (15980266308177/50000000000000 : ℝ)^3715 := by
    have hnat : (4089372641 : ℕ)^4739*50000000000000^3715 ≤ 15980266308177^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4089372641 10000000000 15980266308177 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40893727/100000000 : ℝ)^4739 ≤ (31960533204571/100000000000000 : ℝ)^3715 := by
    have hnat : (40893727 : ℕ)^4739*100000000000000^3715 ≤ 31960533204571^3715*100000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40893727 100000000 31960533204571 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(35132743/78125000 : ℝ), (4089372641/10000000000 : ℝ), (40893727/100000000 : ℝ)] ![(18039467083809/50000000000000 : ℝ), (15980266308177/50000000000000 : ℝ), (31960533204571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(35132743/78125000 : ℝ)|^4739 ≤ (18039467083809/50000000000000 : ℝ)^3715
        have hw : |(35132743/78125000 : ℝ)|=(35132743/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4089372641/10000000000 : ℝ)|^4739 ≤ (15980266308177/50000000000000 : ℝ)^3715
        have hw : |(4089372641/10000000000 : ℝ)|=(4089372641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40893727/100000000 : ℝ)|^4739 ≤ (31960533204571/100000000000000 : ℝ)^3715
        have hw : |(40893727/100000000 : ℝ)|=(40893727/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_box_4 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1001529961/5000000000 : ℝ)*x 0 + (2606902867/5000000000 : ℝ)*x 1 + (5213806317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1001529961/5000000000 : ℝ)^4739 ≤ (1285918215387/10000000000000 : ℝ)^3715 := by
    have hnat : (1001529961 : ℕ)^4739*10000000000000^3715 ≤ 1285918215387^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001529961 5000000000 1285918215387 10000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606902867/5000000000 : ℝ)^4739 ≤ (10892601451397/25000000000000 : ℝ)^3715 := by
    have hnat : (2606902867 : ℕ)^4739*25000000000000^3715 ≤ 10892601451397^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606902867 5000000000 10892601451397 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5213806317/10000000000 : ℝ)^4739 ≤ (1742816480819/4000000000000 : ℝ)^3715 := by
    have hnat : (5213806317 : ℕ)^4739*4000000000000^3715 ≤ 1742816480819^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213806317 10000000000 1742816480819 4000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1001529961/5000000000 : ℝ), (2606902867/5000000000 : ℝ), (5213806317/10000000000 : ℝ)] ![(1285918215387/10000000000000 : ℝ), (10892601451397/25000000000000 : ℝ), (1742816480819/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1001529961/5000000000 : ℝ)|^4739 ≤ (1285918215387/10000000000000 : ℝ)^3715
        have hw : |(-1001529961/5000000000 : ℝ)|=(1001529961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606902867/5000000000 : ℝ)|^4739 ≤ (10892601451397/25000000000000 : ℝ)^3715
        have hw : |(2606902867/5000000000 : ℝ)|=(2606902867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5213806317/10000000000 : ℝ)|^4739 ≤ (1742816480819/4000000000000 : ℝ)^3715
        have hw : |(5213806317/10000000000 : ℝ)|=(5213806317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_box_5 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348268317/2500000000 : ℝ)*x 0 + (-882287523/5000000000 : ℝ)*x 1 + (104276129/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348268317/2500000000 : ℝ)^4739 ≤ (11372603034867/25000000000000 : ℝ)^3715 := by
    have hnat : (1348268317 : ℕ)^4739*25000000000000^3715 ≤ 11372603034867^3715*2500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348268317 2500000000 11372603034867 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (882287523/5000000000 : ℝ)^4739 ≤ (10939174416889/100000000000000 : ℝ)^3715 := by
    have hnat : (882287523 : ℕ)^4739*100000000000000^3715 ≤ 10939174416889^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882287523 5000000000 10939174416889 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104276129/200000000 : ℝ)^4739 ≤ (43570413438279/100000000000000 : ℝ)^3715 := by
    have hnat : (104276129 : ℕ)^4739*100000000000000^3715 ≤ 43570413438279^3715*200000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104276129 200000000 43570413438279 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348268317/2500000000 : ℝ), (-882287523/5000000000 : ℝ), (104276129/200000000 : ℝ)] ![(11372603034867/25000000000000 : ℝ), (10939174416889/100000000000000 : ℝ), (43570413438279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348268317/2500000000 : ℝ)|^4739 ≤ (11372603034867/25000000000000 : ℝ)^3715
        have hw : |(1348268317/2500000000 : ℝ)|=(1348268317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-882287523/5000000000 : ℝ)|^4739 ≤ (10939174416889/100000000000000 : ℝ)^3715
        have hw : |(-882287523/5000000000 : ℝ)|=(882287523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104276129/200000000 : ℝ)|^4739 ≤ (43570413438279/100000000000000 : ℝ)^3715
        have hw : |(104276129/200000000 : ℝ)|=(104276129/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_box_6 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5393073583/10000000000 : ℝ)*x 0 + (1042761133/2000000000 : ℝ)*x 1 + (-70583027/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5393073583/10000000000 : ℝ)^4739 ≤ (45490415528861/100000000000000 : ℝ)^3715 := by
    have hnat : (5393073583 : ℕ)^4739*100000000000000^3715 ≤ 45490415528861^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393073583 10000000000 45490415528861 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042761133/2000000000 : ℝ)^4739 ≤ (10892601267509/25000000000000 : ℝ)^3715 := by
    have hnat : (1042761133 : ℕ)^4739*25000000000000^3715 ≤ 10892601267509^3715*2000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042761133 2000000000 10892601267509 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70583027/400000000 : ℝ)^4739 ≤ (5469589695543/50000000000000 : ℝ)^3715 := by
    have hnat : (70583027 : ℕ)^4739*50000000000000^3715 ≤ 5469589695543^3715*400000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70583027 400000000 5469589695543 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5393073583/10000000000 : ℝ), (1042761133/2000000000 : ℝ), (-70583027/400000000 : ℝ)] ![(45490415528861/100000000000000 : ℝ), (10892601267509/25000000000000 : ℝ), (5469589695543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5393073583/10000000000 : ℝ)|^4739 ≤ (45490415528861/100000000000000 : ℝ)^3715
        have hw : |(5393073583/10000000000 : ℝ)|=(5393073583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042761133/2000000000 : ℝ)|^4739 ≤ (10892601267509/25000000000000 : ℝ)^3715
        have hw : |(1042761133/2000000000 : ℝ)|=(1042761133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-70583027/400000000 : ℝ)|^4739 ≤ (5469589695543/50000000000000 : ℝ)^3715
        have hw : |(-70583027/400000000 : ℝ)|=(70583027/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_box_7 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1965302723/5000000000 : ℝ)*x 0 + (4372219543/10000000000 : ℝ)*x 1 + (4372219233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1965302723/5000000000 : ℝ)^4739 ≤ (15193105128027/50000000000000 : ℝ)^3715 := by
    have hnat : (1965302723 : ℕ)^4739*50000000000000^3715 ≤ 15193105128027^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965302723 5000000000 15193105128027 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4372219543/10000000000 : ℝ)^4739 ≤ (3480689644387/10000000000000 : ℝ)^3715 := by
    have hnat : (4372219543 : ℕ)^4739*10000000000000^3715 ≤ 3480689644387^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372219543 10000000000 3480689644387 10000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4372219233/10000000000 : ℝ)^4739 ≤ (17403446647869/50000000000000 : ℝ)^3715 := by
    have hnat : (4372219233 : ℕ)^4739*50000000000000^3715 ≤ 17403446647869^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372219233 10000000000 17403446647869 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1965302723/5000000000 : ℝ), (4372219543/10000000000 : ℝ), (4372219233/10000000000 : ℝ)] ![(15193105128027/50000000000000 : ℝ), (3480689644387/10000000000000 : ℝ), (17403446647869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1965302723/5000000000 : ℝ)|^4739 ≤ (15193105128027/50000000000000 : ℝ)^3715
        have hw : |(1965302723/5000000000 : ℝ)|=(1965302723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4372219543/10000000000 : ℝ)|^4739 ≤ (3480689644387/10000000000000 : ℝ)^3715
        have hw : |(4372219543/10000000000 : ℝ)|=(4372219543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4372219233/10000000000 : ℝ)|^4739 ≤ (17403446647869/50000000000000 : ℝ)^3715
        have hw : |(4372219233/10000000000 : ℝ)|=(4372219233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_box_8 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-235468719/1250000000 : ℝ)*x 0 + (1266774407/2500000000 : ℝ)*x 1 + (5449382617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235468719/1250000000 : ℝ)^4739 ≤ (2378050693201/20000000000000 : ℝ)^3715 := by
    have hnat : (235468719 : ℕ)^4739*20000000000000^3715 ≤ 2378050693201^3715*1250000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235468719 1250000000 2378050693201 20000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1266774407/2500000000 : ℝ)^4739 ≤ (5251572159383/12500000000000 : ℝ)^3715 := by
    have hnat : (1266774407 : ℕ)^4739*12500000000000^3715 ≤ 5251572159383^3715*2500000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1266774407 2500000000 5251572159383 12500000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5449382617/10000000000 : ℝ)^4739 ≤ (23048584625061/50000000000000 : ℝ)^3715 := by
    have hnat : (5449382617 : ℕ)^4739*50000000000000^3715 ≤ 23048584625061^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449382617 10000000000 23048584625061 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-235468719/1250000000 : ℝ), (1266774407/2500000000 : ℝ), (5449382617/10000000000 : ℝ)] ![(2378050693201/20000000000000 : ℝ), (5251572159383/12500000000000 : ℝ), (23048584625061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-235468719/1250000000 : ℝ)|^4739 ≤ (2378050693201/20000000000000 : ℝ)^3715
        have hw : |(-235468719/1250000000 : ℝ)|=(235468719/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1266774407/2500000000 : ℝ)|^4739 ≤ (5251572159383/12500000000000 : ℝ)^3715
        have hw : |(1266774407/2500000000 : ℝ)|=(1266774407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5449382617/10000000000 : ℝ)|^4739 ≤ (23048584625061/50000000000000 : ℝ)^3715
        have hw : |(5449382617/10000000000 : ℝ)|=(5449382617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_box_9 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230363211/10000000000 : ℝ)*x 0 + (-832365479/5000000000 : ℝ)*x 1 + (2724691373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230363211/10000000000 : ℝ)^4739 ≤ (43746988729117/100000000000000 : ℝ)^3715 := by
    have hnat : (5230363211 : ℕ)^4739*100000000000000^3715 ≤ 43746988729117^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230363211 10000000000 43746988729117 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (832365479/5000000000 : ℝ)^4739 ≤ (2538960153637/25000000000000 : ℝ)^3715 := by
    have hnat : (832365479 : ℕ)^4739*25000000000000^3715 ≤ 2538960153637^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832365479 5000000000 2538960153637 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2724691373/5000000000 : ℝ)^4739 ≤ (2304858532107/5000000000000 : ℝ)^3715 := by
    have hnat : (2724691373 : ℕ)^4739*5000000000000^3715 ≤ 2304858532107^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724691373 5000000000 2304858532107 5000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230363211/10000000000 : ℝ), (-832365479/5000000000 : ℝ), (2724691373/5000000000 : ℝ)] ![(43746988729117/100000000000000 : ℝ), (2538960153637/25000000000000 : ℝ), (2304858532107/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230363211/10000000000 : ℝ)|^4739 ≤ (43746988729117/100000000000000 : ℝ)^3715
        have hw : |(5230363211/10000000000 : ℝ)|=(5230363211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-832365479/5000000000 : ℝ)|^4739 ≤ (2538960153637/25000000000000 : ℝ)^3715
        have hw : |(-832365479/5000000000 : ℝ)|=(832365479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2724691373/5000000000 : ℝ)|^4739 ≤ (2304858532107/5000000000000 : ℝ)^3715
        have hw : |(2724691373/5000000000 : ℝ)|=(2724691373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_box_10 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (523036379/1000000000 : ℝ)*x 0 + (5449383131/10000000000 : ℝ)*x 1 + (-166472963/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523036379/1000000000 : ℝ)^4739 ≤ (1093674872669/2500000000000 : ℝ)^3715 := by
    have hnat : (523036379 : ℕ)^4739*2500000000000^3715 ≤ 1093674872669^3715*1000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523036379 1000000000 1093674872669 2500000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5449383131/10000000000 : ℝ)^4739 ≤ (46097174796609/100000000000000 : ℝ)^3715 := by
    have hnat : (5449383131 : ℕ)^4739*100000000000000^3715 ≤ 46097174796609^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449383131 10000000000 46097174796609 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166472963/1000000000 : ℝ)^4739 ≤ (10155830279851/100000000000000 : ℝ)^3715 := by
    have hnat : (166472963 : ℕ)^4739*100000000000000^3715 ≤ 10155830279851^3715*1000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166472963 1000000000 10155830279851 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523036379/1000000000 : ℝ), (5449383131/10000000000 : ℝ), (-166472963/1000000000 : ℝ)] ![(1093674872669/2500000000000 : ℝ), (46097174796609/100000000000000 : ℝ), (10155830279851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523036379/1000000000 : ℝ)|^4739 ≤ (1093674872669/2500000000000 : ℝ)^3715
        have hw : |(523036379/1000000000 : ℝ)|=(523036379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5449383131/10000000000 : ℝ)|^4739 ≤ (46097174796609/100000000000000 : ℝ)^3715
        have hw : |(5449383131/10000000000 : ℝ)|=(5449383131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-166472963/1000000000 : ℝ)|^4739 ≤ (10155830279851/100000000000000 : ℝ)^3715
        have hw : |(-166472963/1000000000 : ℝ)|=(166472963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_box_11 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (915452113/2000000000 : ℝ)*x 0 + (2024007341/5000000000 : ℝ)*x 1 + (101200343/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (915452113/2000000000 : ℝ)^4739 ≤ (1153201589761/3125000000000 : ℝ)^3715 := by
    have hnat : (915452113 : ℕ)^4739*3125000000000^3715 ≤ 1153201589761^3715*2000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915452113 2000000000 1153201589761 3125000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2024007341/5000000000 : ℝ)^4739 ≤ (31548779340497/100000000000000 : ℝ)^3715 := by
    have hnat : (2024007341 : ℕ)^4739*100000000000000^3715 ≤ 31548779340497^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024007341 5000000000 31548779340497 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101200343/250000000 : ℝ)^4739 ≤ (7887192444103/25000000000000 : ℝ)^3715 := by
    have hnat : (101200343 : ℕ)^4739*25000000000000^3715 ≤ 7887192444103^3715*250000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101200343 250000000 7887192444103 25000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(915452113/2000000000 : ℝ), (2024007341/5000000000 : ℝ), (101200343/250000000 : ℝ)] ![(1153201589761/3125000000000 : ℝ), (31548779340497/100000000000000 : ℝ), (7887192444103/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(915452113/2000000000 : ℝ)|^4739 ≤ (1153201589761/3125000000000 : ℝ)^3715
        have hw : |(915452113/2000000000 : ℝ)|=(915452113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2024007341/5000000000 : ℝ)|^4739 ≤ (31548779340497/100000000000000 : ℝ)^3715
        have hw : |(2024007341/5000000000 : ℝ)|=(2024007341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(101200343/250000000 : ℝ)|^4739 ≤ (7887192444103/25000000000000 : ℝ)^3715
        have hw : |(101200343/250000000 : ℝ)|=(101200343/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_box_12 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-779892269/5000000000 : ℝ)*x 0 + (1112015181/2000000000 : ℝ)*x 1 + (5193935057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (779892269/5000000000 : ℝ)^4739 ≤ (934633847881/10000000000000 : ℝ)^3715 := by
    have hnat : (779892269 : ℕ)^4739*10000000000000^3715 ≤ 934633847881^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779892269 5000000000 934633847881 10000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1112015181/2000000000 : ℝ)^4739 ≤ (47294969391311/100000000000000 : ℝ)^3715 := by
    have hnat : (1112015181 : ℕ)^4739*100000000000000^3715 ≤ 47294969391311^3715*2000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112015181 2000000000 47294969391311 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5193935057/10000000000 : ℝ)^4739 ≤ (21679346060863/50000000000000 : ℝ)^3715 := by
    have hnat : (5193935057 : ℕ)^4739*50000000000000^3715 ≤ 21679346060863^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193935057 10000000000 21679346060863 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-779892269/5000000000 : ℝ), (1112015181/2000000000 : ℝ), (5193935057/10000000000 : ℝ)] ![(934633847881/10000000000000 : ℝ), (47294969391311/100000000000000 : ℝ), (21679346060863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-779892269/5000000000 : ℝ)|^4739 ≤ (934633847881/10000000000000 : ℝ)^3715
        have hw : |(-779892269/5000000000 : ℝ)|=(779892269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1112015181/2000000000 : ℝ)|^4739 ≤ (47294969391311/100000000000000 : ℝ)^3715
        have hw : |(1112015181/2000000000 : ℝ)|=(1112015181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5193935057/10000000000 : ℝ)|^4739 ≤ (21679346060863/50000000000000 : ℝ)^3715
        have hw : |(5193935057/10000000000 : ℝ)|=(5193935057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_box_13 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5406804127/10000000000 : ℝ)*x 0 + (-1772653653/10000000000 : ℝ)*x 1 + (1038786993/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5406804127/10000000000 : ℝ)^4739 ≤ (9127641542043/20000000000000 : ℝ)^3715 := by
    have hnat : (5406804127 : ℕ)^4739*20000000000000^3715 ≤ 9127641542043^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406804127 10000000000 9127641542043 20000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1772653653/10000000000 : ℝ)^4739 ≤ (11003101137079/100000000000000 : ℝ)^3715 := by
    have hnat : (1772653653 : ℕ)^4739*100000000000000^3715 ≤ 11003101137079^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1772653653 10000000000 11003101137079 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038786993/2000000000 : ℝ)^4739 ≤ (43358691142021/100000000000000 : ℝ)^3715 := by
    have hnat : (1038786993 : ℕ)^4739*100000000000000^3715 ≤ 43358691142021^3715*2000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038786993 2000000000 43358691142021 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5406804127/10000000000 : ℝ), (-1772653653/10000000000 : ℝ), (1038786993/2000000000 : ℝ)] ![(9127641542043/20000000000000 : ℝ), (11003101137079/100000000000000 : ℝ), (43358691142021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5406804127/10000000000 : ℝ)|^4739 ≤ (9127641542043/20000000000000 : ℝ)^3715
        have hw : |(5406804127/10000000000 : ℝ)|=(5406804127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1772653653/10000000000 : ℝ)|^4739 ≤ (11003101137079/100000000000000 : ℝ)^3715
        have hw : |(-1772653653/10000000000 : ℝ)|=(1772653653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1038786993/2000000000 : ℝ)|^4739 ≤ (43358691142021/100000000000000 : ℝ)^3715
        have hw : |(1038786993/2000000000 : ℝ)|=(1038786993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_box_14 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540680411/1000000000 : ℝ)*x 0 + (2596967489/5000000000 : ℝ)*x 1 + (-886326829/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540680411/1000000000 : ℝ)^4739 ≤ (45638207527167/100000000000000 : ℝ)^3715 := by
    have hnat : (540680411 : ℕ)^4739*100000000000000^3715 ≤ 45638207527167^3715*1000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540680411 1000000000 45638207527167 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2596967489/5000000000 : ℝ)^4739 ≤ (43358691280457/100000000000000 : ℝ)^3715 := by
    have hnat : (2596967489 : ℕ)^4739*100000000000000^3715 ≤ 43358691280457^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596967489 5000000000 43358691280457 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (886326829/5000000000 : ℝ)^4739 ≤ (1100310117667/10000000000000 : ℝ)^3715 := by
    have hnat : (886326829 : ℕ)^4739*10000000000000^3715 ≤ 1100310117667^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886326829 5000000000 1100310117667 10000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540680411/1000000000 : ℝ), (2596967489/5000000000 : ℝ), (-886326829/5000000000 : ℝ)] ![(45638207527167/100000000000000 : ℝ), (43358691280457/100000000000000 : ℝ), (1100310117667/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540680411/1000000000 : ℝ)|^4739 ≤ (45638207527167/100000000000000 : ℝ)^3715
        have hw : |(540680411/1000000000 : ℝ)|=(540680411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2596967489/5000000000 : ℝ)|^4739 ≤ (43358691280457/100000000000000 : ℝ)^3715
        have hw : |(2596967489/5000000000 : ℝ)|=(2596967489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-886326829/5000000000 : ℝ)|^4739 ≤ (1100310117667/10000000000000 : ℝ)^3715
        have hw : |(-886326829/5000000000 : ℝ)|=(886326829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1605_box_15 (p : ℝ) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1937117427/5000000000 : ℝ)*x 0 + (2199755781/5000000000 : ℝ)*x 1 + (4399511947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1937117427/5000000000 : ℝ)^4739 ≤ (1864463230677/6250000000000 : ℝ)^3715 := by
    have hnat : (1937117427 : ℕ)^4739*6250000000000^3715 ≤ 1864463230677^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937117427 5000000000 1864463230677 6250000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2199755781/5000000000 : ℝ)^4739 ≤ (35084292187537/100000000000000 : ℝ)^3715 := by
    have hnat : (2199755781 : ℕ)^4739*100000000000000^3715 ≤ 35084292187537^3715*5000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199755781 5000000000 35084292187537 100000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4399511947/10000000000 : ℝ)^4739 ≤ (17542148052013/50000000000000 : ℝ)^3715 := by
    have hnat : (4399511947 : ℕ)^4739*50000000000000^3715 ≤ 17542148052013^3715*10000000000^4739 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4399511947 10000000000 17542148052013 50000000000000 4739 3715 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4739/1024 : ℝ)) 4739 3715 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1937117427/5000000000 : ℝ), (2199755781/5000000000 : ℝ), (4399511947/10000000000 : ℝ)] ![(1864463230677/6250000000000 : ℝ), (35084292187537/100000000000000 : ℝ), (17542148052013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1937117427/5000000000 : ℝ)|^4739 ≤ (1864463230677/6250000000000 : ℝ)^3715
        have hw : |(1937117427/5000000000 : ℝ)|=(1937117427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2199755781/5000000000 : ℝ)|^4739 ≤ (35084292187537/100000000000000 : ℝ)^3715
        have hw : |(2199755781/5000000000 : ℝ)|=(2199755781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4399511947/10000000000 : ℝ)|^4739 ≤ (17542148052013/50000000000000 : ℝ)^3715
        have hw : |(4399511947/10000000000 : ℝ)|=(4399511947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1605_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16349/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5201/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(64903/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(2907/5000 : ℝ) ∧ (80333/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (87773/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16349/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5201/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16349/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5201/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16349/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5201/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16349/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5201/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16349/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5201/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16349/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5201/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5201/50000 : ℝ) ^ (4735/1024 : ℝ) ≤ (1425920391801987/50000000000000000000 : ℝ) := by
    have hpowers : (5201/50000 : ℝ)^4735 ≤ (1425920391801987/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5201 : ℕ)^4735*50000000000000000000^1024 ≤ 1425920391801987^1024*50000^4735 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5201 50000 1425920391801987 50000000000000000000 4735 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5201/50000 : ℝ)) (X := (1425920391801987/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16349/100000 : ℝ) ^ (4735/1024 : ℝ) ≤ (23076229339282731/100000000000000000000 : ℝ) := by
    have hpowers : (16349/100000 : ℝ)^4735 ≤ (23076229339282731/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16349 : ℕ)^4735*100000000000000000000^1024 ≤ 23076229339282731^1024*100000^4735 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16349 100000 23076229339282731 100000000000000000000 4735 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16349/100000 : ℝ)) (X := (23076229339282731/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001425920391801987/25000000000000000000 : ℝ) ≤ (400004933845311/400000000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (25001425920391801987/25000000000000000000 : ℝ)^1024 ≤ (400004933845311/400000000000000 : ℝ)^4735 := by
      have hnat : (25001425920391801987 : ℕ)^1024*400000000000000^4735 ≤ 400004933845311^4735*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001425920391801987 25000000000000000000 400004933845311 400000000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400004933845311/400000000000000 : ℝ)) (X := (25001425920391801987/25000000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005185614024577341/20000000000000000000 : ℝ) ≤ (625035041772173/625000000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (20005185614024577341/20000000000000000000 : ℝ)^1024 ≤ (625035041772173/625000000000000 : ℝ)^4735 := by
      have hnat : (20005185614024577341 : ℕ)^1024*625000000000000^4735 ≤ 625035041772173^4735*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005185614024577341 20000000000000000000 625035041772173 625000000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625035041772173/625000000000000 : ℝ)) (X := (20005185614024577341/20000000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023076229339282731/50000000000000000000 : ℝ) ≤ (10000997990576761/10000000000000000 : ℝ) ^ (4735/1024 : ℝ) := by
    have hpowers : (50023076229339282731/50000000000000000000 : ℝ)^1024 ≤ (10000997990576761/10000000000000000 : ℝ)^4735 := by
      have hnat : (50023076229339282731 : ℕ)^1024*10000000000000000^4735 ≤ 10000997990576761^4735*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023076229339282731 50000000000000000000 10000997990576761 10000000000000000 1024 4735 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000997990576761/10000000000000000 : ℝ)) (X := (50023076229339282731/50000000000000000000 : ℝ)) (by norm_num) 4735 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1425920391801987/50000000000000000000 : ℝ) ≤ ((59461635487945270553/59470000000000000000 : ℝ)+2*(437322221993/594700000000000 : ℝ)*(5201/50000 : ℝ))^(4735/1024 : ℝ) := by
    rw [show (59461635487945270553/59470000000000000000 : ℝ)+2*(437322221993/594700000000000 : ℝ)*(5201/50000 : ℝ)=(400004933845311/400000000000000 : ℝ) by norm_num, show 1+2*(1425920391801987/50000000000000000000 : ℝ)=(25001425920391801987/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23076229339282731/100000000000000000000 : ℝ)+(1425920391801987/50000000000000000000 : ℝ) ≤ ((59461635487945270553/59470000000000000000 : ℝ)+(437322221993/594700000000000 : ℝ)*((16349/100000 : ℝ)+(5201/50000 : ℝ)))^(4735/1024 : ℝ) := by
    rw [show (59461635487945270553/59470000000000000000 : ℝ)+(437322221993/594700000000000 : ℝ)*((16349/100000 : ℝ)+(5201/50000 : ℝ))=(625035041772173/625000000000000 : ℝ) by norm_num, show 1+(23076229339282731/100000000000000000000 : ℝ)+(1425920391801987/50000000000000000000 : ℝ)=(20005185614024577341/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23076229339282731/100000000000000000000 : ℝ) ≤ ((59461635487945270553/59470000000000000000 : ℝ)+2*(437322221993/594700000000000 : ℝ)*(16349/100000 : ℝ))^(4735/1024 : ℝ) := by
    rw [show (59461635487945270553/59470000000000000000 : ℝ)+2*(437322221993/594700000000000 : ℝ)*(16349/100000 : ℝ)=(10000997990576761/10000000000000000 : ℝ) by norm_num, show 1+2*(23076229339282731/100000000000000000000 : ℝ)=(50023076229339282731/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (59461635487945270553/59470000000000000000 : ℝ)*(X 1 0+X 2 0)+(437322221993/594700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (5201/50000 : ℝ)) (hi := (16349/100000 : ℝ)) (c := (59461635487945270553/59470000000000000000 : ℝ)) (alpha := (437322221993/594700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (59461635487945270553/59470000000000000000 : ℝ)*(X 0 1+X 2 1)+(437322221993/594700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (5201/50000 : ℝ)) (hi := (16349/100000 : ℝ)) (c := (59461635487945270553/59470000000000000000 : ℝ)) (alpha := (437322221993/594700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (59461635487945270553/59470000000000000000 : ℝ)*(X 0 2+X 1 2)+(437322221993/594700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4735/1024 : ℝ)) (lo := (5201/50000 : ℝ)) (hi := (16349/100000 : ℝ)) (c := (59461635487945270553/59470000000000000000 : ℝ)) (alpha := (437322221993/594700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1441618959/10000000000 : ℝ)*X 0 0+(2709688973/5000000000 : ℝ)*X 0 1+(5419377699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1050218409/2000000000 : ℝ)*X 1 0+(-167785483/1000000000 : ℝ)*X 1 1+(5419378029/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1312773131/2500000000 : ℝ)*X 2 0+(2709688763/5000000000 : ℝ)*X 2 1+(-1677854869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((35132743/78125000 : ℝ)*X 0 0+(4089372641/10000000000 : ℝ)*X 0 1+(40893727/100000000 : ℝ)*X 0 2+(35132743/78125000 : ℝ)*X 1 0+(4089372641/10000000000 : ℝ)*X 1 1+(40893727/100000000 : ℝ)*X 1 2+(35132743/78125000 : ℝ)*X 2 0+(4089372641/10000000000 : ℝ)*X 2 1+(40893727/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1001529961/5000000000 : ℝ)*X 0 0+(2606902867/5000000000 : ℝ)*X 0 1+(5213806317/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1348268317/2500000000 : ℝ)*X 1 0+(-882287523/5000000000 : ℝ)*X 1 1+(104276129/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5393073583/10000000000 : ℝ)*X 2 0+(1042761133/2000000000 : ℝ)*X 2 1+(-70583027/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1965302723/5000000000 : ℝ)*X 0 0+(4372219543/10000000000 : ℝ)*X 0 1+(4372219233/10000000000 : ℝ)*X 0 2+(1965302723/5000000000 : ℝ)*X 1 0+(4372219543/10000000000 : ℝ)*X 1 1+(4372219233/10000000000 : ℝ)*X 1 2+(1965302723/5000000000 : ℝ)*X 2 0+(4372219543/10000000000 : ℝ)*X 2 1+(4372219233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-235468719/1250000000 : ℝ)*X 0 0+(1266774407/2500000000 : ℝ)*X 0 1+(5449382617/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5230363211/10000000000 : ℝ)*X 1 0+(-832365479/5000000000 : ℝ)*X 1 1+(2724691373/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((523036379/1000000000 : ℝ)*X 2 0+(5449383131/10000000000 : ℝ)*X 2 1+(-166472963/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((915452113/2000000000 : ℝ)*X 0 0+(2024007341/5000000000 : ℝ)*X 0 1+(101200343/250000000 : ℝ)*X 0 2+(915452113/2000000000 : ℝ)*X 1 0+(2024007341/5000000000 : ℝ)*X 1 1+(101200343/250000000 : ℝ)*X 1 2+(915452113/2000000000 : ℝ)*X 2 0+(2024007341/5000000000 : ℝ)*X 2 1+(101200343/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-779892269/5000000000 : ℝ)*X 0 0+(1112015181/2000000000 : ℝ)*X 0 1+(5193935057/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5406804127/10000000000 : ℝ)*X 1 0+(-1772653653/10000000000 : ℝ)*X 1 1+(1038786993/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((540680411/1000000000 : ℝ)*X 2 0+(2596967489/5000000000 : ℝ)*X 2 1+(-886326829/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1937117427/5000000000 : ℝ)*X 0 0+(2199755781/5000000000 : ℝ)*X 0 1+(4399511947/10000000000 : ℝ)*X 0 2+(1937117427/5000000000 : ℝ)*X 1 0+(2199755781/5000000000 : ℝ)*X 1 1+(4399511947/10000000000 : ℝ)*X 1 2+(1937117427/5000000000 : ℝ)*X 2 0+(2199755781/5000000000 : ℝ)*X 2 1+(4399511947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1605_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-64903/100000 : ℝ) ≤ (-964913882592011405991646845320343/1486750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (114868861/100000000000000 : ℝ)*(upper1) + (115785893/100000000000000 : ℝ)*(lower4) + (12156403/25000000000000 : ℝ)*(upper5) + (835962614167159/50000000000000 : ℝ)*(major0) + (835962614167159/50000000000000 : ℝ)*(major1) + (835962614167159/50000000000000 : ℝ)*(major2) + (6154644059/100000000000000 : ℝ)*(sp2) + (2134326799/100000000000000 : ℝ)*(sp3) + (299220422069719/12500000000000 : ℝ)*(sp4) + (598422387303253/25000000000000 : ℝ)*(sp5) + (1196879497252823/50000000000000 : ℝ)*(sp6) + (121464600120211/12500000000000 : ℝ)*(sp7) + (1772591953/100000000000000 : ℝ)*(sp12) + (37799968347/50000000000000 : ℝ)*(sp13) + (971718935288487/100000000000000 : ℝ)*(f.failure) + (1196882574574853/50000000000000 : ℝ)*(f.sum) + (47118346734859/7433750000000000000000000000 : ℝ)*base66 + (17762115038975068927/2973500000000000000000000000000000 : ℝ)*base67 + (23201446014999568927/2973500000000000000000000000000000 : ℝ)*base69 + (12997286097708068927/2973500000000000000000000000000000 : ℝ)*base71 + (68056215266841/29735000000000000000000000000 : ℝ)*base74 + (582277111232068927/2973500000000000000000000000000000 : ℝ)*base75 + (30332894634978068927/2973500000000000000000000000000000 : ℝ)*base77 + (20642365511036568927/2973500000000000000000000000000000 : ℝ)*base79 + (121337329189231/29735000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (18452273/10000000000000000000000 : ℝ)*base90 + (18452273/10000000000000000000000 : ℝ)*base92 + (18452273/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (2907/5000 : ℝ) ≤ (8644332476522553403711950639/14867500000000000000000000000 : ℝ) := by norm_num
    linear_combination (8626617/25000000000000 : ℝ)*(lower1) + (36136607/100000000000000 : ℝ)*(lower2) + (21031511/100000000000000 : ℝ)*(upper4) + (1756016219220151/100000000000000 : ℝ)*(major0) + (1756016219220151/100000000000000 : ℝ)*(major1) + (1756016219220151/100000000000000 : ℝ)*(major2) + (2472057567799539/100000000000000 : ℝ)*(sp0) + (247205714362623/10000000000000 : ℝ)*(sp1) + (494408741370753/20000000000000 : ℝ)*(sp2) + (510295810201629/50000000000000 : ℝ)*(sp3) + (2052166289/100000000000000 : ℝ)*(sp5) + (199307823/25000000000000 : ℝ)*(sp7) + (1627992981/100000000000000 : ℝ)*(sp8) + (3097787751/20000000000000 : ℝ)*(sp10) + (20411848352691/2000000000000 : ℝ)*(f.failure) + (61801479894813/2500000000000 : ℝ)*(f.sum) + (40491067150229/14867500000000000000000000000 : ℝ)*base65 + (1998006614946813503/5947000000000000000000000000000000 : ℝ)*base67 + (10573759760819186497/5947000000000000000000000000000000 : ℝ)*base70 + (17262076541356813503/5947000000000000000000000000000000 : ℝ)*base71 + (31357205797043/29735000000000000000000000000 : ℝ)*base73 + (55483299899326813503/5947000000000000000000000000000000 : ℝ)*base75 + (37030652636719186497/5947000000000000000000000000000000 : ℝ)*base78 + (3754593882404186497/5947000000000000000000000000000000 : ℝ)*base80 + (22451749881151/3716875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2169989/200000000000000000000 : ℝ)*base90 + (2169989/200000000000000000000 : ℝ)*base92 + (2169989/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80333/100000 : ℝ) ≤ (1194390349897078413678511392764499/1486750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3419571/50000000000000 : ℝ)*(upper0) + (31189569/50000000000000 : ℝ)*(lower1) + (5074967/20000000000000 : ℝ)*(lower3) + (193117361/50000000000000 : ℝ)*(upper4) + (931290452929587/50000000000000 : ℝ)*(major0) + (931290452929587/50000000000000 : ℝ)*(major1) + (931290452929587/50000000000000 : ℝ)*(major2) + (1086411083/100000000000000 : ℝ)*(sp0) + (22652292819/20000000000000 : ℝ)*(sp2) + (1226391973/2500000000000 : ℝ)*(sp3) + (2615854615573461/100000000000000 : ℝ)*(sp8) + (81745490687017/3125000000000 : ℝ)*(sp9) + (2615742440520449/100000000000000 : ℝ)*(sp10) + (1082478502406491/100000000000000 : ℝ)*(sp11) + (1082527558085411/100000000000000 : ℝ)*(f.failure) + (81745490687017/3125000000000 : ℝ)*(f.sum) + (465045601151/232304687500000000000000000 : ℝ)*base66 + (5698747706025348389/2973500000000000000000000000000000 : ℝ)*base68 + (23625239892826348389/2973500000000000000000000000000000 : ℝ)*base70 + (22071169570343848389/2973500000000000000000000000000000 : ℝ)*base72 + (21100643049317/7433750000000000000000000000 : ℝ)*base74 + (115850460625021348389/2973500000000000000000000000000000 : ℝ)*base76 + (1627930985634848389/2973500000000000000000000000000000 : ℝ)*base78 + (18624697202805848389/2973500000000000000000000000000000 : ℝ)*base80 + (425424148591043/29735000000000000000000000000 : ℝ)*base82 + (8337131/10000000000000000000000 : ℝ)*base89 + (8337131/10000000000000000000000 : ℝ)*base91 + (8337131/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-87773/100000 : ℝ) ≤ (-2609851326987456472467336557560161/2973500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (421947/25000000000000 : ℝ)*(lower3) + (27501579/100000000000000 : ℝ)*(lower4) + (53005977/100000000000000 : ℝ)*(upper5) + (1904375230205021/100000000000000 : ℝ)*(major0) + (1904375230205021/100000000000000 : ℝ)*(major1) + (1904375230205021/100000000000000 : ℝ)*(major2) + (25614377/100000000000000 : ℝ)*(sp4) + (2364196643/20000000000000 : ℝ)*(sp5) + (889664129/3125000000000 : ℝ)*(sp6) + (12261284941/100000000000000 : ℝ)*(sp7) + (2731188898570891/100000000000000 : ℝ)*(sp12) + (1365588551601027/50000000000000 : ℝ)*(sp13) + (136558022746657/5000000000000 : ℝ)*(sp14) + (553403028966957/50000000000000 : ℝ)*(sp15) + (221363663843771/20000000000000 : ℝ)*(f.failure) + (682797231046317/25000000000000 : ℝ)*(f.sum) + (93451950471297/29735000000000000000000000000 : ℝ)*base66 + (13367194632498653387/5947000000000000000000000000000000 : ℝ)*base68 + (411366126139653387/5947000000000000000000000000000000 : ℝ)*base70 + (43886401829650653387/5947000000000000000000000000000000 : ℝ)*base72 + (20294441095303/7433750000000000000000000000 : ℝ)*base74 + (29348930303247653387/5947000000000000000000000000000000 : ℝ)*base76 + (5858668021287346613/5947000000000000000000000000000000 : ℝ)*base77 + (9718125884752346613/5947000000000000000000000000000000 : ℝ)*base79 + (3432330280873/1858437500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (6677309/2000000000000000000000 : ℝ)*base90 + (6677309/2000000000000000000000 : ℝ)*base92 + (6677309/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1605_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16349/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5201/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64903/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2907/5000 : ℝ) else (80333/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87773/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1605_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1605_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16349/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5201/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64903/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2907/5000 : ℝ) else (80333/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87773/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1605_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4735/1024 : ℝ) ≤ p) (hpb : p ≤ (4739/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (172058521/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16349/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5201/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(64903/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2907/5000 : ℝ) else (80333/100000 : ℝ) ≤ X j i ∧ X j i ≤ (87773/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1605_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

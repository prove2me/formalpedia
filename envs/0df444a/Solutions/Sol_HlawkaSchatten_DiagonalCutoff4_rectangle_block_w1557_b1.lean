-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1557_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:23:52.620574+00:00
-- url     : https://prove2.me/submissions/1148da15-2bc9-4a55-86a4-b23bac607b80

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
theorem support_rectangle_w1557_s3_0 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1803236911/10000000000 : ℝ)*x 0 + (2714695571/5000000000 : ℝ)*x 1 + (41742763/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1803236911/10000000000 : ℝ)^4611 ≤ (2764484907419/25000000000000 : ℝ)^3587 := by
    have hnat : (1803236911 : ℕ)^4611*25000000000000^3587 ≤ 2764484907419^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1803236911 10000000000 2764484907419 25000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714695571/5000000000 : ℝ)^4611 ≤ (22803374847423/50000000000000 : ℝ)^3587 := by
    have hnat : (2714695571 : ℕ)^4611*50000000000000^3587 ≤ 22803374847423^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714695571 5000000000 22803374847423 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41742763/80000000 : ℝ)^4611 ≤ (43335310670593/100000000000000 : ℝ)^3587 := by
    have hnat : (41742763 : ℕ)^4611*100000000000000^3587 ≤ 43335310670593^3587*80000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41742763 80000000 43335310670593 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1803236911/10000000000 : ℝ), (2714695571/5000000000 : ℝ), (41742763/80000000 : ℝ)] ![(2764484907419/25000000000000 : ℝ), (22803374847423/50000000000000 : ℝ), (43335310670593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1803236911/10000000000 : ℝ)|^4611 ≤ (2764484907419/25000000000000 : ℝ)^3587
        have hw : |(-1803236911/10000000000 : ℝ)|=(1803236911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714695571/5000000000 : ℝ)|^4611 ≤ (22803374847423/50000000000000 : ℝ)^3587
        have hw : |(2714695571/5000000000 : ℝ)|=(2714695571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41742763/80000000 : ℝ)|^4611 ≤ (43335310670593/100000000000000 : ℝ)^3587
        have hw : |(41742763/80000000 : ℝ)|=(41742763/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s3_1 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349496567/10000000000 : ℝ)*x 0 + (-1911530401/10000000000 : ℝ)*x 1 + (5217845309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349496567/10000000000 : ℝ)^4611 ≤ (22372934819089/50000000000000 : ℝ)^3587 := by
    have hnat : (5349496567 : ℕ)^4611*50000000000000^3587 ≤ 22372934819089^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349496567 10000000000 22372934819089 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1911530401/10000000000 : ℝ)^4611 ≤ (1489852547207/12500000000000 : ℝ)^3587 := by
    have hnat : (1911530401 : ℕ)^4611*12500000000000^3587 ≤ 1489852547207^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1911530401 10000000000 1489852547207 12500000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217845309/10000000000 : ℝ)^4611 ≤ (2708456872873/6250000000000 : ℝ)^3587 := by
    have hnat : (5217845309 : ℕ)^4611*6250000000000^3587 ≤ 2708456872873^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217845309 10000000000 2708456872873 6250000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349496567/10000000000 : ℝ), (-1911530401/10000000000 : ℝ), (5217845309/10000000000 : ℝ)] ![(22372934819089/50000000000000 : ℝ), (1489852547207/12500000000000 : ℝ), (2708456872873/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349496567/10000000000 : ℝ)|^4611 ≤ (22372934819089/50000000000000 : ℝ)^3587
        have hw : |(5349496567/10000000000 : ℝ)|=(5349496567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1911530401/10000000000 : ℝ)|^4611 ≤ (1489852547207/12500000000000 : ℝ)^3587
        have hw : |(-1911530401/10000000000 : ℝ)|=(1911530401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217845309/10000000000 : ℝ)|^4611 ≤ (2708456872873/6250000000000 : ℝ)^3587
        have hw : |(5217845309/10000000000 : ℝ)|=(5217845309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s3_2 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674748333/5000000000 : ℝ)*x 0 + (2608922627/5000000000 : ℝ)*x 1 + (-955765171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674748333/5000000000 : ℝ)^4611 ≤ (44745870702661/100000000000000 : ℝ)^3587 := by
    have hnat : (2674748333 : ℕ)^4611*100000000000000^3587 ≤ 44745870702661^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674748333 5000000000 44745870702661 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608922627/5000000000 : ℝ)^4611 ≤ (2166765468939/5000000000000 : ℝ)^3587 := by
    have hnat : (2608922627 : ℕ)^4611*5000000000000^3587 ≤ 2166765468939^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608922627 5000000000 2166765468939 5000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (955765171/5000000000 : ℝ)^4611 ≤ (11918819904757/100000000000000 : ℝ)^3587 := by
    have hnat : (955765171 : ℕ)^4611*100000000000000^3587 ≤ 11918819904757^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955765171 5000000000 11918819904757 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674748333/5000000000 : ℝ), (2608922627/5000000000 : ℝ), (-955765171/5000000000 : ℝ)] ![(44745870702661/100000000000000 : ℝ), (2166765468939/5000000000000 : ℝ), (11918819904757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674748333/5000000000 : ℝ)|^4611 ≤ (44745870702661/100000000000000 : ℝ)^3587
        have hw : |(2674748333/5000000000 : ℝ)|=(2674748333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608922627/5000000000 : ℝ)|^4611 ≤ (2166765468939/5000000000000 : ℝ)^3587
        have hw : |(2608922627/5000000000 : ℝ)|=(2608922627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-955765171/5000000000 : ℝ)|^4611 ≤ (11918819904757/100000000000000 : ℝ)^3587
        have hw : |(-955765171/5000000000 : ℝ)|=(955765171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s3_3 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4249082179/10000000000 : ℝ)*x 0 + (4007505663/10000000000 : ℝ)*x 1 + (900490657/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4249082179/10000000000 : ℝ)^4611 ≤ (3327994203983/10000000000000 : ℝ)^3587 := by
    have hnat : (4249082179 : ℕ)^4611*10000000000000^3587 ≤ 3327994203983^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249082179 10000000000 3327994203983 10000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4007505663/10000000000 : ℝ)^4611 ≤ (6173543416903/20000000000000 : ℝ)^3587 := by
    have hnat : (4007505663 : ℕ)^4611*20000000000000^3587 ≤ 6173543416903^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4007505663 10000000000 6173543416903 20000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900490657/2000000000 : ℝ)^4611 ≤ (7170468172647/20000000000000 : ℝ)^3587 := by
    have hnat : (900490657 : ℕ)^4611*20000000000000^3587 ≤ 7170468172647^3587*2000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900490657 2000000000 7170468172647 20000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4249082179/10000000000 : ℝ), (4007505663/10000000000 : ℝ), (900490657/2000000000 : ℝ)] ![(3327994203983/10000000000000 : ℝ), (6173543416903/20000000000000 : ℝ), (7170468172647/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4249082179/10000000000 : ℝ)|^4611 ≤ (3327994203983/10000000000000 : ℝ)^3587
        have hw : |(4249082179/10000000000 : ℝ)|=(4249082179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4007505663/10000000000 : ℝ)|^4611 ≤ (6173543416903/20000000000000 : ℝ)^3587
        have hw : |(4007505663/10000000000 : ℝ)|=(4007505663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900490657/2000000000 : ℝ)|^4611 ≤ (7170468172647/20000000000000 : ℝ)^3587
        have hw : |(900490657/2000000000 : ℝ)|=(900490657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s3_4 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-901632809/5000000000 : ℝ)*x 0 + (5218963653/10000000000 : ℝ)*x 1 + (1085652891/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (901632809/5000000000 : ℝ)^4611 ≤ (34556768513/312500000000 : ℝ)^3587 := by
    have hnat : (901632809 : ℕ)^4611*312500000000^3587 ≤ 34556768513^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901632809 5000000000 34556768513 312500000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218963653/10000000000 : ℝ)^4611 ≤ (10836812483409/25000000000000 : ℝ)^3587 := by
    have hnat : (5218963653 : ℕ)^4611*25000000000000^3587 ≤ 10836812483409^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218963653 10000000000 10836812483409 25000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085652891/2000000000 : ℝ)^4611 ≤ (5699323016677/12500000000000 : ℝ)^3587 := by
    have hnat : (1085652891 : ℕ)^4611*12500000000000^3587 ≤ 5699323016677^3587*2000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085652891 2000000000 5699323016677 12500000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-901632809/5000000000 : ℝ), (5218963653/10000000000 : ℝ), (1085652891/2000000000 : ℝ)] ![(34556768513/312500000000 : ℝ), (10836812483409/25000000000000 : ℝ), (5699323016677/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-901632809/5000000000 : ℝ)|^4611 ≤ (34556768513/312500000000 : ℝ)^3587
        have hw : |(-901632809/5000000000 : ℝ)|=(901632809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218963653/10000000000 : ℝ)|^4611 ≤ (10836812483409/25000000000000 : ℝ)^3587
        have hw : |(5218963653/10000000000 : ℝ)|=(5218963653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085652891/2000000000 : ℝ)|^4611 ≤ (5699323016677/12500000000000 : ℝ)^3587
        have hw : |(1085652891/2000000000 : ℝ)|=(1085652891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s3_5 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661702053/1250000000 : ℝ)*x 0 + (-850555581/5000000000 : ℝ)*x 1 + (5428264407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661702053/1250000000 : ℝ)^4611 ≤ (44145924347051/100000000000000 : ℝ)^3587 := by
    have hnat : (661702053 : ℕ)^4611*100000000000000^3587 ≤ 44145924347051^3587*1250000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661702053 1250000000 44145924347051 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (850555581/5000000000 : ℝ)^4611 ≤ (5129746011671/50000000000000 : ℝ)^3587 := by
    have hnat : (850555581 : ℕ)^4611*50000000000000^3587 ≤ 5129746011671^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850555581 5000000000 5129746011671 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428264407/10000000000 : ℝ)^4611 ≤ (5699322951893/12500000000000 : ℝ)^3587 := by
    have hnat : (5428264407 : ℕ)^4611*12500000000000^3587 ≤ 5699322951893^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428264407 10000000000 5699322951893 12500000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661702053/1250000000 : ℝ), (-850555581/5000000000 : ℝ), (5428264407/10000000000 : ℝ)] ![(44145924347051/100000000000000 : ℝ), (5129746011671/50000000000000 : ℝ), (5699322951893/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661702053/1250000000 : ℝ)|^4611 ≤ (44145924347051/100000000000000 : ℝ)^3587
        have hw : |(661702053/1250000000 : ℝ)|=(661702053/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-850555581/5000000000 : ℝ)|^4611 ≤ (5129746011671/50000000000000 : ℝ)^3587
        have hw : |(-850555581/5000000000 : ℝ)|=(850555581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428264407/10000000000 : ℝ)|^4611 ≤ (5699322951893/12500000000000 : ℝ)^3587
        have hw : |(5428264407/10000000000 : ℝ)|=(5428264407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s3_6 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646808133/5000000000 : ℝ)*x 0 + (1085652899/2000000000 : ℝ)*x 1 + (-1701111257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646808133/5000000000 : ℝ)^4611 ≤ (44145922653263/100000000000000 : ℝ)^3587 := by
    have hnat : (2646808133 : ℕ)^4611*100000000000000^3587 ≤ 44145922653263^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646808133 5000000000 44145922653263 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085652899/2000000000 : ℝ)^4611 ≤ (45594584565309/100000000000000 : ℝ)^3587 := by
    have hnat : (1085652899 : ℕ)^4611*100000000000000^3587 ≤ 45594584565309^3587*2000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085652899 2000000000 45594584565309 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1701111257/10000000000 : ℝ)^4611 ≤ (2051898551971/20000000000000 : ℝ)^3587 := by
    have hnat : (1701111257 : ℕ)^4611*20000000000000^3587 ≤ 2051898551971^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1701111257 10000000000 2051898551971 20000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646808133/5000000000 : ℝ), (1085652899/2000000000 : ℝ), (-1701111257/10000000000 : ℝ)] ![(44145922653263/100000000000000 : ℝ), (45594584565309/100000000000000 : ℝ), (2051898551971/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646808133/5000000000 : ℝ)|^4611 ≤ (44145922653263/100000000000000 : ℝ)^3587
        have hw : |(2646808133/5000000000 : ℝ)|=(2646808133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085652899/2000000000 : ℝ)|^4611 ≤ (45594584565309/100000000000000 : ℝ)^3587
        have hw : |(1085652899/2000000000 : ℝ)|=(1085652899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1701111257/10000000000 : ℝ)|^4611 ≤ (2051898551971/20000000000000 : ℝ)^3587
        have hw : |(-1701111257/10000000000 : ℝ)|=(1701111257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s3_7 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2124574709/5000000000 : ℝ)*x 0 + (562479591/1250000000 : ℝ)*x 1 + (31329233/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2124574709/5000000000 : ℝ)^4611 ≤ (33280619016033/100000000000000 : ℝ)^3587 := by
    have hnat : (2124574709 : ℕ)^4611*100000000000000^3587 ≤ 33280619016033^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124574709 5000000000 33280619016033 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562479591/1250000000 : ℝ)^4611 ≤ (447819498733/1250000000000 : ℝ)^3587 := by
    have hnat : (562479591 : ℕ)^4611*1250000000000^3587 ≤ 447819498733^3587*1250000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562479591 1250000000 447819498733 1250000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31329233/78125000 : ℝ)^4611 ≤ (30893821069551/100000000000000 : ℝ)^3587 := by
    have hnat : (31329233 : ℕ)^4611*100000000000000^3587 ≤ 30893821069551^3587*78125000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31329233 78125000 30893821069551 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2124574709/5000000000 : ℝ), (562479591/1250000000 : ℝ), (31329233/78125000 : ℝ)] ![(33280619016033/100000000000000 : ℝ), (447819498733/1250000000000 : ℝ), (30893821069551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2124574709/5000000000 : ℝ)|^4611 ≤ (33280619016033/100000000000000 : ℝ)^3587
        have hw : |(2124574709/5000000000 : ℝ)|=(2124574709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562479591/1250000000 : ℝ)|^4611 ≤ (447819498733/1250000000000 : ℝ)^3587
        have hw : |(562479591/1250000000 : ℝ)|=(562479591/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31329233/78125000 : ℝ)|^4611 ≤ (30893821069551/100000000000000 : ℝ)^3587
        have hw : |(31329233/78125000 : ℝ)|=(31329233/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1557_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83491779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1981/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1343/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11041/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7763/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1981/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1343/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1981/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1343/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1981/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1343/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1981/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1343/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1981/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1343/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1981/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1343/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1343/12500 : ℝ) ^ (4609/1024 : ℝ) ≤ (871627386256071/20000000000000000000 : ℝ) := by
    have hpowers : (1343/12500 : ℝ)^4609 ≤ (871627386256071/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1343 : ℕ)^4609*20000000000000000000^1024 ≤ 871627386256071^1024*12500^4609 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1343 12500 871627386256071 20000000000000000000 4609 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1343/12500 : ℝ)) (X := (871627386256071/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1981/12500 : ℝ) ^ (4609/1024 : ℝ) ≤ (12533541714156999/50000000000000000000 : ℝ) := by
    have hpowers : (1981/12500 : ℝ)^4609 ≤ (12533541714156999/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1981 : ℕ)^4609*50000000000000000000^1024 ≤ 12533541714156999^1024*12500^4609 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1981 12500 12533541714156999 50000000000000000000 4609 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1981/12500 : ℝ)) (X := (12533541714156999/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000871627386256071/10000000000000000000 : ℝ) ≤ (1250024205798137/1250000000000000 : ℝ) ^ (4609/1024 : ℝ) := by
    have hpowers : (10000871627386256071/10000000000000000000 : ℝ)^1024 ≤ (1250024205798137/1250000000000000 : ℝ)^4609 := by
      have hnat : (10000871627386256071 : ℕ)^1024*1250000000000000^4609 ≤ 1250024205798137^4609*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000871627386256071 10000000000000000000 1250024205798137 1250000000000000 1024 4609 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250024205798137/1250000000000000 : ℝ)) (X := (10000871627386256071/10000000000000000000 : ℝ)) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029425220359594353/100000000000000000000 : ℝ) ≤ (400026147084447/400000000000000 : ℝ) ^ (4609/1024 : ℝ) := by
    have hpowers : (100029425220359594353/100000000000000000000 : ℝ)^1024 ≤ (400026147084447/400000000000000 : ℝ)^4609 := by
      have hnat : (100029425220359594353 : ℕ)^1024*400000000000000^4609 ≤ 400026147084447^4609*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029425220359594353 100000000000000000000 400026147084447 400000000000000 1024 4609 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400026147084447/400000000000000 : ℝ)) (X := (100029425220359594353/100000000000000000000 : ℝ)) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012533541714156999/25000000000000000000 : ℝ) ≤ (5000556853918627/5000000000000000 : ℝ) ^ (4609/1024 : ℝ) := by
    have hpowers : (25012533541714156999/25000000000000000000 : ℝ)^1024 ≤ (5000556853918627/5000000000000000 : ℝ)^4609 := by
      have hnat : (25012533541714156999 : ℕ)^1024*5000000000000000^4609 ≤ 5000556853918627^4609*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012533541714156999 25000000000000000000 5000556853918627 5000000000000000 1024 4609 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000556853918627/5000000000000000 : ℝ)) (X := (25012533541714156999/25000000000000000000 : ℝ)) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(871627386256071/20000000000000000000 : ℝ) ≤ ((3189443951931721527/3190000000000000000 : ℝ)+2*(460030726079/510400000000000 : ℝ)*(1343/12500 : ℝ))^(4609/1024 : ℝ) := by
    rw [show (3189443951931721527/3190000000000000000 : ℝ)+2*(460030726079/510400000000000 : ℝ)*(1343/12500 : ℝ)=(1250024205798137/1250000000000000 : ℝ) by norm_num, show 1+2*(871627386256071/20000000000000000000 : ℝ)=(10000871627386256071/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12533541714156999/50000000000000000000 : ℝ)+(871627386256071/20000000000000000000 : ℝ) ≤ ((3189443951931721527/3190000000000000000 : ℝ)+(460030726079/510400000000000 : ℝ)*((1981/12500 : ℝ)+(1343/12500 : ℝ)))^(4609/1024 : ℝ) := by
    rw [show (3189443951931721527/3190000000000000000 : ℝ)+(460030726079/510400000000000 : ℝ)*((1981/12500 : ℝ)+(1343/12500 : ℝ))=(400026147084447/400000000000000 : ℝ) by norm_num, show 1+(12533541714156999/50000000000000000000 : ℝ)+(871627386256071/20000000000000000000 : ℝ)=(100029425220359594353/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12533541714156999/50000000000000000000 : ℝ) ≤ ((3189443951931721527/3190000000000000000 : ℝ)+2*(460030726079/510400000000000 : ℝ)*(1981/12500 : ℝ))^(4609/1024 : ℝ) := by
    rw [show (3189443951931721527/3190000000000000000 : ℝ)+2*(460030726079/510400000000000 : ℝ)*(1981/12500 : ℝ)=(5000556853918627/5000000000000000 : ℝ) by norm_num, show 1+2*(12533541714156999/50000000000000000000 : ℝ)=(25012533541714156999/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3189443951931721527/3190000000000000000 : ℝ)*(X 1 0+X 2 0)+(460030726079/510400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4609/1024 : ℝ)) (lo := (1343/12500 : ℝ)) (hi := (1981/12500 : ℝ)) (c := (3189443951931721527/3190000000000000000 : ℝ)) (alpha := (460030726079/510400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3189443951931721527/3190000000000000000 : ℝ)*(X 0 1+X 2 1)+(460030726079/510400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4609/1024 : ℝ)) (lo := (1343/12500 : ℝ)) (hi := (1981/12500 : ℝ)) (c := (3189443951931721527/3190000000000000000 : ℝ)) (alpha := (460030726079/510400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3189443951931721527/3190000000000000000 : ℝ)*(X 0 2+X 1 2)+(460030726079/510400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4609/1024 : ℝ)) (lo := (1343/12500 : ℝ)) (hi := (1981/12500 : ℝ)) (c := (3189443951931721527/3190000000000000000 : ℝ)) (alpha := (460030726079/510400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1803236911/10000000000 : ℝ)*X 0 0+(2714695571/5000000000 : ℝ)*X 0 1+(41742763/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349496567/10000000000 : ℝ)*X 1 0+(-1911530401/10000000000 : ℝ)*X 1 1+(5217845309/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674748333/5000000000 : ℝ)*X 2 0+(2608922627/5000000000 : ℝ)*X 2 1+(-955765171/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4249082179/10000000000 : ℝ)*X 0 0+(4007505663/10000000000 : ℝ)*X 0 1+(900490657/2000000000 : ℝ)*X 0 2+(4249082179/10000000000 : ℝ)*X 1 0+(4007505663/10000000000 : ℝ)*X 1 1+(900490657/2000000000 : ℝ)*X 1 2+(4249082179/10000000000 : ℝ)*X 2 0+(4007505663/10000000000 : ℝ)*X 2 1+(900490657/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-901632809/5000000000 : ℝ)*X 0 0+(5218963653/10000000000 : ℝ)*X 0 1+(1085652891/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661702053/1250000000 : ℝ)*X 1 0+(-850555581/5000000000 : ℝ)*X 1 1+(5428264407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646808133/5000000000 : ℝ)*X 2 0+(1085652899/2000000000 : ℝ)*X 2 1+(-1701111257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2124574709/5000000000 : ℝ)*X 0 0+(562479591/1250000000 : ℝ)*X 0 1+(31329233/78125000 : ℝ)*X 0 2+(2124574709/5000000000 : ℝ)*X 1 0+(562479591/1250000000 : ℝ)*X 1 1+(31329233/78125000 : ℝ)*X 1 2+(2124574709/5000000000 : ℝ)*X 2 0+(562479591/1250000000 : ℝ)*X 2 1+(31329233/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12479091563610054058323/2552000000000000000000000000 : ℝ) := by norm_num
    linear_combination (403665621/50000000000000 : ℝ)*(base19) + (447130117/50000000000000 : ℝ)*(base23) + (18499/6250000000000 : ℝ)*(lower2) + (667891/1000000000000 : ℝ)*(upper3) + (69109793/50000000000000 : ℝ)*(upper5) + (337378050163081/10000000000000 : ℝ)*(major0) + (337378050163081/10000000000000 : ℝ)*(major1) + (337378050163081/10000000000000 : ℝ)*(major2) + (4727120382423517/100000000000000 : ℝ)*(sp0) + (4727133266346143/100000000000000 : ℝ)*(sp1) + (73861455928393/1562500000000 : ℝ)*(sp2) + (1010210765942119/50000000000000 : ℝ)*(sp3) + (3422813467/25000000000000 : ℝ)*(sp4) + (1308675613/25000000000000 : ℝ)*(sp7) + (202042676658669/10000000000000 : ℝ)*(f.failure) + (945426814735477/20000000000000 : ℝ)*(f.sum) + (1739783954659/510400000000000000000000000 : ℝ)*base65 + (177710958882111563/31900000000000000000000000000000 : ℝ)*base68 + (288358344020388437/31900000000000000000000000000000 : ℝ)*base69 + (42663315040988437/31900000000000000000000000000000 : ℝ)*base71 + (1138914092093/510400000000000000000000000 : ℝ)*base74 + (469950772853588437/31900000000000000000000000000000 : ℝ)*base75 + (143473955375911563/31900000000000000000000000000000 : ℝ)*base78 + (186306426323111563/31900000000000000000000000000000 : ℝ)*base80 + (12968091243111/2552000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (582151/500000000000000000000 : ℝ)*base89 + (582151/500000000000000000000 : ℝ)*base91 + (582151/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (460359155055992591184930951/39875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1993186373/100000000000000 : ℝ)*(base19) + (484690287/25000000000000 : ℝ)*(base23) + (235900131/100000000000000 : ℝ)*(upper3) + (137789/250000000000 : ℝ)*(lower4) + (64957693/25000000000000 : ℝ)*(upper5) + (852487326692729/25000000000000 : ℝ)*(major0) + (852487326692729/25000000000000 : ℝ)*(major1) + (852487326692729/25000000000000 : ℝ)*(major2) + (31004718167/100000000000000 : ℝ)*(sp1) + (29494773067/100000000000000 : ℝ)*(sp2) + (4777811362423071/100000000000000 : ℝ)*(sp4) + (1194444591129633/25000000000000 : ℝ)*(sp5) + (597222491111107/12500000000000 : ℝ)*(sp6) + (408417373256703/20000000000000 : ℝ)*(sp7) + (408417373256703/20000000000000 : ℝ)*(f.failure) + (4777811362423071/100000000000000 : ℝ)*(f.sum) + (22331002498631/6380000000000000000000000000 : ℝ)*base65 + (650113587876870933/79750000000000000000000000000000 : ℝ)*base67 + (212118981162370933/79750000000000000000000000000000 : ℝ)*base69 + (570756815667870933/79750000000000000000000000000000 : ℝ)*base71 + (54368693253371/6380000000000000000000000000 : ℝ)*base73 + (147894675142129067/79750000000000000000000000000000 : ℝ)*base76 + (351107446803120933/79750000000000000000000000000000 : ℝ)*base77 + (125160356279379067/79750000000000000000000000000000 : ℝ)*base80 + (28989137316929/6380000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2855363/1000000000000000000000 : ℝ)*base90 + (2855363/1000000000000000000000 : ℝ)*base92 + (2855363/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1557_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83491779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1981/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1343/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11041/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7763/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1557_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1557_s4_0 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-901749099/5000000000 : ℝ)*x 0 + (1356910747/2500000000 : ℝ)*x 1 + (5219420397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (901749099/5000000000 : ℝ)^4611 ≤ (2764999841889/25000000000000 : ℝ)^3587 := by
    have hnat : (901749099 : ℕ)^4611*25000000000000^3587 ≤ 2764999841889^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901749099 5000000000 2764999841889 25000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356910747/2500000000 : ℝ)^4611 ≤ (22793937032239/50000000000000 : ℝ)^3587 := by
    have hnat : (1356910747 : ℕ)^4611*50000000000000^3587 ≤ 22793937032239^3587*2500000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356910747 2500000000 22793937032239 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219420397/10000000000 : ℝ)^4611 ≤ (8670425311589/20000000000000 : ℝ)^3587 := by
    have hnat : (5219420397 : ℕ)^4611*20000000000000^3587 ≤ 8670425311589^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219420397 10000000000 8670425311589 20000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-901749099/5000000000 : ℝ), (1356910747/2500000000 : ℝ), (5219420397/10000000000 : ℝ)] ![(2764999841889/25000000000000 : ℝ), (22793937032239/50000000000000 : ℝ), (8670425311589/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-901749099/5000000000 : ℝ)|^4611 ≤ (2764999841889/25000000000000 : ℝ)^3587
        have hw : |(-901749099/5000000000 : ℝ)|=(901749099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356910747/2500000000 : ℝ)|^4611 ≤ (22793937032239/50000000000000 : ℝ)^3587
        have hw : |(1356910747/2500000000 : ℝ)|=(1356910747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219420397/10000000000 : ℝ)|^4611 ≤ (8670425311589/20000000000000 : ℝ)^3587
        have hw : |(5219420397/10000000000 : ℝ)|=(5219420397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s4_1 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674517413/5000000000 : ℝ)*x 0 + (-955025769/5000000000 : ℝ)*x 1 + (2609710211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674517413/5000000000 : ℝ)^4611 ≤ (699076638969/1562500000000 : ℝ)^3587 := by
    have hnat : (2674517413 : ℕ)^4611*1562500000000^3587 ≤ 699076638969^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674517413 5000000000 699076638969 1562500000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (955025769/5000000000 : ℝ)^4611 ≤ (5953484132323/50000000000000 : ℝ)^3587 := by
    have hnat : (955025769 : ℕ)^4611*50000000000000^3587 ≤ 5953484132323^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955025769 5000000000 5953484132323 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609710211/5000000000 : ℝ)^4611 ≤ (43352126824871/100000000000000 : ℝ)^3587 := by
    have hnat : (2609710211 : ℕ)^4611*100000000000000^3587 ≤ 43352126824871^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609710211 5000000000 43352126824871 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674517413/5000000000 : ℝ), (-955025769/5000000000 : ℝ), (2609710211/5000000000 : ℝ)] ![(699076638969/1562500000000 : ℝ), (5953484132323/50000000000000 : ℝ), (43352126824871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674517413/5000000000 : ℝ)|^4611 ≤ (699076638969/1562500000000 : ℝ)^3587
        have hw : |(2674517413/5000000000 : ℝ)|=(2674517413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-955025769/5000000000 : ℝ)|^4611 ≤ (5953484132323/50000000000000 : ℝ)^3587
        have hw : |(-955025769/5000000000 : ℝ)|=(955025769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609710211/5000000000 : ℝ)|^4611 ≤ (43352126824871/100000000000000 : ℝ)^3587
        have hw : |(2609710211/5000000000 : ℝ)|=(2609710211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s4_2 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349034871/10000000000 : ℝ)*x 0 + (5219420383/10000000000 : ℝ)*x 1 + (-191005153/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349034871/10000000000 : ℝ)^4611 ≤ (2237045268893/5000000000000 : ℝ)^3587 := by
    have hnat : (5349034871 : ℕ)^4611*5000000000000^3587 ≤ 2237045268893^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349034871 10000000000 2237045268893 5000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219420383/10000000000 : ℝ)^4611 ≤ (21676063204233/50000000000000 : ℝ)^3587 := by
    have hnat : (5219420383 : ℕ)^4611*50000000000000^3587 ≤ 21676063204233^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219420383 10000000000 21676063204233 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (191005153/1000000000 : ℝ)^4611 ≤ (5953484100269/50000000000000 : ℝ)^3587 := by
    have hnat : (191005153 : ℕ)^4611*50000000000000^3587 ≤ 5953484100269^3587*1000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191005153 1000000000 5953484100269 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349034871/10000000000 : ℝ), (5219420383/10000000000 : ℝ), (-191005153/1000000000 : ℝ)] ![(2237045268893/5000000000000 : ℝ), (21676063204233/50000000000000 : ℝ), (5953484100269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349034871/10000000000 : ℝ)|^4611 ≤ (2237045268893/5000000000000 : ℝ)^3587
        have hw : |(5349034871/10000000000 : ℝ)|=(5349034871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219420383/10000000000 : ℝ)|^4611 ≤ (21676063204233/50000000000000 : ℝ)^3587
        have hw : |(5219420383/10000000000 : ℝ)|=(5219420383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-191005153/1000000000 : ℝ)|^4611 ≤ (5953484100269/50000000000000 : ℝ)^3587
        have hw : |(-191005153/1000000000 : ℝ)|=(191005153/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s4_3 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4249247457/10000000000 : ℝ)*x 0 + (802274949/2000000000 : ℝ)*x 1 + (2249273573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4249247457/10000000000 : ℝ)^4611 ≤ (8320401524627/25000000000000 : ℝ)^3587 := by
    have hnat : (4249247457 : ℕ)^4611*25000000000000^3587 ≤ 8320401524627^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249247457 10000000000 8320401524627 25000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (802274949/2000000000 : ℝ)^4611 ≤ (15453015735561/50000000000000 : ℝ)^3587 := by
    have hnat : (802274949 : ℕ)^4611*50000000000000^3587 ≤ 15453015735561^3587*2000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802274949 2000000000 15453015735561 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249273573/5000000000 : ℝ)^4611 ≤ (2238272650863/6250000000000 : ℝ)^3587 := by
    have hnat : (2249273573 : ℕ)^4611*6250000000000^3587 ≤ 2238272650863^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249273573 5000000000 2238272650863 6250000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4249247457/10000000000 : ℝ), (802274949/2000000000 : ℝ), (2249273573/5000000000 : ℝ)] ![(8320401524627/25000000000000 : ℝ), (15453015735561/50000000000000 : ℝ), (2238272650863/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4249247457/10000000000 : ℝ)|^4611 ≤ (8320401524627/25000000000000 : ℝ)^3587
        have hw : |(4249247457/10000000000 : ℝ)|=(4249247457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(802274949/2000000000 : ℝ)|^4611 ≤ (15453015735561/50000000000000 : ℝ)^3587
        have hw : |(802274949/2000000000 : ℝ)|=(802274949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249273573/5000000000 : ℝ)|^4611 ≤ (2238272650863/6250000000000 : ℝ)^3587
        have hw : |(2249273573/5000000000 : ℝ)|=(2249273573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s4_4 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1803525517/10000000000 : ℝ)*x 0 + (5220504083/10000000000 : ℝ)*x 1 + (5426551327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1803525517/10000000000 : ℝ)^4611 ≤ (2212042945891/20000000000000 : ℝ)^3587 := by
    have hnat : (1803525517 : ℕ)^4611*20000000000000^3587 ≤ 2212042945891^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1803525517 10000000000 2212042945891 20000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220504083/10000000000 : ℝ)^4611 ≤ (43363697486331/100000000000000 : ℝ)^3587 := by
    have hnat : (5220504083 : ℕ)^4611*100000000000000^3587 ≤ 43363697486331^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220504083 10000000000 43363697486331 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426551327/10000000000 : ℝ)^4611 ≤ (45576087774053/100000000000000 : ℝ)^3587 := by
    have hnat : (5426551327 : ℕ)^4611*100000000000000^3587 ≤ 45576087774053^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426551327 10000000000 45576087774053 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1803525517/10000000000 : ℝ), (5220504083/10000000000 : ℝ), (5426551327/10000000000 : ℝ)] ![(2212042945891/20000000000000 : ℝ), (43363697486331/100000000000000 : ℝ), (45576087774053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1803525517/10000000000 : ℝ)|^4611 ≤ (2212042945891/20000000000000 : ℝ)^3587
        have hw : |(-1803525517/10000000000 : ℝ)|=(1803525517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220504083/10000000000 : ℝ)|^4611 ≤ (43363697486331/100000000000000 : ℝ)^3587
        have hw : |(5220504083/10000000000 : ℝ)|=(5220504083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426551327/10000000000 : ℝ)|^4611 ≤ (45576087774053/100000000000000 : ℝ)^3587
        have hw : |(5426551327/10000000000 : ℝ)|=(5426551327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s4_5 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294032833/10000000000 : ℝ)*x 0 + (-425730167/2500000000 : ℝ)*x 1 + (5426551419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294032833/10000000000 : ℝ)^4611 ≤ (4415038837469/10000000000000 : ℝ)^3587 := by
    have hnat : (5294032833 : ℕ)^4611*10000000000000^3587 ≤ 4415038837469^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294032833 10000000000 4415038837469 10000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425730167/2500000000 : ℝ)^4611 ≤ (5136761418477/50000000000000 : ℝ)^3587 := by
    have hnat : (425730167 : ℕ)^4611*50000000000000^3587 ≤ 5136761418477^3587*2500000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425730167 2500000000 5136761418477 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426551419/10000000000 : ℝ)^4611 ≤ (45576088767317/100000000000000 : ℝ)^3587 := by
    have hnat : (5426551419 : ℕ)^4611*100000000000000^3587 ≤ 45576088767317^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426551419 10000000000 45576088767317 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294032833/10000000000 : ℝ), (-425730167/2500000000 : ℝ), (5426551419/10000000000 : ℝ)] ![(4415038837469/10000000000000 : ℝ), (5136761418477/50000000000000 : ℝ), (45576088767317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294032833/10000000000 : ℝ)|^4611 ≤ (4415038837469/10000000000000 : ℝ)^3587
        have hw : |(5294032833/10000000000 : ℝ)|=(5294032833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-425730167/2500000000 : ℝ)|^4611 ≤ (5136761418477/50000000000000 : ℝ)^3587
        have hw : |(-425730167/2500000000 : ℝ)|=(425730167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426551419/10000000000 : ℝ)|^4611 ≤ (45576088767317/100000000000000 : ℝ)^3587
        have hw : |(5426551419/10000000000 : ℝ)|=(5426551419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s4_6 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647016429/5000000000 : ℝ)*x 0 + (1356637869/2500000000 : ℝ)*x 1 + (-340584111/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647016429/5000000000 : ℝ)^4611 ≤ (441503886427/1000000000000 : ℝ)^3587 := by
    have hnat : (2647016429 : ℕ)^4611*1000000000000^3587 ≤ 441503886427^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647016429 5000000000 441503886427 1000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356637869/2500000000 : ℝ)^4611 ≤ (45576089382709/100000000000000 : ℝ)^3587 := by
    have hnat : (1356637869 : ℕ)^4611*100000000000000^3587 ≤ 45576089382709^3587*2500000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356637869 2500000000 45576089382709 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340584111/2000000000 : ℝ)^4611 ≤ (16437635137/160000000000 : ℝ)^3587 := by
    have hnat : (340584111 : ℕ)^4611*160000000000^3587 ≤ 16437635137^3587*2000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340584111 2000000000 16437635137 160000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647016429/5000000000 : ℝ), (1356637869/2500000000 : ℝ), (-340584111/2000000000 : ℝ)] ![(441503886427/1000000000000 : ℝ), (45576089382709/100000000000000 : ℝ), (16437635137/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647016429/5000000000 : ℝ)|^4611 ≤ (441503886427/1000000000000 : ℝ)^3587
        have hw : |(2647016429/5000000000 : ℝ)|=(2647016429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356637869/2500000000 : ℝ)|^4611 ≤ (45576089382709/100000000000000 : ℝ)^3587
        have hw : |(1356637869/2500000000 : ℝ)|=(1356637869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-340584111/2000000000 : ℝ)|^4611 ≤ (16437635137/160000000000 : ℝ)^3587
        have hw : |(-340584111/2000000000 : ℝ)|=(340584111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s4_7 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4249311497/10000000000 : ℝ)*x 0 + (4496011823/10000000000 : ℝ)*x 1 + (2006964427/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4249311497/10000000000 : ℝ)^4611 ≤ (6656450174721/20000000000000 : ℝ)^3587 := by
    have hnat : (4249311497 : ℕ)^4611*20000000000000^3587 ≤ 6656450174721^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249311497 10000000000 6656450174721 20000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496011823/10000000000 : ℝ)^4611 ≤ (35786419258633/100000000000000 : ℝ)^3587 := by
    have hnat : (4496011823 : ℕ)^4611*100000000000000^3587 ≤ 35786419258633^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496011823 10000000000 35786419258633 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006964427/5000000000 : ℝ)^4611 ≤ (15465664923529/50000000000000 : ℝ)^3587 := by
    have hnat : (2006964427 : ℕ)^4611*50000000000000^3587 ≤ 15465664923529^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006964427 5000000000 15465664923529 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4249311497/10000000000 : ℝ), (4496011823/10000000000 : ℝ), (2006964427/5000000000 : ℝ)] ![(6656450174721/20000000000000 : ℝ), (35786419258633/100000000000000 : ℝ), (15465664923529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4249311497/10000000000 : ℝ)|^4611 ≤ (6656450174721/20000000000000 : ℝ)^3587
        have hw : |(4249311497/10000000000 : ℝ)|=(4249311497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496011823/10000000000 : ℝ)|^4611 ≤ (35786419258633/100000000000000 : ℝ)^3587
        have hw : |(4496011823/10000000000 : ℝ)|=(4496011823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2006964427/5000000000 : ℝ)|^4611 ≤ (15465664923529/50000000000000 : ℝ)^3587
        have hw : |(2006964427/5000000000 : ℝ)|=(2006964427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1557_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83491779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7763/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11041/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (443/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7763/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11041/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7763/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11041/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7763/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11041/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7763/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11041/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7763/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11041/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7763/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11041/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11041/100000 : ℝ) ^ (4609/1024 : ℝ) ≤ (307952191974441/6250000000000000000 : ℝ) := by
    have hpowers : (11041/100000 : ℝ)^4609 ≤ (307952191974441/6250000000000000000 : ℝ)^1024 := by
      have hnat : (11041 : ℕ)^4609*6250000000000000000^1024 ≤ 307952191974441^1024*100000^4609 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11041 100000 307952191974441 6250000000000000000 4609 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11041/100000 : ℝ)) (X := (307952191974441/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7763/50000 : ℝ) ^ (4609/1024 : ℝ) ≤ (4570967495617541/20000000000000000000 : ℝ) := by
    have hpowers : (7763/50000 : ℝ)^4609 ≤ (4570967495617541/20000000000000000000 : ℝ)^1024 := by
      have hnat : (7763 : ℕ)^4609*20000000000000000000^1024 ≤ 4570967495617541^1024*50000^4609 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7763 50000 4570967495617541 20000000000000000000 4609 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7763/50000 : ℝ)) (X := (4570967495617541/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125307952191974441/3125000000000000000 : ℝ) ≤ (10000218932321747/10000000000000000 : ℝ) ^ (4609/1024 : ℝ) := by
    have hpowers : (3125307952191974441/3125000000000000000 : ℝ)^1024 ≤ (10000218932321747/10000000000000000 : ℝ)^4609 := by
      have hnat : (3125307952191974441 : ℕ)^1024*10000000000000000^4609 ≤ 10000218932321747^4609*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125307952191974441 3125000000000000000 10000218932321747 10000000000000000 1024 4609 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000218932321747/10000000000000000 : ℝ)) (X := (3125307952191974441/3125000000000000000 : ℝ)) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027782072549678761/100000000000000000000 : ℝ) ≤ (10000617178757947/10000000000000000 : ℝ) ^ (4609/1024 : ℝ) := by
    have hpowers : (100027782072549678761/100000000000000000000 : ℝ)^1024 ≤ (10000617178757947/10000000000000000 : ℝ)^4609 := by
      have hnat : (100027782072549678761 : ℕ)^1024*10000000000000000^4609 ≤ 10000617178757947^4609*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027782072549678761 100000000000000000000 10000617178757947 10000000000000000 1024 4609 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000617178757947/10000000000000000 : ℝ)) (X := (100027782072549678761/100000000000000000000 : ℝ)) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004570967495617541/10000000000000000000 : ℝ) ≤ (10001015425194147/10000000000000000 : ℝ) ^ (4609/1024 : ℝ) := by
    have hpowers : (10004570967495617541/10000000000000000000 : ℝ)^1024 ≤ (10001015425194147/10000000000000000 : ℝ)^4609 := by
      have hnat : (10004570967495617541 : ℕ)^1024*10000000000000000^4609 ≤ 10001015425194147^4609*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004570967495617541 10000000000000000000 10001015425194147 10000000000000000 1024 4609 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001015425194147/10000000000000000 : ℝ)) (X := (10004570967495617541/10000000000000000000 : ℝ)) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(307952191974441/6250000000000000000 : ℝ) ≤ ((8968437566731773379/8970000000000000000 : ℝ)+2*(1991232181/2242500000000 : ℝ)*(11041/100000 : ℝ))^(4609/1024 : ℝ) := by
    rw [show (8968437566731773379/8970000000000000000 : ℝ)+2*(1991232181/2242500000000 : ℝ)*(11041/100000 : ℝ)=(10000218932321747/10000000000000000 : ℝ) by norm_num, show 1+2*(307952191974441/6250000000000000000 : ℝ)=(3125307952191974441/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4570967495617541/20000000000000000000 : ℝ)+(307952191974441/6250000000000000000 : ℝ) ≤ ((8968437566731773379/8970000000000000000 : ℝ)+(1991232181/2242500000000 : ℝ)*((7763/50000 : ℝ)+(11041/100000 : ℝ)))^(4609/1024 : ℝ) := by
    rw [show (8968437566731773379/8970000000000000000 : ℝ)+(1991232181/2242500000000 : ℝ)*((7763/50000 : ℝ)+(11041/100000 : ℝ))=(10000617178757947/10000000000000000 : ℝ) by norm_num, show 1+(4570967495617541/20000000000000000000 : ℝ)+(307952191974441/6250000000000000000 : ℝ)=(100027782072549678761/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4570967495617541/20000000000000000000 : ℝ) ≤ ((8968437566731773379/8970000000000000000 : ℝ)+2*(1991232181/2242500000000 : ℝ)*(7763/50000 : ℝ))^(4609/1024 : ℝ) := by
    rw [show (8968437566731773379/8970000000000000000 : ℝ)+2*(1991232181/2242500000000 : ℝ)*(7763/50000 : ℝ)=(10001015425194147/10000000000000000 : ℝ) by norm_num, show 1+2*(4570967495617541/20000000000000000000 : ℝ)=(10004570967495617541/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8968437566731773379/8970000000000000000 : ℝ)*(X 1 0+X 2 0)+(1991232181/2242500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4609/1024 : ℝ)) (lo := (11041/100000 : ℝ)) (hi := (7763/50000 : ℝ)) (c := (8968437566731773379/8970000000000000000 : ℝ)) (alpha := (1991232181/2242500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8968437566731773379/8970000000000000000 : ℝ)*(X 0 1+X 2 1)+(1991232181/2242500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4609/1024 : ℝ)) (lo := (11041/100000 : ℝ)) (hi := (7763/50000 : ℝ)) (c := (8968437566731773379/8970000000000000000 : ℝ)) (alpha := (1991232181/2242500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8968437566731773379/8970000000000000000 : ℝ)*(X 0 2+X 1 2)+(1991232181/2242500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4609/1024 : ℝ)) (lo := (11041/100000 : ℝ)) (hi := (7763/50000 : ℝ)) (c := (8968437566731773379/8970000000000000000 : ℝ)) (alpha := (1991232181/2242500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-901749099/5000000000 : ℝ)*X 0 0+(1356910747/2500000000 : ℝ)*X 0 1+(5219420397/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674517413/5000000000 : ℝ)*X 1 0+(-955025769/5000000000 : ℝ)*X 1 1+(2609710211/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349034871/10000000000 : ℝ)*X 2 0+(5219420383/10000000000 : ℝ)*X 2 1+(-191005153/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4249247457/10000000000 : ℝ)*X 0 0+(802274949/2000000000 : ℝ)*X 0 1+(2249273573/5000000000 : ℝ)*X 0 2+(4249247457/10000000000 : ℝ)*X 1 0+(802274949/2000000000 : ℝ)*X 1 1+(2249273573/5000000000 : ℝ)*X 1 2+(4249247457/10000000000 : ℝ)*X 2 0+(802274949/2000000000 : ℝ)*X 2 1+(2249273573/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1803525517/10000000000 : ℝ)*X 0 0+(5220504083/10000000000 : ℝ)*X 0 1+(5426551327/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294032833/10000000000 : ℝ)*X 1 0+(-425730167/2500000000 : ℝ)*X 1 1+(5426551419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647016429/5000000000 : ℝ)*X 2 0+(1356637869/2500000000 : ℝ)*X 2 1+(-340584111/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4249311497/10000000000 : ℝ)*X 0 0+(4496011823/10000000000 : ℝ)*X 0 1+(2006964427/5000000000 : ℝ)*X 0 2+(4249311497/10000000000 : ℝ)*X 1 0+(4496011823/10000000000 : ℝ)*X 1 1+(2006964427/5000000000 : ℝ)*X 1 2+(4249311497/10000000000 : ℝ)*X 2 0+(4496011823/10000000000 : ℝ)*X 2 1+(2006964427/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26114811273185315869265469/11500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (199107047/50000000000000 : ℝ)*(base19) + (389363279/100000000000000 : ℝ)*(base23) + (13172939/50000000000000 : ℝ)*(lower2) + (31897957/50000000000000 : ℝ)*(upper3) + (21302473/50000000000000 : ℝ)*(upper5) + (3427616662460081/100000000000000 : ℝ)*(major0) + (3427616662460081/100000000000000 : ℝ)*(major1) + (3427616662460081/100000000000000 : ℝ)*(major2) + (1200639848975891/25000000000000 : ℝ)*(sp0) + (2401282844069849/50000000000000 : ℝ)*(sp1) + (2401282848495257/50000000000000 : ℝ)*(sp2) + (2052664043348131/100000000000000 : ℝ)*(sp3) + (6690450229/100000000000000 : ℝ)*(sp4) + (3119523127/100000000000000 : ℝ)*(sp7) + (1026333581435629/50000000000000 : ℝ)*(f.failure) + (37520047549639/781250000000 : ℝ)*(f.sum) + (96758044373/69000000000000000000000000 : ℝ)*base66 + (915203435528078177/69000000000000000000000000000000 : ℝ)*base68 + (574979133908078177/69000000000000000000000000000000 : ℝ)*base70 + (387062957879078177/69000000000000000000000000000000 : ℝ)*base72 + (36817055959/8625000000000000000000000 : ℝ)*base74 + (184170983693078177/69000000000000000000000000000000 : ℝ)*base76 + (344772246953078177/69000000000000000000000000000000 : ℝ)*base78 + (77381466515078177/69000000000000000000000000000000 : ℝ)*base80 + (4350525007/3450000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (14193991/2500000000000000000000 : ℝ)*base89 + (14193991/2500000000000000000000 : ℝ)*base91 + (14193991/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (134456903676598123509/18687500000000000000000000 : ℝ) := by norm_num
    linear_combination (401800697/50000000000000 : ℝ)*(base19) + (1042379599/100000000000000 : ℝ)*(base23) + (75712771/50000000000000 : ℝ)*(upper3) + (4074833/5000000000000 : ℝ)*(lower4) + (123583533/100000000000000 : ℝ)*(upper5) + (1731896463576273/50000000000000 : ℝ)*(major0) + (1731896463576273/50000000000000 : ℝ)*(major1) + (1731896463576273/50000000000000 : ℝ)*(major2) + (6294262163/50000000000000 : ℝ)*(sp1) + (3709666643/20000000000000 : ℝ)*(sp2) + (4853253884665421/100000000000000 : ℝ)*(sp4) + (48532404925397/1000000000000 : ℝ)*(sp5) + (4853234293952607/100000000000000 : ℝ)*(sp6) + (82973269192229/4000000000000 : ℝ)*(sp7) + (82973269192229/4000000000000 : ℝ)*(f.failure) + (4853253884665421/100000000000000 : ℝ)*(f.sum) + (323446539951/74750000000000000000000000 : ℝ)*base65 + (588601038732145489/149500000000000000000000000000000 : ℝ)*base67 + (852183115018354511/149500000000000000000000000000000 : ℝ)*base70 + (604482859823645489/149500000000000000000000000000000 : ℝ)*base71 + (370479835123/299000000000000000000000000 : ℝ)*base73 + (248367682334145489/149500000000000000000000000000000 : ℝ)*base75 + (447571617578854511/149500000000000000000000000000000 : ℝ)*base78 + (759501058700854511/149500000000000000000000000000000 : ℝ)*base80 + (331969723649/299000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (185391/200000000000000000000 : ℝ)*base89 + (185391/200000000000000000000 : ℝ)*base91 + (185391/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1557_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83491779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7763/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11041/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1557_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1557_s5_0 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1803526501/10000000000 : ℝ)*x 0 + (271372793/500000000 : ℝ)*x 1 + (5219588727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1803526501/10000000000 : ℝ)^4611 ≤ (1382527810821/12500000000000 : ℝ)^3587 := by
    have hnat : (1803526501 : ℕ)^4611*12500000000000^3587 ≤ 1382527810821^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1803526501 10000000000 1382527810821 12500000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271372793/500000000 : ℝ)^4611 ≤ (11396463414851/25000000000000 : ℝ)^3587 := by
    have hnat : (271372793 : ℕ)^4611*25000000000000^3587 ≤ 11396463414851^3587*500000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271372793 500000000 11396463414851 25000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219588727/10000000000 : ℝ)^4611 ≤ (43353923836513/100000000000000 : ℝ)^3587 := by
    have hnat : (5219588727 : ℕ)^4611*100000000000000^3587 ≤ 43353923836513^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219588727 10000000000 43353923836513 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1803526501/10000000000 : ℝ), (271372793/500000000 : ℝ), (5219588727/10000000000 : ℝ)] ![(1382527810821/12500000000000 : ℝ), (11396463414851/25000000000000 : ℝ), (43353923836513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1803526501/10000000000 : ℝ)|^4611 ≤ (1382527810821/12500000000000 : ℝ)^3587
        have hw : |(-1803526501/10000000000 : ℝ)|=(1803526501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271372793/500000000 : ℝ)|^4611 ≤ (11396463414851/25000000000000 : ℝ)^3587
        have hw : |(271372793/500000000 : ℝ)|=(271372793/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219588727/10000000000 : ℝ)|^4611 ≤ (43353923836513/100000000000000 : ℝ)^3587
        have hw : |(5219588727/10000000000 : ℝ)|=(5219588727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s5_1 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267449263/500000000 : ℝ)*x 0 + (-1909893793/10000000000 : ℝ)*x 1 + (5219588727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267449263/500000000 : ℝ)^4611 ≤ (5592546494549/12500000000000 : ℝ)^3587 := by
    have hnat : (267449263 : ℕ)^4611*12500000000000^3587 ≤ 5592546494549^3587*500000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267449263 500000000 5592546494549 12500000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1909893793/10000000000 : ℝ)^4611 ≤ (11905704196933/100000000000000 : ℝ)^3587 := by
    have hnat : (1909893793 : ℕ)^4611*100000000000000^3587 ≤ 11905704196933^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909893793 10000000000 11905704196933 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219588727/10000000000 : ℝ)^4611 ≤ (43353923836513/100000000000000 : ℝ)^3587 := by
    have hnat : (5219588727 : ℕ)^4611*100000000000000^3587 ≤ 43353923836513^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219588727 10000000000 43353923836513 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267449263/500000000 : ℝ), (-1909893793/10000000000 : ℝ), (5219588727/10000000000 : ℝ)] ![(5592546494549/12500000000000 : ℝ), (11905704196933/100000000000000 : ℝ), (43353923836513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267449263/500000000 : ℝ)|^4611 ≤ (5592546494549/12500000000000 : ℝ)^3587
        have hw : |(267449263/500000000 : ℝ)|=(267449263/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1909893793/10000000000 : ℝ)|^4611 ≤ (11905704196933/100000000000000 : ℝ)^3587
        have hw : |(-1909893793/10000000000 : ℝ)|=(1909893793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219588727/10000000000 : ℝ)|^4611 ≤ (43353923836513/100000000000000 : ℝ)^3587
        have hw : |(5219588727/10000000000 : ℝ)|=(5219588727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s5_2 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674492629/5000000000 : ℝ)*x 0 + (5219588729/10000000000 : ℝ)*x 1 + (-59684181/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674492629/5000000000 : ℝ)^4611 ≤ (44740371934887/100000000000000 : ℝ)^3587 := by
    have hnat : (2674492629 : ℕ)^4611*100000000000000^3587 ≤ 44740371934887^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674492629 5000000000 44740371934887 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219588729/10000000000 : ℝ)^4611 ≤ (43353923857867/100000000000000 : ℝ)^3587 := by
    have hnat : (5219588729 : ℕ)^4611*100000000000000^3587 ≤ 43353923857867^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219588729 10000000000 43353923857867 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59684181/312500000 : ℝ)^4611 ≤ (11905704188919/100000000000000 : ℝ)^3587 := by
    have hnat : (59684181 : ℕ)^4611*100000000000000^3587 ≤ 11905704188919^3587*312500000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59684181 312500000 11905704188919 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674492629/5000000000 : ℝ), (5219588729/10000000000 : ℝ), (-59684181/312500000 : ℝ)] ![(44740371934887/100000000000000 : ℝ), (43353923857867/100000000000000 : ℝ), (11905704188919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674492629/5000000000 : ℝ)|^4611 ≤ (44740371934887/100000000000000 : ℝ)^3587
        have hw : |(2674492629/5000000000 : ℝ)|=(2674492629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219588729/10000000000 : ℝ)|^4611 ≤ (43353923857867/100000000000000 : ℝ)^3587
        have hw : |(5219588729/10000000000 : ℝ)|=(5219588729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-59684181/312500000 : ℝ)|^4611 ≤ (11905704188919/100000000000000 : ℝ)^3587
        have hw : |(-59684181/312500000 : ℝ)|=(59684181/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s5_3 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4249264899/10000000000 : ℝ)*x 0 + (250736791/625000000 : ℝ)*x 1 + (4498129387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4249264899/10000000000 : ℝ)^4611 ≤ (33281781709839/100000000000000 : ℝ)^3587 := by
    have hnat : (4249264899 : ℕ)^4611*100000000000000^3587 ≤ 33281781709839^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249264899 10000000000 33281781709839 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250736791/625000000 : ℝ)^4611 ≤ (3863766366937/12500000000000 : ℝ)^3587 := by
    have hnat : (250736791 : ℕ)^4611*12500000000000^3587 ≤ 3863766366937^3587*625000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250736791 625000000 3863766366937 12500000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498129387/10000000000 : ℝ)^4611 ≤ (35808087331329/100000000000000 : ℝ)^3587 := by
    have hnat : (4498129387 : ℕ)^4611*100000000000000^3587 ≤ 35808087331329^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498129387 10000000000 35808087331329 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4249264899/10000000000 : ℝ), (250736791/625000000 : ℝ), (4498129387/10000000000 : ℝ)] ![(33281781709839/100000000000000 : ℝ), (3863766366937/12500000000000 : ℝ), (35808087331329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4249264899/10000000000 : ℝ)|^4611 ≤ (33281781709839/100000000000000 : ℝ)^3587
        have hw : |(4249264899/10000000000 : ℝ)|=(4249264899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(250736791/625000000 : ℝ)|^4611 ≤ (3863766366937/12500000000000 : ℝ)^3587
        have hw : |(250736791/625000000 : ℝ)|=(250736791/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498129387/10000000000 : ℝ)|^4611 ≤ (35808087331329/100000000000000 : ℝ)^3587
        have hw : |(4498129387/10000000000 : ℝ)|=(4498129387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s5_4 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-360710691/2000000000 : ℝ)*x 0 + (2610334239/5000000000 : ℝ)*x 1 + (5426368337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (360710691/2000000000 : ℝ)^4611 ≤ (2212086994407/20000000000000 : ℝ)^3587 := by
    have hnat : (360710691 : ℕ)^4611*20000000000000^3587 ≤ 2212086994407^3587*2000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360710691 2000000000 2212086994407 20000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610334239/5000000000 : ℝ)^4611 ≤ (43365452854297/100000000000000 : ℝ)^3587 := by
    have hnat : (2610334239 : ℕ)^4611*100000000000000^3587 ≤ 43365452854297^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610334239 5000000000 43365452854297 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426368337/10000000000 : ℝ)^4611 ≤ (5696764019981/12500000000000 : ℝ)^3587 := by
    have hnat : (5426368337 : ℕ)^4611*12500000000000^3587 ≤ 5696764019981^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426368337 10000000000 5696764019981 12500000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-360710691/2000000000 : ℝ), (2610334239/5000000000 : ℝ), (5426368337/10000000000 : ℝ)] ![(2212086994407/20000000000000 : ℝ), (43365452854297/100000000000000 : ℝ), (5696764019981/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-360710691/2000000000 : ℝ)|^4611 ≤ (2212086994407/20000000000000 : ℝ)^3587
        have hw : |(-360710691/2000000000 : ℝ)|=(360710691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610334239/5000000000 : ℝ)|^4611 ≤ (43365452854297/100000000000000 : ℝ)^3587
        have hw : |(2610334239/5000000000 : ℝ)|=(2610334239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426368337/10000000000 : ℝ)|^4611 ≤ (5696764019981/12500000000000 : ℝ)^3587
        have hw : |(5426368337/10000000000 : ℝ)|=(5426368337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s5_5 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294077289/10000000000 : ℝ)*x 0 + (-2724983/16000000 : ℝ)*x 1 + (1356592033/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294077289/10000000000 : ℝ)^4611 ≤ (275942906013/625000000000 : ℝ)^3587 := by
    have hnat : (5294077289 : ℕ)^4611*625000000000^3587 ≤ 275942906013^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294077289 10000000000 275942906013 625000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724983/16000000 : ℝ)^4611 ≤ (10275025083057/100000000000000 : ℝ)^3587 := by
    have hnat : (2724983 : ℕ)^4611*100000000000000^3587 ≤ 10275025083057^3587*16000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724983 16000000 10275025083057 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356592033/2500000000 : ℝ)^4611 ≤ (22787054973309/50000000000000 : ℝ)^3587 := by
    have hnat : (1356592033 : ℕ)^4611*50000000000000^3587 ≤ 22787054973309^3587*2500000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356592033 2500000000 22787054973309 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294077289/10000000000 : ℝ), (-2724983/16000000 : ℝ), (1356592033/2500000000 : ℝ)] ![(275942906013/625000000000 : ℝ), (10275025083057/100000000000000 : ℝ), (22787054973309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294077289/10000000000 : ℝ)|^4611 ≤ (275942906013/625000000000 : ℝ)^3587
        have hw : |(5294077289/10000000000 : ℝ)|=(5294077289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2724983/16000000 : ℝ)|^4611 ≤ (10275025083057/100000000000000 : ℝ)^3587
        have hw : |(-2724983/16000000 : ℝ)|=(2724983/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356592033/2500000000 : ℝ)|^4611 ≤ (22787054973309/50000000000000 : ℝ)^3587
        have hw : |(1356592033/2500000000 : ℝ)|=(1356592033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s5_6 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294077411/10000000000 : ℝ)*x 0 + (1356591987/2500000000 : ℝ)*x 1 + (-1703114461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294077411/10000000000 : ℝ)^4611 ≤ (22075433134987/50000000000000 : ℝ)^3587 := by
    have hnat : (5294077411 : ℕ)^4611*50000000000000^3587 ≤ 22075433134987^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294077411 10000000000 22075433134987 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356591987/2500000000 : ℝ)^4611 ≤ (4557410796011/10000000000000 : ℝ)^3587 := by
    have hnat : (1356591987 : ℕ)^4611*10000000000000^3587 ≤ 4557410796011^3587*2500000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356591987 2500000000 4557410796011 10000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1703114461/10000000000 : ℝ)^4611 ≤ (10275025750019/100000000000000 : ℝ)^3587 := by
    have hnat : (1703114461 : ℕ)^4611*100000000000000^3587 ≤ 10275025750019^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1703114461 10000000000 10275025750019 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294077411/10000000000 : ℝ), (1356591987/2500000000 : ℝ), (-1703114461/10000000000 : ℝ)] ![(22075433134987/50000000000000 : ℝ), (4557410796011/10000000000000 : ℝ), (10275025750019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294077411/10000000000 : ℝ)|^4611 ≤ (22075433134987/50000000000000 : ℝ)^3587
        have hw : |(5294077411/10000000000 : ℝ)|=(5294077411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356591987/2500000000 : ℝ)|^4611 ≤ (4557410796011/10000000000000 : ℝ)^3587
        have hw : |(1356591987/2500000000 : ℝ)|=(1356591987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1703114461/10000000000 : ℝ)|^4611 ≤ (10275025750019/100000000000000 : ℝ)^3587
        have hw : |(-1703114461/10000000000 : ℝ)|=(1703114461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s5_7 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212466451/500000000 : ℝ)*x 0 + (4495601991/10000000000 : ℝ)*x 1 + (4014334351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212466451/500000000 : ℝ)^4611 ≤ (33282427301229/100000000000000 : ℝ)^3587 := by
    have hnat : (212466451 : ℕ)^4611*100000000000000^3587 ≤ 33282427301229^3587*500000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212466451 500000000 33282427301229 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4495601991/10000000000 : ℝ)^4611 ≤ (35782225969959/100000000000000 : ℝ)^3587 := by
    have hnat : (4495601991 : ℕ)^4611*100000000000000^3587 ≤ 35782225969959^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495601991 10000000000 35782225969959 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4014334351/10000000000 : ℝ)^4611 ≤ (3866918338243/12500000000000 : ℝ)^3587 := by
    have hnat : (4014334351 : ℕ)^4611*12500000000000^3587 ≤ 3866918338243^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4014334351 10000000000 3866918338243 12500000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212466451/500000000 : ℝ), (4495601991/10000000000 : ℝ), (4014334351/10000000000 : ℝ)] ![(33282427301229/100000000000000 : ℝ), (35782225969959/100000000000000 : ℝ), (3866918338243/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212466451/500000000 : ℝ)|^4611 ≤ (33282427301229/100000000000000 : ℝ)^3587
        have hw : |(212466451/500000000 : ℝ)|=(212466451/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4495601991/10000000000 : ℝ)|^4611 ≤ (35782225969959/100000000000000 : ℝ)^3587
        have hw : |(4495601991/10000000000 : ℝ)|=(4495601991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4014334351/10000000000 : ℝ)|^4611 ≤ (3866918338243/12500000000000 : ℝ)^3587
        have hw : |(4014334351/10000000000 : ℝ)|=(4014334351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1557_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83491779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (5539/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (443/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (443/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (443/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (443/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (443/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (443/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (443/4000 : ℝ) ^ (4609/1024 : ℝ) ≤ (4995897839478119/100000000000000000000 : ℝ) := by
    have hpowers : (443/4000 : ℝ)^4609 ≤ (4995897839478119/100000000000000000000 : ℝ)^1024 := by
      have hnat : (443 : ℕ)^4609*100000000000000000000^1024 ≤ 4995897839478119^1024*4000^4609 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        443 4000 4995897839478119 100000000000000000000 4609 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (443/4000 : ℝ)) (X := (4995897839478119/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4609/1024 : ℝ) ≤ (22610710848432823/100000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4609 ≤ (22610710848432823/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4609*100000000000000000000^1024 ≤ 22610710848432823^1024*100000^4609 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 22610710848432823 100000000000000000000 4609 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (22610710848432823/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004995897839478119/50000000000000000000 : ℝ) ≤ (625013873943921/625000000000000 : ℝ) ^ (4609/1024 : ℝ) := by
    have hpowers : (50004995897839478119/50000000000000000000 : ℝ)^1024 ≤ (625013873943921/625000000000000 : ℝ)^4609 := by
      have hnat : (50004995897839478119 : ℕ)^1024*625000000000000^4609 ≤ 625013873943921^4609*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004995897839478119 50000000000000000000 625013873943921 625000000000000 1024 4609 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625013873943921/625000000000000 : ℝ)) (X := (50004995897839478119/50000000000000000000 : ℝ)) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013803304343955471/50000000000000000000 : ℝ) ≤ (10000613281246567/10000000000000000 : ℝ) ^ (4609/1024 : ℝ) := by
    have hpowers : (50013803304343955471/50000000000000000000 : ℝ)^1024 ≤ (10000613281246567/10000000000000000 : ℝ)^4609 := by
      have hnat : (50013803304343955471 : ℕ)^1024*10000000000000000^4609 ≤ 10000613281246567^4609*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013803304343955471 50000000000000000000 10000613281246567 10000000000000000 1024 4609 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000613281246567/10000000000000000 : ℝ)) (X := (50013803304343955471/50000000000000000000 : ℝ)) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022610710848432823/50000000000000000000 : ℝ) ≤ (5000502289695199/5000000000000000 : ℝ) ^ (4609/1024 : ℝ) := by
    have hpowers : (50022610710848432823/50000000000000000000 : ℝ)^1024 ≤ (5000502289695199/5000000000000000 : ℝ)^4609 := by
      have hnat : (50022610710848432823 : ℕ)^1024*5000000000000000^4609 ≤ 5000502289695199^4609*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022610710848432823 50000000000000000000 5000502289695199 5000000000000000 1024 4609 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000502289695199/5000000000000000 : ℝ)) (X := (50022610710848432823/50000000000000000000 : ℝ)) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4995897839478119/100000000000000000000 : ℝ) ≤ ((22066156289764810027/22070000000000000000 : ℝ)+2*(391298143831/441400000000000 : ℝ)*(443/4000 : ℝ))^(4609/1024 : ℝ) := by
    rw [show (22066156289764810027/22070000000000000000 : ℝ)+2*(391298143831/441400000000000 : ℝ)*(443/4000 : ℝ)=(625013873943921/625000000000000 : ℝ) by norm_num, show 1+2*(4995897839478119/100000000000000000000 : ℝ)=(50004995897839478119/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22610710848432823/100000000000000000000 : ℝ)+(4995897839478119/100000000000000000000 : ℝ) ≤ ((22066156289764810027/22070000000000000000 : ℝ)+(391298143831/441400000000000 : ℝ)*((15489/100000 : ℝ)+(443/4000 : ℝ)))^(4609/1024 : ℝ) := by
    rw [show (22066156289764810027/22070000000000000000 : ℝ)+(391298143831/441400000000000 : ℝ)*((15489/100000 : ℝ)+(443/4000 : ℝ))=(10000613281246567/10000000000000000 : ℝ) by norm_num, show 1+(22610710848432823/100000000000000000000 : ℝ)+(4995897839478119/100000000000000000000 : ℝ)=(50013803304343955471/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22610710848432823/100000000000000000000 : ℝ) ≤ ((22066156289764810027/22070000000000000000 : ℝ)+2*(391298143831/441400000000000 : ℝ)*(15489/100000 : ℝ))^(4609/1024 : ℝ) := by
    rw [show (22066156289764810027/22070000000000000000 : ℝ)+2*(391298143831/441400000000000 : ℝ)*(15489/100000 : ℝ)=(5000502289695199/5000000000000000 : ℝ) by norm_num, show 1+2*(22610710848432823/100000000000000000000 : ℝ)=(50022610710848432823/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22066156289764810027/22070000000000000000 : ℝ)*(X 1 0+X 2 0)+(391298143831/441400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4609/1024 : ℝ)) (lo := (443/4000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (22066156289764810027/22070000000000000000 : ℝ)) (alpha := (391298143831/441400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22066156289764810027/22070000000000000000 : ℝ)*(X 0 1+X 2 1)+(391298143831/441400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4609/1024 : ℝ)) (lo := (443/4000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (22066156289764810027/22070000000000000000 : ℝ)) (alpha := (391298143831/441400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22066156289764810027/22070000000000000000 : ℝ)*(X 0 2+X 1 2)+(391298143831/441400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4609/1024 : ℝ)) (lo := (443/4000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (22066156289764810027/22070000000000000000 : ℝ)) (alpha := (391298143831/441400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1803526501/10000000000 : ℝ)*X 0 0+(271372793/500000000 : ℝ)*X 0 1+(5219588727/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267449263/500000000 : ℝ)*X 1 0+(-1909893793/10000000000 : ℝ)*X 1 1+(5219588727/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674492629/5000000000 : ℝ)*X 2 0+(5219588729/10000000000 : ℝ)*X 2 1+(-59684181/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4249264899/10000000000 : ℝ)*X 0 0+(250736791/625000000 : ℝ)*X 0 1+(4498129387/10000000000 : ℝ)*X 0 2+(4249264899/10000000000 : ℝ)*X 1 0+(250736791/625000000 : ℝ)*X 1 1+(4498129387/10000000000 : ℝ)*X 1 2+(4249264899/10000000000 : ℝ)*X 2 0+(250736791/625000000 : ℝ)*X 2 1+(4498129387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-360710691/2000000000 : ℝ)*X 0 0+(2610334239/5000000000 : ℝ)*X 0 1+(5426368337/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294077289/10000000000 : ℝ)*X 1 0+(-2724983/16000000 : ℝ)*X 1 1+(1356592033/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294077411/10000000000 : ℝ)*X 2 0+(1356591987/2500000000 : ℝ)*X 2 1+(-1703114461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((212466451/500000000 : ℝ)*X 0 0+(4495601991/10000000000 : ℝ)*X 0 1+(4014334351/10000000000 : ℝ)*X 0 2+(212466451/500000000 : ℝ)*X 1 0+(4495601991/10000000000 : ℝ)*X 1 1+(4014334351/10000000000 : ℝ)*X 1 2+(212466451/500000000 : ℝ)*X 2 0+(4495601991/10000000000 : ℝ)*X 2 1+(4014334351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4783332910055130543519982473/551750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45845001/3125000000000 : ℝ)*(base19) + (684445123/50000000000000 : ℝ)*(base23) + (51538013/100000000000000 : ℝ)*(lower2) + (105962357/50000000000000 : ℝ)*(upper3) + (71343123/50000000000000 : ℝ)*(upper5) + (1716751537358611/50000000000000 : ℝ)*(major0) + (1716751537358611/50000000000000 : ℝ)*(major1) + (1716751537358611/50000000000000 : ℝ)*(major2) + (2405394942988179/50000000000000 : ℝ)*(sp0) + (4810812085716443/100000000000000 : ℝ)*(sp1) + (4810812183866229/100000000000000 : ℝ)*(sp2) + (514045343447213/25000000000000 : ℝ)*(sp3) + (23666780117/100000000000000 : ℝ)*(sp4) + (1366738703/12500000000000 : ℝ)*(sp7) + (514048076924619/25000000000000 : ℝ)*(f.failure) + (192432542110259/4000000000000 : ℝ)*(f.sum) + (6867534373871/2758750000000000000000000000 : ℝ)*base66 + (16031779602832357503/1103500000000000000000000000000000 : ℝ)*base68 + (13936150716625857503/1103500000000000000000000000000000 : ℝ)*base70 + (4043786526203357503/1103500000000000000000000000000000 : ℝ)*base72 + (28682578549077/5517500000000000000000000000 : ℝ)*base74 + (18754104951506857503/1103500000000000000000000000000000 : ℝ)*base76 + (8698815095060357503/1103500000000000000000000000000000 : ℝ)*base78 + (11512420882304857503/1103500000000000000000000000000000 : ℝ)*base80 + (45488753609559/11035000000000000000000000000 : ℝ)*base82 + (14207201/1250000000000000000000 : ℝ)*base89 + (14207201/1250000000000000000000 : ℝ)*base91 + (14207201/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3181443417648079936833517041/551750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (583914479/100000000000000 : ℝ)*(base19) + (18651943/1562500000000 : ℝ)*(base23) + (324841561/100000000000000 : ℝ)*(lower1) + (253824597/100000000000000 : ℝ)*(lower4) + (88926021/50000000000000 : ℝ)*(upper5) + (3469644482520839/100000000000000 : ℝ)*(major0) + (3469644482520839/100000000000000 : ℝ)*(major1) + (3469644482520839/100000000000000 : ℝ)*(major2) + (1903480187/25000000000000 : ℝ)*(sp0) + (441820013/25000000000000 : ℝ)*(sp2) + (4861445158728513/100000000000000 : ℝ)*(sp4) + (2430726094367391/50000000000000 : ℝ)*(sp5) + (4861449811644857/100000000000000 : ℝ)*(sp6) + (64932375005913/3125000000000 : ℝ)*(sp7) + (64932375005913/3125000000000 : ℝ)*(f.failure) + (4861452772649261/100000000000000 : ℝ)*(f.sum) + (82392131319219/22070000000000000000000000000 : ℝ)*base65 + (10574857285764102653/2207000000000000000000000000000000 : ℝ)*base67 + (8912249273563102653/2207000000000000000000000000000000 : ℝ)*base69 + (11977430574788102653/2207000000000000000000000000000000 : ℝ)*base71 + (14864670415789/22070000000000000000000000000 : ℝ)*base73 + (547131004334102653/2207000000000000000000000000000000 : ℝ)*base75 + (1425531772726897347/2207000000000000000000000000000000 : ℝ)*base78 + (24032082049814102653/2207000000000000000000000000000000 : ℝ)*base79 + (85679777534641/22070000000000000000000000000 : ℝ)*base82 + (951727/156250000000000000000 : ℝ)*base89 + (951727/156250000000000000000 : ℝ)*base91 + (951727/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1557_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83491779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (443/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5539/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1557_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1557_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83491779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1981/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1343/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5539/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1557_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1557_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1557_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83491779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1981/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1343/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5539/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1557_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

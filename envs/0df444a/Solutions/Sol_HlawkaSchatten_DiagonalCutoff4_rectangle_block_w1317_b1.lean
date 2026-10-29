-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1317_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:42:17.501761+00:00
-- url     : https://prove2.me/submissions/28d3beb8-84e5-49d5-a6b9-02ba8f226d78

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
theorem support_rectangle_w1317_s3_0 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2063731333/10000000000 : ℝ)*x 0 + (2715247617/5000000000 : ℝ)*x 1 + (2614322399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063731333/10000000000 : ℝ)^4277 ≤ (12557851016129/100000000000000 : ℝ)^3253 := by
    have hnat : (2063731333 : ℕ)^4277*100000000000000^3253 ≤ 12557851016129^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063731333 10000000000 12557851016129 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715247617/5000000000 : ℝ)^4277 ≤ (44809542595697/100000000000000 : ℝ)^3253 := by
    have hnat : (2715247617 : ℕ)^4277*100000000000000^3253 ≤ 44809542595697^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715247617 5000000000 44809542595697 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614322399/5000000000 : ℝ)^4277 ≤ (42632606373437/100000000000000 : ℝ)^3253 := by
    have hnat : (2614322399 : ℕ)^4277*100000000000000^3253 ≤ 42632606373437^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614322399 5000000000 42632606373437 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2063731333/10000000000 : ℝ), (2715247617/5000000000 : ℝ), (2614322399/5000000000 : ℝ)] ![(12557851016129/100000000000000 : ℝ), (44809542595697/100000000000000 : ℝ), (42632606373437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2063731333/10000000000 : ℝ)|^4277 ≤ (12557851016129/100000000000000 : ℝ)^3253
        have hw : |(-2063731333/10000000000 : ℝ)|=(2063731333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715247617/5000000000 : ℝ)|^4277 ≤ (44809542595697/100000000000000 : ℝ)^3253
        have hw : |(2715247617/5000000000 : ℝ)|=(2715247617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614322399/5000000000 : ℝ)|^4277 ≤ (42632606373437/100000000000000 : ℝ)^3253
        have hw : |(2614322399/5000000000 : ℝ)|=(2614322399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s3_1 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353604571/10000000000 : ℝ)*x 0 + (-1083480311/5000000000 : ℝ)*x 1 + (2614322371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353604571/10000000000 : ℝ)^4277 ≤ (43977227466757/100000000000000 : ℝ)^3253 := by
    have hnat : (5353604571 : ℕ)^4277*100000000000000^3253 ≤ 43977227466757^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353604571 10000000000 43977227466757 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083480311/5000000000 : ℝ)^4277 ≤ (6695083372539/50000000000000 : ℝ)^3253 := by
    have hnat : (1083480311 : ℕ)^4277*50000000000000^3253 ≤ 6695083372539^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083480311 5000000000 6695083372539 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614322371/5000000000 : ℝ)^4277 ≤ (42632605773099/100000000000000 : ℝ)^3253 := by
    have hnat : (2614322371 : ℕ)^4277*100000000000000^3253 ≤ 42632605773099^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614322371 5000000000 42632605773099 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353604571/10000000000 : ℝ), (-1083480311/5000000000 : ℝ), (2614322371/5000000000 : ℝ)] ![(43977227466757/100000000000000 : ℝ), (6695083372539/50000000000000 : ℝ), (42632605773099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353604571/10000000000 : ℝ)|^4277 ≤ (43977227466757/100000000000000 : ℝ)^3253
        have hw : |(5353604571/10000000000 : ℝ)|=(5353604571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1083480311/5000000000 : ℝ)|^4277 ≤ (6695083372539/50000000000000 : ℝ)^3253
        have hw : |(-1083480311/5000000000 : ℝ)|=(1083480311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614322371/5000000000 : ℝ)|^4277 ≤ (42632605773099/100000000000000 : ℝ)^3253
        have hw : |(2614322371/5000000000 : ℝ)|=(2614322371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s3_2 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353604757/10000000000 : ℝ)*x 0 + (5228644211/10000000000 : ℝ)*x 1 + (-86678443/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353604757/10000000000 : ℝ)^4277 ≤ (21988614737809/50000000000000 : ℝ)^3253 := by
    have hnat : (5353604757 : ℕ)^4277*50000000000000^3253 ≤ 21988614737809^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353604757 10000000000 21988614737809 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228644211/10000000000 : ℝ)^4277 ≤ (42632600080607/100000000000000 : ℝ)^3253 := by
    have hnat : (5228644211 : ℕ)^4277*100000000000000^3253 ≤ 42632600080607^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228644211 10000000000 42632600080607 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86678443/400000000 : ℝ)^4277 ≤ (6695085212711/50000000000000 : ℝ)^3253 := by
    have hnat : (86678443 : ℕ)^4277*50000000000000^3253 ≤ 6695085212711^3253*400000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86678443 400000000 6695085212711 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353604757/10000000000 : ℝ), (5228644211/10000000000 : ℝ), (-86678443/400000000 : ℝ)] ![(21988614737809/50000000000000 : ℝ), (42632600080607/100000000000000 : ℝ), (6695085212711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353604757/10000000000 : ℝ)|^4277 ≤ (21988614737809/50000000000000 : ℝ)^3253
        have hw : |(5353604757/10000000000 : ℝ)|=(5353604757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228644211/10000000000 : ℝ)|^4277 ≤ (42632600080607/100000000000000 : ℝ)^3253
        have hw : |(5228644211/10000000000 : ℝ)|=(5228644211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86678443/400000000 : ℝ)|^4277 ≤ (6695085212711/50000000000000 : ℝ)^3253
        have hw : |(-86678443/400000000 : ℝ)|=(86678443/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s3_3 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2165985239/5000000000 : ℝ)*x 0 + (4127341909/10000000000 : ℝ)*x 1 + (909231903/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165985239/5000000000 : ℝ)^4277 ≤ (16645200973937/50000000000000 : ℝ)^3253 := by
    have hnat : (2165985239 : ℕ)^4277*50000000000000^3253 ≤ 16645200973937^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165985239 5000000000 16645200973937 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4127341909/10000000000 : ℝ)^4277 ≤ (976199928497/3125000000000 : ℝ)^3253 := by
    have hnat : (4127341909 : ℕ)^4277*3125000000000^3253 ≤ 976199928497^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127341909 10000000000 976199928497 3125000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (909231903/2000000000 : ℝ)^4277 ≤ (35471200330257/100000000000000 : ℝ)^3253 := by
    have hnat : (909231903 : ℕ)^4277*100000000000000^3253 ≤ 35471200330257^3253*2000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909231903 2000000000 35471200330257 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165985239/5000000000 : ℝ), (4127341909/10000000000 : ℝ), (909231903/2000000000 : ℝ)] ![(16645200973937/50000000000000 : ℝ), (976199928497/3125000000000 : ℝ), (35471200330257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165985239/5000000000 : ℝ)|^4277 ≤ (16645200973937/50000000000000 : ℝ)^3253
        have hw : |(2165985239/5000000000 : ℝ)|=(2165985239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4127341909/10000000000 : ℝ)|^4277 ≤ (976199928497/3125000000000 : ℝ)^3253
        have hw : |(4127341909/10000000000 : ℝ)|=(4127341909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(909231903/2000000000 : ℝ)|^4277 ≤ (35471200330257/100000000000000 : ℝ)^3253
        have hw : |(909231903/2000000000 : ℝ)|=(909231903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s3_4 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1031876083/5000000000 : ℝ)*x 0 + (5229499007/10000000000 : ℝ)*x 1 + (5429635743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031876083/5000000000 : ℝ)^4277 ≤ (12558017690897/100000000000000 : ℝ)^3253 := by
    have hnat : (1031876083 : ℕ)^4277*100000000000000^3253 ≤ 12558017690897^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031876083 5000000000 12558017690897 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229499007/10000000000 : ℝ)^4277 ≤ (21320882003287/50000000000000 : ℝ)^3253 := by
    have hnat : (5229499007 : ℕ)^4277*50000000000000^3253 ≤ 21320882003287^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229499007 10000000000 21320882003287 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429635743/10000000000 : ℝ)^4277 ≤ (44800218284167/100000000000000 : ℝ)^3253 := by
    have hnat : (5429635743 : ℕ)^4277*100000000000000^3253 ≤ 44800218284167^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429635743 10000000000 44800218284167 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1031876083/5000000000 : ℝ), (5229499007/10000000000 : ℝ), (5429635743/10000000000 : ℝ)] ![(12558017690897/100000000000000 : ℝ), (21320882003287/50000000000000 : ℝ), (44800218284167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1031876083/5000000000 : ℝ)|^4277 ≤ (12558017690897/100000000000000 : ℝ)^3253
        have hw : |(-1031876083/5000000000 : ℝ)|=(1031876083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229499007/10000000000 : ℝ)|^4277 ≤ (21320882003287/50000000000000 : ℝ)^3253
        have hw : |(5229499007/10000000000 : ℝ)|=(5229499007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429635743/10000000000 : ℝ)|^4277 ≤ (44800218284167/100000000000000 : ℝ)^3253
        have hw : |(5429635743/10000000000 : ℝ)|=(5429635743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s3_5 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301763057/10000000000 : ℝ)*x 0 + (-1965969683/10000000000 : ℝ)*x 1 + (5429635703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301763057/10000000000 : ℝ)^4277 ≤ (43418177626223/100000000000000 : ℝ)^3253 := by
    have hnat : (5301763057 : ℕ)^4277*100000000000000^3253 ≤ 43418177626223^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301763057 10000000000 43418177626223 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1965969683/10000000000 : ℝ)^4277 ≤ (11781604509801/100000000000000 : ℝ)^3253 := by
    have hnat : (1965969683 : ℕ)^4277*100000000000000^3253 ≤ 11781604509801^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965969683 10000000000 11781604509801 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429635703/10000000000 : ℝ)^4277 ≤ (5600027231279/12500000000000 : ℝ)^3253 := by
    have hnat : (5429635703 : ℕ)^4277*12500000000000^3253 ≤ 5600027231279^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429635703 10000000000 5600027231279 12500000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301763057/10000000000 : ℝ), (-1965969683/10000000000 : ℝ), (5429635703/10000000000 : ℝ)] ![(43418177626223/100000000000000 : ℝ), (11781604509801/100000000000000 : ℝ), (5600027231279/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301763057/10000000000 : ℝ)|^4277 ≤ (43418177626223/100000000000000 : ℝ)^3253
        have hw : |(5301763057/10000000000 : ℝ)|=(5301763057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1965969683/10000000000 : ℝ)|^4277 ≤ (11781604509801/100000000000000 : ℝ)^3253
        have hw : |(-1965969683/10000000000 : ℝ)|=(1965969683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429635703/10000000000 : ℝ)|^4277 ≤ (5600027231279/12500000000000 : ℝ)^3253
        have hw : |(5429635703/10000000000 : ℝ)|=(5429635703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s3_6 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1656801/3125000 : ℝ)*x 0 + (678704447/1250000000 : ℝ)*x 1 + (-982984831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1656801/3125000 : ℝ)^4277 ≤ (21709089582973/50000000000000 : ℝ)^3253 := by
    have hnat : (1656801 : ℕ)^4277*50000000000000^3253 ≤ 21709089582973^3253*3125000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1656801 3125000 21709089582973 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678704447/1250000000 : ℝ)^4277 ≤ (5600027059061/12500000000000 : ℝ)^3253 := by
    have hnat : (678704447 : ℕ)^4277*12500000000000^3253 ≤ 5600027059061^3253*1250000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678704447 1250000000 5600027059061 12500000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (982984831/5000000000 : ℝ)^4277 ≤ (5890802172169/50000000000000 : ℝ)^3253 := by
    have hnat : (982984831 : ℕ)^4277*50000000000000^3253 ≤ 5890802172169^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982984831 5000000000 5890802172169 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1656801/3125000 : ℝ), (678704447/1250000000 : ℝ), (-982984831/5000000000 : ℝ)] ![(21709089582973/50000000000000 : ℝ), (5600027059061/12500000000000 : ℝ), (5890802172169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1656801/3125000 : ℝ)|^4277 ≤ (21709089582973/50000000000000 : ℝ)^3253
        have hw : |(1656801/3125000 : ℝ)|=(1656801/3125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678704447/1250000000 : ℝ)|^4277 ≤ (5600027059061/12500000000000 : ℝ)^3253
        have hw : |(678704447/1250000000 : ℝ)|=(678704447/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-982984831/5000000000 : ℝ)|^4277 ≤ (5890802172169/50000000000000 : ℝ)^3253
        have hw : |(-982984831/5000000000 : ℝ)|=(982984831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s3_7 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2166006633/5000000000 : ℝ)*x 0 + (4544386849/10000000000 : ℝ)*x 1 + (516140707/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166006633/5000000000 : ℝ)^4277 ≤ (33290834273919/100000000000000 : ℝ)^3253 := by
    have hnat : (2166006633 : ℕ)^4277*100000000000000^3253 ≤ 33290834273919^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166006633 5000000000 33290834273919 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4544386849/10000000000 : ℝ)^4277 ≤ (221581352787/625000000000 : ℝ)^3253 := by
    have hnat : (4544386849 : ℕ)^4277*625000000000^3253 ≤ 221581352787^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4544386849 10000000000 221581352787 625000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516140707/1250000000 : ℝ)^4277 ≤ (31256149262017/100000000000000 : ℝ)^3253 := by
    have hnat : (516140707 : ℕ)^4277*100000000000000^3253 ≤ 31256149262017^3253*1250000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516140707 1250000000 31256149262017 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166006633/5000000000 : ℝ), (4544386849/10000000000 : ℝ), (516140707/1250000000 : ℝ)] ![(33290834273919/100000000000000 : ℝ), (221581352787/625000000000 : ℝ), (31256149262017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166006633/5000000000 : ℝ)|^4277 ≤ (33290834273919/100000000000000 : ℝ)^3253
        have hw : |(2166006633/5000000000 : ℝ)|=(2166006633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4544386849/10000000000 : ℝ)|^4277 ≤ (221581352787/625000000000 : ℝ)^3253
        have hw : |(4544386849/10000000000 : ℝ)|=(4544386849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516140707/1250000000 : ℝ)|^4277 ≤ (31256149262017/100000000000000 : ℝ)^3253
        have hw : |(516140707/1250000000 : ℝ)|=(516140707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1317_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16207/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9683/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2153/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3759/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16207/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9683/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16207/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9683/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16207/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9683/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16207/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9683/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16207/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9683/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16207/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9683/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9683/100000 : ℝ) ^ (1069/256 : ℝ) ≤ (5831755206233803/100000000000000000000 : ℝ) := by
    have hpowers : (9683/100000 : ℝ)^1069 ≤ (5831755206233803/100000000000000000000 : ℝ)^256 := by
      have hnat : (9683 : ℕ)^1069*100000000000000000000^256 ≤ 5831755206233803^256*100000^1069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9683 100000 5831755206233803 100000000000000000000 1069 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9683/100000 : ℝ)) (X := (5831755206233803/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hpowhi : (16207/100000 : ℝ) ^ (1069/256 : ℝ) ≤ (25053077024250877/50000000000000000000 : ℝ) := by
    have hpowers : (16207/100000 : ℝ)^1069 ≤ (25053077024250877/50000000000000000000 : ℝ)^256 := by
      have hnat : (16207 : ℕ)^1069*50000000000000000000^256 ≤ 25053077024250877^256*100000^1069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16207 100000 25053077024250877 50000000000000000000 1069 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16207/100000 : ℝ)) (X := (25053077024250877/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005831755206233803/50000000000000000000 : ℝ) ≤ (5000139650432469/5000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (50005831755206233803/50000000000000000000 : ℝ)^256 ≤ (5000139650432469/5000000000000000 : ℝ)^1069 := by
      have hnat : (50005831755206233803 : ℕ)^256*5000000000000000^1069 ≤ 5000139650432469^1069*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005831755206233803 50000000000000000000 5000139650432469 5000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000139650432469/5000000000000000 : ℝ)) (X := (50005831755206233803/50000000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100055937909254735557/100000000000000000000 : ℝ) ≤ (10001339294642757/10000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (100055937909254735557/100000000000000000000 : ℝ)^256 ≤ (10001339294642757/10000000000000000 : ℝ)^1069 := by
      have hnat : (100055937909254735557 : ℕ)^256*10000000000000000^1069 ≤ 10001339294642757^1069*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100055937909254735557 100000000000000000000 10001339294642757 10000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001339294642757/10000000000000000 : ℝ)) (X := (100055937909254735557/100000000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25025053077024250877/25000000000000000000 : ℝ) ≤ (312574977763143/312500000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (25025053077024250877/25000000000000000000 : ℝ)^256 ≤ (312574977763143/312500000000000 : ℝ)^1069 := by
      have hnat : (25025053077024250877 : ℕ)^256*312500000000000^1069 ≤ 312574977763143^1069*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25025053077024250877 25000000000000000000 312574977763143 312500000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312574977763143/312500000000000 : ℝ)) (X := (25025053077024250877/25000000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5831755206233803/100000000000000000000 : ℝ) ≤ ((32610647159670806379/32620000000000000000 : ℝ)+2*(1059993777819/652400000000000 : ℝ)*(9683/100000 : ℝ))^(1069/256 : ℝ) := by
    rw [show (32610647159670806379/32620000000000000000 : ℝ)+2*(1059993777819/652400000000000 : ℝ)*(9683/100000 : ℝ)=(5000139650432469/5000000000000000 : ℝ) by norm_num, show 1+2*(5831755206233803/100000000000000000000 : ℝ)=(50005831755206233803/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25053077024250877/50000000000000000000 : ℝ)+(5831755206233803/100000000000000000000 : ℝ) ≤ ((32610647159670806379/32620000000000000000 : ℝ)+(1059993777819/652400000000000 : ℝ)*((16207/100000 : ℝ)+(9683/100000 : ℝ)))^(1069/256 : ℝ) := by
    rw [show (32610647159670806379/32620000000000000000 : ℝ)+(1059993777819/652400000000000 : ℝ)*((16207/100000 : ℝ)+(9683/100000 : ℝ))=(10001339294642757/10000000000000000 : ℝ) by norm_num, show 1+(25053077024250877/50000000000000000000 : ℝ)+(5831755206233803/100000000000000000000 : ℝ)=(100055937909254735557/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25053077024250877/50000000000000000000 : ℝ) ≤ ((32610647159670806379/32620000000000000000 : ℝ)+2*(1059993777819/652400000000000 : ℝ)*(16207/100000 : ℝ))^(1069/256 : ℝ) := by
    rw [show (32610647159670806379/32620000000000000000 : ℝ)+2*(1059993777819/652400000000000 : ℝ)*(16207/100000 : ℝ)=(312574977763143/312500000000000 : ℝ) by norm_num, show 1+2*(25053077024250877/50000000000000000000 : ℝ)=(25025053077024250877/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32610647159670806379/32620000000000000000 : ℝ)*(X 1 0+X 2 0)+(1059993777819/652400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (9683/100000 : ℝ)) (hi := (16207/100000 : ℝ)) (c := (32610647159670806379/32620000000000000000 : ℝ)) (alpha := (1059993777819/652400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32610647159670806379/32620000000000000000 : ℝ)*(X 0 1+X 2 1)+(1059993777819/652400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (9683/100000 : ℝ)) (hi := (16207/100000 : ℝ)) (c := (32610647159670806379/32620000000000000000 : ℝ)) (alpha := (1059993777819/652400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32610647159670806379/32620000000000000000 : ℝ)*(X 0 2+X 1 2)+(1059993777819/652400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (9683/100000 : ℝ)) (hi := (16207/100000 : ℝ)) (c := (32610647159670806379/32620000000000000000 : ℝ)) (alpha := (1059993777819/652400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2063731333/10000000000 : ℝ)*X 0 0+(2715247617/5000000000 : ℝ)*X 0 1+(2614322399/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353604571/10000000000 : ℝ)*X 1 0+(-1083480311/5000000000 : ℝ)*X 1 1+(2614322371/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353604757/10000000000 : ℝ)*X 2 0+(5228644211/10000000000 : ℝ)*X 2 1+(-86678443/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2165985239/5000000000 : ℝ)*X 0 0+(4127341909/10000000000 : ℝ)*X 0 1+(909231903/2000000000 : ℝ)*X 0 2+(2165985239/5000000000 : ℝ)*X 1 0+(4127341909/10000000000 : ℝ)*X 1 1+(909231903/2000000000 : ℝ)*X 1 2+(2165985239/5000000000 : ℝ)*X 2 0+(4127341909/10000000000 : ℝ)*X 2 1+(909231903/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1031876083/5000000000 : ℝ)*X 0 0+(5229499007/10000000000 : ℝ)*X 0 1+(5429635743/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301763057/10000000000 : ℝ)*X 1 0+(-1965969683/10000000000 : ℝ)*X 1 1+(5429635703/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1656801/3125000 : ℝ)*X 2 0+(678704447/1250000000 : ℝ)*X 2 1+(-982984831/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2166006633/5000000000 : ℝ)*X 0 0+(4544386849/10000000000 : ℝ)*X 0 1+(516140707/1250000000 : ℝ)*X 0 2+(2166006633/5000000000 : ℝ)*X 1 0+(4544386849/10000000000 : ℝ)*X 1 1+(516140707/1250000000 : ℝ)*X 1 2+(2166006633/5000000000 : ℝ)*X 2 0+(4544386849/10000000000 : ℝ)*X 2 1+(516140707/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (29766440754933476940691833/6371093750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1071456391/100000000000000 : ℝ)*(base19) + (1461902367/100000000000000 : ℝ)*(base23) + (48587/4000000000000 : ℝ)*(lower2) + (271987397/100000000000000 : ℝ)*(upper3) + (59048017/50000000000000 : ℝ)*(lower4) + (114716979261139/3125000000000 : ℝ)*(major0) + (114716979261139/3125000000000 : ℝ)*(major1) + (114716979261139/3125000000000 : ℝ)*(major2) + (990836659035873/20000000000000 : ℝ)*(sp0) + (4954192746536701/100000000000000 : ℝ)*(sp1) + (2477096178045363/50000000000000 : ℝ)*(sp2) + (298460229324077/12500000000000 : ℝ)*(sp3) + (10522813727/100000000000000 : ℝ)*(sp4) + (10864390233/100000000000000 : ℝ)*(sp7) + (47753853979657/2000000000000 : ℝ)*(f.failure) + (1238548454498273/25000000000000 : ℝ)*(f.sum) + (14774727341117/8155000000000000000000000000 : ℝ)*base66 + (368944285098805681/101937500000000000000000000000000 : ℝ)*base67 + (216851134493181/101937500000000000000000000000000 : ℝ)*base69 + (447866699552118181/101937500000000000000000000000000 : ℝ)*base71 + (16590164825183/8155000000000000000000000000 : ℝ)*base73 + (1421303205031930681/101937500000000000000000000000000 : ℝ)*base75 + (749320257962944319/101937500000000000000000000000000 : ℝ)*base78 + (155836633755243181/101937500000000000000000000000000 : ℝ)*base79 + (6300601618081/4077500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (103883/10000000000000000000 : ℝ)*base89 + (103883/10000000000000000000 : ℝ)*base91 + (103883/10000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1137197529333813225422503041/116500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (417020413/20000000000000 : ℝ)*(base19) + (2338142517/100000000000000 : ℝ)*(base23) + (28445863/12500000000000 : ℝ)*(upper3) + (6191753/12500000000000 : ℝ)*(lower4) + (117068673/50000000000000 : ℝ)*(upper5) + (1851176880906951/50000000000000 : ℝ)*(major0) + (1851176880906951/50000000000000 : ℝ)*(major1) + (1851176880906951/50000000000000 : ℝ)*(major2) + (35096820199/100000000000000 : ℝ)*(sp1) + (2352337437/6250000000000 : ℝ)*(sp2) + (2498292103734133/50000000000000 : ℝ)*(sp4) + (2498273512773001/50000000000000 : ℝ)*(sp5) + (4996544231926757/100000000000000 : ℝ)*(sp6) + (301015373847641/12500000000000 : ℝ)*(sp7) + (301015373847641/12500000000000 : ℝ)*(f.failure) + (2498292103734133/50000000000000 : ℝ)*(f.sum) + (9998577681349/16310000000000000000000000000 : ℝ)*base65 + (8186668473075690429/1631000000000000000000000000000000 : ℝ)*base67 + (2342177118356309571/1631000000000000000000000000000000 : ℝ)*base70 + (10975663890091309571/1631000000000000000000000000000000 : ℝ)*base72 + (69451061668189/16310000000000000000000000000 : ℝ)*base73 + (11046859064162309571/1631000000000000000000000000000000 : ℝ)*base76 + (5180671309322309571/1631000000000000000000000000000000 : ℝ)*base78 + (4238783256933690429/1631000000000000000000000000000000 : ℝ)*base79 + (70925275171329/16310000000000000000000000000 : ℝ)*base81 + (250379/62500000000000000000 : ℝ)*base89 + (250379/62500000000000000000 : ℝ)*base91 + (250379/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1317_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16207/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9683/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2153/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3759/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1317_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1317_s4_0 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-413081139/2000000000 : ℝ)*x 0 + (5417054961/10000000000 : ℝ)*x 1 + (2620493339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (413081139/2000000000 : ℝ)^4277 ≤ (19642575729/156250000000 : ℝ)^3253 := by
    have hnat : (413081139 : ℕ)^4277*156250000000^3253 ≤ 19642575729^3253*2000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413081139 2000000000 19642575729 156250000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417054961/10000000000 : ℝ)^4277 ≤ (44663787063903/100000000000000 : ℝ)^3253 := by
    have hnat : (5417054961 : ℕ)^4277*100000000000000^3253 ≤ 44663787063903^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417054961 10000000000 44663787063903 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620493339/5000000000 : ℝ)^4277 ≤ (8552992892111/20000000000000 : ℝ)^3253 := by
    have hnat : (2620493339 : ℕ)^4277*20000000000000^3253 ≤ 8552992892111^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620493339 5000000000 8552992892111 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-413081139/2000000000 : ℝ), (5417054961/10000000000 : ℝ), (2620493339/5000000000 : ℝ)] ![(19642575729/156250000000 : ℝ), (44663787063903/100000000000000 : ℝ), (8552992892111/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-413081139/2000000000 : ℝ)|^4277 ≤ (19642575729/156250000000 : ℝ)^3253
        have hw : |(-413081139/2000000000 : ℝ)|=(413081139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417054961/10000000000 : ℝ)|^4277 ≤ (44663787063903/100000000000000 : ℝ)^3253
        have hw : |(5417054961/10000000000 : ℝ)|=(5417054961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620493339/5000000000 : ℝ)|^4277 ≤ (8552992892111/20000000000000 : ℝ)^3253
        have hw : |(2620493339/5000000000 : ℝ)|=(2620493339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s4_1 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070038743/2000000000 : ℝ)*x 0 + (-2155193219/10000000000 : ℝ)*x 1 + (1310246599/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070038743/2000000000 : ℝ)^4277 ≤ (43940392814937/100000000000000 : ℝ)^3253 := by
    have hnat : (1070038743 : ℕ)^4277*100000000000000^3253 ≤ 43940392814937^3253*2000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070038743 2000000000 43940392814937 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2155193219/10000000000 : ℝ)^4277 ≤ (13294645721793/100000000000000 : ℝ)^3253 := by
    have hnat : (2155193219 : ℕ)^4277*100000000000000^3253 ≤ 13294645721793^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155193219 10000000000 13294645721793 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310246599/2500000000 : ℝ)^4277 ≤ (42764961435179/100000000000000 : ℝ)^3253 := by
    have hnat : (1310246599 : ℕ)^4277*100000000000000^3253 ≤ 42764961435179^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310246599 2500000000 42764961435179 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070038743/2000000000 : ℝ), (-2155193219/10000000000 : ℝ), (1310246599/2500000000 : ℝ)] ![(43940392814937/100000000000000 : ℝ), (13294645721793/100000000000000 : ℝ), (42764961435179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070038743/2000000000 : ℝ)|^4277 ≤ (43940392814937/100000000000000 : ℝ)^3253
        have hw : |(1070038743/2000000000 : ℝ)|=(1070038743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2155193219/10000000000 : ℝ)|^4277 ≤ (13294645721793/100000000000000 : ℝ)^3253
        have hw : |(-2155193219/10000000000 : ℝ)|=(2155193219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310246599/2500000000 : ℝ)|^4277 ≤ (42764961435179/100000000000000 : ℝ)^3253
        have hw : |(1310246599/2500000000 : ℝ)|=(1310246599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s4_2 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350193601/10000000000 : ℝ)*x 0 + (5240986047/10000000000 : ℝ)*x 1 + (-1077596917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350193601/10000000000 : ℝ)^4277 ≤ (10985097895987/25000000000000 : ℝ)^3253 := by
    have hnat : (5350193601 : ℕ)^4277*25000000000000^3253 ≤ 10985097895987^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350193601 10000000000 10985097895987 25000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240986047/10000000000 : ℝ)^4277 ≤ (334101231961/781250000000 : ℝ)^3253 := by
    have hnat : (5240986047 : ℕ)^4277*781250000000^3253 ≤ 334101231961^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240986047 10000000000 334101231961 781250000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077596917/5000000000 : ℝ)^4277 ≤ (13294650709729/100000000000000 : ℝ)^3253 := by
    have hnat : (1077596917 : ℕ)^4277*100000000000000^3253 ≤ 13294650709729^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077596917 5000000000 13294650709729 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350193601/10000000000 : ℝ), (5240986047/10000000000 : ℝ), (-1077596917/5000000000 : ℝ)] ![(10985097895987/25000000000000 : ℝ), (334101231961/781250000000 : ℝ), (13294650709729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350193601/10000000000 : ℝ)|^4277 ≤ (10985097895987/25000000000000 : ℝ)^3253
        have hw : |(5350193601/10000000000 : ℝ)|=(5350193601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240986047/10000000000 : ℝ)|^4277 ≤ (334101231961/781250000000 : ℝ)^3253
        have hw : |(5240986047/10000000000 : ℝ)|=(5240986047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1077596917/5000000000 : ℝ)|^4277 ≤ (13294650709729/100000000000000 : ℝ)^3253
        have hw : |(-1077596917/5000000000 : ℝ)|=(1077596917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s4_3 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2166492727/5000000000 : ℝ)*x 0 + (4153962553/10000000000 : ℝ)*x 1 + (4519285653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166492727/5000000000 : ℝ)^4277 ≤ (33300657534917/100000000000000 : ℝ)^3253 := by
    have hnat : (2166492727 : ℕ)^4277*100000000000000^3253 ≤ 33300657534917^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166492727 5000000000 33300657534917 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4153962553/10000000000 : ℝ)^4277 ≤ (15751786196209/50000000000000 : ℝ)^3253 := by
    have hnat : (4153962553 : ℕ)^4277*50000000000000^3253 ≤ 15751786196209^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153962553 10000000000 15751786196209 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4519285653/10000000000 : ℝ)^4277 ≤ (35195770052551/100000000000000 : ℝ)^3253 := by
    have hnat : (4519285653 : ℕ)^4277*100000000000000^3253 ≤ 35195770052551^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4519285653 10000000000 35195770052551 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166492727/5000000000 : ℝ), (4153962553/10000000000 : ℝ), (4519285653/10000000000 : ℝ)] ![(33300657534917/100000000000000 : ℝ), (15751786196209/50000000000000 : ℝ), (35195770052551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166492727/5000000000 : ℝ)|^4277 ≤ (33300657534917/100000000000000 : ℝ)^3253
        have hw : |(2166492727/5000000000 : ℝ)|=(2166492727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4153962553/10000000000 : ℝ)|^4277 ≤ (15751786196209/50000000000000 : ℝ)^3253
        have hw : |(4153962553/10000000000 : ℝ)|=(4153962553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4519285653/10000000000 : ℝ)|^4277 ≤ (35195770052551/100000000000000 : ℝ)^3253
        have hw : |(4519285653/10000000000 : ℝ)|=(4519285653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s4_4 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-51635487/250000000 : ℝ)*x 0 + (2620818571/5000000000 : ℝ)*x 1 + (2708200513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51635487/250000000 : ℝ)^4277 ≤ (1571419847723/12500000000000 : ℝ)^3253 := by
    have hnat : (51635487 : ℕ)^4277*12500000000000^3253 ≤ 1571419847723^3253*250000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51635487 250000000 1571419847723 12500000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620818571/5000000000 : ℝ)^4277 ≤ (855438859183/2000000000000 : ℝ)^3253 := by
    have hnat : (2620818571 : ℕ)^4277*2000000000000^3253 ≤ 855438859183^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620818571 5000000000 855438859183 2000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708200513/5000000000 : ℝ)^4277 ≤ (4465669824601/10000000000000 : ℝ)^3253 := by
    have hnat : (2708200513 : ℕ)^4277*10000000000000^3253 ≤ 4465669824601^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708200513 5000000000 4465669824601 10000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51635487/250000000 : ℝ), (2620818571/5000000000 : ℝ), (2708200513/5000000000 : ℝ)] ![(1571419847723/12500000000000 : ℝ), (855438859183/2000000000000 : ℝ), (4465669824601/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51635487/250000000 : ℝ)|^4277 ≤ (1571419847723/12500000000000 : ℝ)^3253
        have hw : |(-51635487/250000000 : ℝ)|=(51635487/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620818571/5000000000 : ℝ)|^4277 ≤ (855438859183/2000000000000 : ℝ)^3253
        have hw : |(2620818571/5000000000 : ℝ)|=(2620818571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708200513/5000000000 : ℝ)|^4277 ≤ (4465669824601/10000000000000 : ℝ)^3253
        have hw : |(2708200513/5000000000 : ℝ)|=(2708200513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s4_5 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304975483/10000000000 : ℝ)*x 0 + (-494944769/2500000000 : ℝ)*x 1 + (5416401021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304975483/10000000000 : ℝ)^4277 ≤ (43452770051011/100000000000000 : ℝ)^3253 := by
    have hnat : (5304975483 : ℕ)^4277*100000000000000^3253 ≤ 43452770051011^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304975483 10000000000 43452770051011 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (494944769/2500000000 : ℝ)^4277 ≤ (1189053175183/10000000000000 : ℝ)^3253 := by
    have hnat : (494944769 : ℕ)^4277*10000000000000^3253 ≤ 1189053175183^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494944769 2500000000 1189053175183 10000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416401021/10000000000 : ℝ)^4277 ≤ (4465669819181/10000000000000 : ℝ)^3253 := by
    have hnat : (5416401021 : ℕ)^4277*10000000000000^3253 ≤ 4465669819181^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416401021 10000000000 4465669819181 10000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304975483/10000000000 : ℝ), (-494944769/2500000000 : ℝ), (5416401021/10000000000 : ℝ)] ![(43452770051011/100000000000000 : ℝ), (1189053175183/10000000000000 : ℝ), (4465669819181/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304975483/10000000000 : ℝ)|^4277 ≤ (43452770051011/100000000000000 : ℝ)^3253
        have hw : |(5304975483/10000000000 : ℝ)|=(5304975483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-494944769/2500000000 : ℝ)|^4277 ≤ (1189053175183/10000000000000 : ℝ)^3253
        have hw : |(-494944769/2500000000 : ℝ)|=(494944769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416401021/10000000000 : ℝ)|^4277 ≤ (4465669819181/10000000000000 : ℝ)^3253
        have hw : |(5416401021/10000000000 : ℝ)|=(5416401021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s4_6 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41445121/78125000 : ℝ)*x 0 + (2708200507/5000000000 : ℝ)*x 1 + (-989889539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41445121/78125000 : ℝ)^4277 ≤ (43452770104857/100000000000000 : ℝ)^3253 := by
    have hnat : (41445121 : ℕ)^4277*100000000000000^3253 ≤ 43452770104857^3253*78125000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41445121 78125000 43452770104857 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708200507/5000000000 : ℝ)^4277 ≤ (4465669811593/10000000000000 : ℝ)^3253 := by
    have hnat : (2708200507 : ℕ)^4277*10000000000000^3253 ≤ 4465669811593^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708200507 5000000000 4465669811593 10000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (989889539/5000000000 : ℝ)^4277 ≤ (11890531767623/100000000000000 : ℝ)^3253 := by
    have hnat : (989889539 : ℕ)^4277*100000000000000^3253 ≤ 11890531767623^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989889539 5000000000 11890531767623 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41445121/78125000 : ℝ), (2708200507/5000000000 : ℝ), (-989889539/5000000000 : ℝ)] ![(43452770104857/100000000000000 : ℝ), (4465669811593/10000000000000 : ℝ), (11890531767623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41445121/78125000 : ℝ)|^4277 ≤ (43452770104857/100000000000000 : ℝ)^3253
        have hw : |(41445121/78125000 : ℝ)|=(41445121/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708200507/5000000000 : ℝ)|^4277 ≤ (4465669811593/10000000000000 : ℝ)^3253
        have hw : |(2708200507/5000000000 : ℝ)|=(2708200507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-989889539/5000000000 : ℝ)|^4277 ≤ (11890531767623/100000000000000 : ℝ)^3253
        have hw : |(-989889539/5000000000 : ℝ)|=(989889539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s4_7 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083253541/2500000000 : ℝ)*x 0 + (4517935343/10000000000 : ℝ)*x 1 + (4155319943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083253541/2500000000 : ℝ)^4277 ≤ (1665047381969/5000000000000 : ℝ)^3253 := by
    have hnat : (1083253541 : ℕ)^4277*5000000000000^3253 ≤ 1665047381969^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083253541 2500000000 1665047381969 5000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4517935343/10000000000 : ℝ)^4277 ≤ (7036388859081/20000000000000 : ℝ)^3253 := by
    have hnat : (4517935343 : ℕ)^4277*20000000000000^3253 ≤ 7036388859081^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517935343 10000000000 7036388859081 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4155319943/10000000000 : ℝ)^4277 ≤ (15758554025531/50000000000000 : ℝ)^3253 := by
    have hnat : (4155319943 : ℕ)^4277*50000000000000^3253 ≤ 15758554025531^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155319943 10000000000 15758554025531 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083253541/2500000000 : ℝ), (4517935343/10000000000 : ℝ), (4155319943/10000000000 : ℝ)] ![(1665047381969/5000000000000 : ℝ), (7036388859081/20000000000000 : ℝ), (15758554025531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083253541/2500000000 : ℝ)|^4277 ≤ (1665047381969/5000000000000 : ℝ)^3253
        have hw : |(1083253541/2500000000 : ℝ)|=(1083253541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4517935343/10000000000 : ℝ)|^4277 ≤ (7036388859081/20000000000000 : ℝ)^3253
        have hw : |(4517935343/10000000000 : ℝ)|=(4517935343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4155319943/10000000000 : ℝ)|^4277 ≤ (15758554025531/50000000000000 : ℝ)^3253
        have hw : |(4155319943/10000000000 : ℝ)|=(4155319943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1317_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3759/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2153/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2757/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2951/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3759/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2153/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3759/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2153/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3759/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2153/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3759/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2153/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3759/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2153/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3759/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2153/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2153/20000 : ℝ) ^ (1069/256 : ℝ) ≤ (9076164394894511/100000000000000000000 : ℝ) := by
    have hpowers : (2153/20000 : ℝ)^1069 ≤ (9076164394894511/100000000000000000000 : ℝ)^256 := by
      have hnat : (2153 : ℕ)^1069*100000000000000000000^256 ≤ 9076164394894511^256*20000^1069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2153 20000 9076164394894511 100000000000000000000 1069 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2153/20000 : ℝ)) (X := (9076164394894511/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3759/25000 : ℝ) ^ (1069/256 : ℝ) ≤ (57240653626209/156250000000000000 : ℝ) := by
    have hpowers : (3759/25000 : ℝ)^1069 ≤ (57240653626209/156250000000000000 : ℝ)^256 := by
      have hnat : (3759 : ℕ)^1069*156250000000000000^256 ≤ 57240653626209^256*25000^1069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3759 25000 57240653626209 156250000000000000 1069 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3759/25000 : ℝ)) (X := (57240653626209/156250000000000000 : ℝ)) (by norm_num) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009076164394894511/50000000000000000000 : ℝ) ≤ (1250054334371363/1250000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (50009076164394894511/50000000000000000000 : ℝ)^256 ≤ (1250054334371363/1250000000000000 : ℝ)^1069 := by
      have hnat : (50009076164394894511 : ℕ)^256*1250000000000000^1069 ≤ 1250054334371363^1069*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009076164394894511 50000000000000000000 1250054334371363 1250000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250054334371363/1250000000000000 : ℝ)) (X := (50009076164394894511/50000000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045710182715668271/100000000000000000000 : ℝ) ≤ (1000109445961937/1000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (100045710182715668271/100000000000000000000 : ℝ)^256 ≤ (1000109445961937/1000000000000000 : ℝ)^1069 := by
      have hnat : (100045710182715668271 : ℕ)^256*1000000000000000^1069 ≤ 1000109445961937^1069*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045710182715668271 100000000000000000000 1000109445961937 1000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000109445961937/1000000000000000 : ℝ)) (X := (100045710182715668271/100000000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (78182240653626209/78125000000000000 : ℝ) ≤ (2500438561066959/2500000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (78182240653626209/78125000000000000 : ℝ)^256 ≤ (2500438561066959/2500000000000000 : ℝ)^1069 := by
      have hnat : (78182240653626209 : ℕ)^256*2500000000000000^1069 ≤ 2500438561066959^1069*78125000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78182240653626209 78125000000000000 2500438561066959 2500000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500438561066959/2500000000000000 : ℝ)) (X := (78182240653626209/78125000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9076164394894511/100000000000000000000 : ℝ) ≤ ((10674412833329814501/10677500000000000000 : ℝ)+2*(329892324233/213550000000000 : ℝ)*(2153/20000 : ℝ))^(1069/256 : ℝ) := by
    rw [show (10674412833329814501/10677500000000000000 : ℝ)+2*(329892324233/213550000000000 : ℝ)*(2153/20000 : ℝ)=(1250054334371363/1250000000000000 : ℝ) by norm_num, show 1+2*(9076164394894511/100000000000000000000 : ℝ)=(50009076164394894511/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(57240653626209/156250000000000000 : ℝ)+(9076164394894511/100000000000000000000 : ℝ) ≤ ((10674412833329814501/10677500000000000000 : ℝ)+(329892324233/213550000000000 : ℝ)*((3759/25000 : ℝ)+(2153/20000 : ℝ)))^(1069/256 : ℝ) := by
    rw [show (10674412833329814501/10677500000000000000 : ℝ)+(329892324233/213550000000000 : ℝ)*((3759/25000 : ℝ)+(2153/20000 : ℝ))=(1000109445961937/1000000000000000 : ℝ) by norm_num, show 1+(57240653626209/156250000000000000 : ℝ)+(9076164394894511/100000000000000000000 : ℝ)=(100045710182715668271/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(57240653626209/156250000000000000 : ℝ) ≤ ((10674412833329814501/10677500000000000000 : ℝ)+2*(329892324233/213550000000000 : ℝ)*(3759/25000 : ℝ))^(1069/256 : ℝ) := by
    rw [show (10674412833329814501/10677500000000000000 : ℝ)+2*(329892324233/213550000000000 : ℝ)*(3759/25000 : ℝ)=(2500438561066959/2500000000000000 : ℝ) by norm_num, show 1+2*(57240653626209/156250000000000000 : ℝ)=(78182240653626209/78125000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10674412833329814501/10677500000000000000 : ℝ)*(X 1 0+X 2 0)+(329892324233/213550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (2153/20000 : ℝ)) (hi := (3759/25000 : ℝ)) (c := (10674412833329814501/10677500000000000000 : ℝ)) (alpha := (329892324233/213550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10674412833329814501/10677500000000000000 : ℝ)*(X 0 1+X 2 1)+(329892324233/213550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (2153/20000 : ℝ)) (hi := (3759/25000 : ℝ)) (c := (10674412833329814501/10677500000000000000 : ℝ)) (alpha := (329892324233/213550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10674412833329814501/10677500000000000000 : ℝ)*(X 0 2+X 1 2)+(329892324233/213550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (2153/20000 : ℝ)) (hi := (3759/25000 : ℝ)) (c := (10674412833329814501/10677500000000000000 : ℝ)) (alpha := (329892324233/213550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-413081139/2000000000 : ℝ)*X 0 0+(5417054961/10000000000 : ℝ)*X 0 1+(2620493339/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070038743/2000000000 : ℝ)*X 1 0+(-2155193219/10000000000 : ℝ)*X 1 1+(1310246599/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350193601/10000000000 : ℝ)*X 2 0+(5240986047/10000000000 : ℝ)*X 2 1+(-1077596917/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2166492727/5000000000 : ℝ)*X 0 0+(4153962553/10000000000 : ℝ)*X 0 1+(4519285653/10000000000 : ℝ)*X 0 2+(2166492727/5000000000 : ℝ)*X 1 0+(4153962553/10000000000 : ℝ)*X 1 1+(4519285653/10000000000 : ℝ)*X 1 2+(2166492727/5000000000 : ℝ)*X 2 0+(4153962553/10000000000 : ℝ)*X 2 1+(4519285653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-51635487/250000000 : ℝ)*X 0 0+(2620818571/5000000000 : ℝ)*X 0 1+(2708200513/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304975483/10000000000 : ℝ)*X 1 0+(-494944769/2500000000 : ℝ)*X 1 1+(5416401021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41445121/78125000 : ℝ)*X 2 0+(2708200507/5000000000 : ℝ)*X 2 1+(-989889539/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1083253541/2500000000 : ℝ)*X 0 0+(4517935343/10000000000 : ℝ)*X 0 1+(4155319943/10000000000 : ℝ)*X 0 2+(1083253541/2500000000 : ℝ)*X 1 0+(4517935343/10000000000 : ℝ)*X 1 1+(4155319943/10000000000 : ℝ)*X 1 2+(1083253541/2500000000 : ℝ)*X 2 0+(4517935343/10000000000 : ℝ)*X 2 1+(4155319943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12999279642840198662522061/1334687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (510034771/20000000000000 : ℝ)*(base19) + (2415265149/100000000000000 : ℝ)*(base23) + (73688053/20000000000000 : ℝ)*(upper3) + (35304487/100000000000000 : ℝ)*(lower4) + (10521331615271/250000000000 : ℝ)*(major0) + (10521331615271/250000000000 : ℝ)*(major1) + (10521331615271/250000000000 : ℝ)*(major2) + (1135933770411367/20000000000000 : ℝ)*(sp0) + (5679705353601803/100000000000000 : ℝ)*(sp1) + (1135939207547431/20000000000000 : ℝ)*(sp2) + (342165970784977/12500000000000 : ℝ)*(sp3) + (19525859411/50000000000000 : ℝ)*(sp4) + (9450773353/100000000000000 : ℝ)*(sp6) + (7324377263/25000000000000 : ℝ)*(sp7) + (684339265947217/25000000000000 : ℝ)*(f.failure) + (5679707903775657/100000000000000 : ℝ)*(f.sum) + (6052811734883/4271000000000000000000000000 : ℝ)*base65 + (5500993965543323/1334687500000000000000000000000 : ℝ)*base67 + (19236451524991021/2669375000000000000000000000000 : ℝ)*base69 + (10071306707103849/667343750000000000000000000000 : ℝ)*base71 + (1990763077637/4271000000000000000000000000 : ℝ)*base74 + (20715508205174771/2669375000000000000000000000000 : ℝ)*base75 + (3477373921003323/1334687500000000000000000000000 : ℝ)*base77 + (21977095771347073/1334687500000000000000000000000 : ℝ)*base79 + (96392702009/21355000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (480477/125000000000000000000 : ℝ)*base90 + (480477/125000000000000000000 : ℝ)*base92 + (480477/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (759265848586738655980446129/106775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1263093439/100000000000000 : ℝ)*(base19) + (1370032323/100000000000000 : ℝ)*(base23) + (145929741/100000000000000 : ℝ)*(upper3) + (46634117/100000000000000 : ℝ)*(lower4) + (150489919/100000000000000 : ℝ)*(upper5) + (847974799858543/20000000000000 : ℝ)*(major0) + (847974799858543/20000000000000 : ℝ)*(major1) + (847974799858543/20000000000000 : ℝ)*(major2) + (3065313373/12500000000000 : ℝ)*(sp1) + (2612274803/10000000000000 : ℝ)*(sp2) + (2861002666333167/50000000000000 : ℝ)*(sp4) + (5721979547065911/100000000000000 : ℝ)*(sp5) + (5721977839885981/100000000000000 : ℝ)*(sp6) + (86179450902789/3125000000000 : ℝ)*(sp7) + (86179450902789/3125000000000 : ℝ)*(f.failure) + (2861002666333167/50000000000000 : ℝ)*(f.sum) + (3784636989823/2135500000000000000000000000 : ℝ)*base65 + (692838232160517957/213550000000000000000000000000000 : ℝ)*base68 + (200896349219317957/213550000000000000000000000000000 : ℝ)*base70 + (107733602163667957/213550000000000000000000000000000 : ℝ)*base72 + (9343877407533/2135500000000000000000000000 : ℝ)*base73 + (1067499654776632043/213550000000000000000000000000000 : ℝ)*base75 + (1113617748129582043/213550000000000000000000000000000 : ℝ)*base77 + (2715614736262317957/213550000000000000000000000000000 : ℝ)*base80 + (1614383891827/1067750000000000000000000000 : ℝ)*base82 + (35041/15625000000000000000 : ℝ)*base89 + (35041/15625000000000000000 : ℝ)*base91 + (35041/15625000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1317_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3759/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2153/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2757/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1317_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1317_s5_0 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2065708653/10000000000 : ℝ)*x 0 + (2707241287/5000000000 : ℝ)*x 1 + (2621679803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2065708653/10000000000 : ℝ)^4277 ≤ (785854559883/6250000000000 : ℝ)^3253 := by
    have hnat : (2065708653 : ℕ)^4277*6250000000000^3253 ≤ 785854559883^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065708653 10000000000 785854559883 6250000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707241287/5000000000 : ℝ)^4277 ≤ (5579487913027/12500000000000 : ℝ)^3253 := by
    have hnat : (2707241287 : ℕ)^4277*12500000000000^3253 ≤ 5579487913027^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707241287 5000000000 5579487913027 12500000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621679803/5000000000 : ℝ)^4277 ≤ (5348802964891/12500000000000 : ℝ)^3253 := by
    have hnat : (2621679803 : ℕ)^4277*12500000000000^3253 ≤ 5348802964891^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621679803 5000000000 5348802964891 12500000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2065708653/10000000000 : ℝ), (2707241287/5000000000 : ℝ), (2621679803/5000000000 : ℝ)] ![(785854559883/6250000000000 : ℝ), (5579487913027/12500000000000 : ℝ), (5348802964891/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2065708653/10000000000 : ℝ)|^4277 ≤ (785854559883/6250000000000 : ℝ)^3253
        have hw : |(-2065708653/10000000000 : ℝ)|=(2065708653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707241287/5000000000 : ℝ)|^4277 ≤ (5579487913027/12500000000000 : ℝ)^3253
        have hw : |(2707241287/5000000000 : ℝ)|=(2707241287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621679803/5000000000 : ℝ)|^4277 ≤ (5348802964891/12500000000000 : ℝ)^3253
        have hw : |(2621679803/5000000000 : ℝ)|=(2621679803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s5_1 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349537789/10000000000 : ℝ)*x 0 + (-2152926679/10000000000 : ℝ)*x 1 + (524335961/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349537789/10000000000 : ℝ)^4277 ≤ (43933310160049/100000000000000 : ℝ)^3253 := by
    have hnat : (5349537789 : ℕ)^4277*100000000000000^3253 ≤ 43933310160049^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349537789 10000000000 43933310160049 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2152926679/10000000000 : ℝ)^4277 ≤ (13276266072431/100000000000000 : ℝ)^3253 := by
    have hnat : (2152926679 : ℕ)^4277*100000000000000^3253 ≤ 13276266072431^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152926679 10000000000 13276266072431 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524335961/1000000000 : ℝ)^4277 ≤ (42790423762047/100000000000000 : ℝ)^3253 := by
    have hnat : (524335961 : ℕ)^4277*100000000000000^3253 ≤ 42790423762047^3253*1000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524335961 1000000000 42790423762047 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349537789/10000000000 : ℝ), (-2152926679/10000000000 : ℝ), (524335961/1000000000 : ℝ)] ![(43933310160049/100000000000000 : ℝ), (13276266072431/100000000000000 : ℝ), (42790423762047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349537789/10000000000 : ℝ)|^4277 ≤ (43933310160049/100000000000000 : ℝ)^3253
        have hw : |(5349537789/10000000000 : ℝ)|=(5349537789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2152926679/10000000000 : ℝ)|^4277 ≤ (13276266072431/100000000000000 : ℝ)^3253
        have hw : |(-2152926679/10000000000 : ℝ)|=(2152926679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524335961/1000000000 : ℝ)|^4277 ≤ (42790423762047/100000000000000 : ℝ)^3253
        have hw : |(524335961/1000000000 : ℝ)|=(524335961/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s5_2 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668692223/1250000000 : ℝ)*x 0 + (5243359609/10000000000 : ℝ)*x 1 + (-1076463343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668692223/1250000000 : ℝ)^4277 ≤ (43933310106061/100000000000000 : ℝ)^3253 := by
    have hnat : (668692223 : ℕ)^4277*100000000000000^3253 ≤ 43933310106061^3253*1250000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668692223 1250000000 43933310106061 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243359609/10000000000 : ℝ)^4277 ≤ (21395211875659/50000000000000 : ℝ)^3253 := by
    have hnat : (5243359609 : ℕ)^4277*50000000000000^3253 ≤ 21395211875659^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243359609 10000000000 21395211875659 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076463343/5000000000 : ℝ)^4277 ≤ (2655253225837/20000000000000 : ℝ)^3253 := by
    have hnat : (1076463343 : ℕ)^4277*20000000000000^3253 ≤ 2655253225837^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076463343 5000000000 2655253225837 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668692223/1250000000 : ℝ), (5243359609/10000000000 : ℝ), (-1076463343/5000000000 : ℝ)] ![(43933310106061/100000000000000 : ℝ), (21395211875659/50000000000000 : ℝ), (2655253225837/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668692223/1250000000 : ℝ)|^4277 ≤ (43933310106061/100000000000000 : ℝ)^3253
        have hw : |(668692223/1250000000 : ℝ)|=(668692223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243359609/10000000000 : ℝ)|^4277 ≤ (21395211875659/50000000000000 : ℝ)^3253
        have hw : |(5243359609/10000000000 : ℝ)|=(5243359609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1076463343/5000000000 : ℝ)|^4277 ≤ (2655253225837/20000000000000 : ℝ)^3253
        have hw : |(-1076463343/5000000000 : ℝ)|=(1076463343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s5_3 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (541645567/1250000000 : ℝ)*x 0 + (4159071223/10000000000 : ℝ)*x 1 + (225706607/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541645567/1250000000 : ℝ)^4277 ≤ (33302467105493/100000000000000 : ℝ)^3253 := by
    have hnat : (541645567 : ℕ)^4277*100000000000000^3253 ≤ 33302467105493^3253*1250000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541645567 1250000000 33302467105493 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4159071223/10000000000 : ℝ)^4277 ≤ (3155452240517/10000000000000 : ℝ)^3253 := by
    have hnat : (4159071223 : ℕ)^4277*10000000000000^3253 ≤ 3155452240517^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159071223 10000000000 3155452240517 10000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225706607/500000000 : ℝ)^4277 ≤ (35143010480217/100000000000000 : ℝ)^3253 := by
    have hnat : (225706607 : ℕ)^4277*100000000000000^3253 ≤ 35143010480217^3253*500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225706607 500000000 35143010480217 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541645567/1250000000 : ℝ), (4159071223/10000000000 : ℝ), (225706607/500000000 : ℝ)] ![(33302467105493/100000000000000 : ℝ), (3155452240517/10000000000000 : ℝ), (35143010480217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541645567/1250000000 : ℝ)|^4277 ≤ (33302467105493/100000000000000 : ℝ)^3253
        have hw : |(541645567/1250000000 : ℝ)|=(541645567/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4159071223/10000000000 : ℝ)|^4277 ≤ (3155452240517/10000000000000 : ℝ)^3253
        have hw : |(4159071223/10000000000 : ℝ)|=(4159071223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(225706607/500000000 : ℝ)|^4277 ≤ (35143010480217/100000000000000 : ℝ)^3253
        have hw : |(225706607/500000000 : ℝ)|=(225706607/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s5_4 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2065721359/10000000000 : ℝ)*x 0 + (5243974347/10000000000 : ℝ)*x 1 + (5413864613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2065721359/10000000000 : ℝ)^4277 ≤ (12573774643281/100000000000000 : ℝ)^3253 := by
    have hnat : (2065721359 : ℕ)^4277*100000000000000^3253 ≤ 12573774643281^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065721359 10000000000 12573774643281 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243974347/10000000000 : ℝ)^4277 ≤ (2674813743529/6250000000000 : ℝ)^3253 := by
    have hnat : (5243974347 : ℕ)^4277*6250000000000^3253 ≤ 2674813743529^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243974347 10000000000 2674813743529 6250000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413864613/10000000000 : ℝ)^4277 ≤ (22314602723999/50000000000000 : ℝ)^3253 := by
    have hnat : (5413864613 : ℕ)^4277*50000000000000^3253 ≤ 22314602723999^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413864613 10000000000 22314602723999 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2065721359/10000000000 : ℝ), (5243974347/10000000000 : ℝ), (5413864613/10000000000 : ℝ)] ![(12573774643281/100000000000000 : ℝ), (2674813743529/6250000000000 : ℝ), (22314602723999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2065721359/10000000000 : ℝ)|^4277 ≤ (12573774643281/100000000000000 : ℝ)^3253
        have hw : |(-2065721359/10000000000 : ℝ)|=(2065721359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243974347/10000000000 : ℝ)|^4277 ≤ (2674813743529/6250000000000 : ℝ)^3253
        have hw : |(5243974347/10000000000 : ℝ)|=(5243974347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413864613/10000000000 : ℝ)|^4277 ≤ (22314602723999/50000000000000 : ℝ)^3253
        have hw : |(5413864613/10000000000 : ℝ)|=(5413864613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s5_5 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305590139/10000000000 : ℝ)*x 0 + (-991210847/5000000000 : ℝ)*x 1 + (1082772943/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305590139/10000000000 : ℝ)^4277 ≤ (8691877922797/20000000000000 : ℝ)^3253 := by
    have hnat : (5305590139 : ℕ)^4277*20000000000000^3253 ≤ 8691877922797^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305590139 10000000000 8691877922797 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (991210847/5000000000 : ℝ)^4277 ≤ (595570190619/5000000000000 : ℝ)^3253 := by
    have hnat : (991210847 : ℕ)^4277*5000000000000^3253 ≤ 595570190619^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991210847 5000000000 595570190619 5000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082772943/2000000000 : ℝ)^4277 ≤ (44629206553519/100000000000000 : ℝ)^3253 := by
    have hnat : (1082772943 : ℕ)^4277*100000000000000^3253 ≤ 44629206553519^3253*2000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082772943 2000000000 44629206553519 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305590139/10000000000 : ℝ), (-991210847/5000000000 : ℝ), (1082772943/2000000000 : ℝ)] ![(8691877922797/20000000000000 : ℝ), (595570190619/5000000000000 : ℝ), (44629206553519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305590139/10000000000 : ℝ)|^4277 ≤ (8691877922797/20000000000000 : ℝ)^3253
        have hw : |(5305590139/10000000000 : ℝ)|=(5305590139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-991210847/5000000000 : ℝ)|^4277 ≤ (595570190619/5000000000000 : ℝ)^3253
        have hw : |(-991210847/5000000000 : ℝ)|=(991210847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082772943/2000000000 : ℝ)|^4277 ≤ (44629206553519/100000000000000 : ℝ)^3253
        have hw : |(1082772943/2000000000 : ℝ)|=(1082772943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s5_6 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652795329/5000000000 : ℝ)*x 0 + (2706932169/5000000000 : ℝ)*x 1 + (-3871917/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652795329/5000000000 : ℝ)^4277 ≤ (21729697601739/50000000000000 : ℝ)^3253 := by
    have hnat : (2652795329 : ℕ)^4277*50000000000000^3253 ≤ 21729697601739^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652795329 5000000000 21729697601739 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706932169/5000000000 : ℝ)^4277 ≤ (22314601233713/50000000000000 : ℝ)^3253 := by
    have hnat : (2706932169 : ℕ)^4277*50000000000000^3253 ≤ 22314601233713^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706932169 5000000000 22314601233713 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3871917/19531250 : ℝ)^4277 ≤ (5955701155699/50000000000000 : ℝ)^3253 := by
    have hnat : (3871917 : ℕ)^4277*50000000000000^3253 ≤ 5955701155699^3253*19531250^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3871917 19531250 5955701155699 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652795329/5000000000 : ℝ), (2706932169/5000000000 : ℝ), (-3871917/19531250 : ℝ)] ![(21729697601739/50000000000000 : ℝ), (22314601233713/50000000000000 : ℝ), (5955701155699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652795329/5000000000 : ℝ)|^4277 ≤ (21729697601739/50000000000000 : ℝ)^3253
        have hw : |(2652795329/5000000000 : ℝ)|=(2652795329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706932169/5000000000 : ℝ)|^4277 ≤ (22314601233713/50000000000000 : ℝ)^3253
        have hw : |(2706932169/5000000000 : ℝ)|=(2706932169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3871917/19531250 : ℝ)|^4277 ≤ (5955701155699/50000000000000 : ℝ)^3253
        have hw : |(-3871917/19531250 : ℝ)|=(3871917/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s5_7 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083297759/2500000000 : ℝ)*x 0 + (70513381/156250000 : ℝ)*x 1 + (208017667/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083297759/2500000000 : ℝ)^4277 ≤ (1040710465067/3125000000000 : ℝ)^3253 := by
    have hnat : (1083297759 : ℕ)^4277*3125000000000^3253 ≤ 1040710465067^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083297759 2500000000 1040710465067 3125000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70513381/156250000 : ℝ)^4277 ≤ (35129952735283/100000000000000 : ℝ)^3253 := by
    have hnat : (70513381 : ℕ)^4277*100000000000000^3253 ≤ 35129952735283^3253*156250000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70513381 156250000 35129952735283 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208017667/500000000 : ℝ)^4277 ≤ (6313462472933/20000000000000 : ℝ)^3253 := by
    have hnat : (208017667 : ℕ)^4277*20000000000000^3253 ≤ 6313462472933^3253*500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208017667 500000000 6313462472933 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083297759/2500000000 : ℝ), (70513381/156250000 : ℝ), (208017667/500000000 : ℝ)] ![(1040710465067/3125000000000 : ℝ), (35129952735283/100000000000000 : ℝ), (6313462472933/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083297759/2500000000 : ℝ)|^4277 ≤ (1040710465067/3125000000000 : ℝ)^3253
        have hw : |(1083297759/2500000000 : ℝ)|=(1083297759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70513381/156250000 : ℝ)|^4277 ≤ (35129952735283/100000000000000 : ℝ)^3253
        have hw : |(70513381/156250000 : ℝ)|=(70513381/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208017667/500000000 : ℝ)|^4277 ≤ (6313462472933/20000000000000 : ℝ)^3253
        have hw : |(208017667/500000000 : ℝ)|=(208017667/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1317_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2757/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11079/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14701/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2757/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2757/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2757/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2757/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2757/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2757/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2757/25000 : ℝ) ^ (1069/256 : ℝ) ≤ (5019331936369653/50000000000000000000 : ℝ) := by
    have hpowers : (2757/25000 : ℝ)^1069 ≤ (5019331936369653/50000000000000000000 : ℝ)^256 := by
      have hnat : (2757 : ℕ)^1069*50000000000000000000^256 ≤ 5019331936369653^256*25000^1069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2757 25000 5019331936369653 50000000000000000000 1069 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2757/25000 : ℝ)) (X := (5019331936369653/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2951/20000 : ℝ) ^ (1069/256 : ℝ) ≤ (3385883036205277/10000000000000000000 : ℝ) := by
    have hpowers : (2951/20000 : ℝ)^1069 ≤ (3385883036205277/10000000000000000000 : ℝ)^256 := by
      have hnat : (2951 : ℕ)^1069*10000000000000000000^256 ≤ 3385883036205277^256*20000^1069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2951 20000 3385883036205277 10000000000000000000 1069 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2951/20000 : ℝ)) (X := (3385883036205277/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005019331936369653/25000000000000000000 : ℝ) ≤ (5000240383701777/5000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (25005019331936369653/25000000000000000000 : ℝ)^256 ≤ (5000240383701777/5000000000000000 : ℝ)^1069 := by
      have hnat : (25005019331936369653 : ℕ)^256*5000000000000000^1069 ≤ 5000240383701777^1069*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005019331936369653 25000000000000000000 5000240383701777 5000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000240383701777/5000000000000000 : ℝ)) (X := (25005019331936369653/25000000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010974373558698019/25000000000000000000 : ℝ) ≤ (2000210212967993/2000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (25010974373558698019/25000000000000000000 : ℝ)^256 ≤ (2000210212967993/2000000000000000 : ℝ)^1069 := by
      have hnat : (25010974373558698019 : ℕ)^256*2000000000000000^1069 ≤ 2000210212967993^1069*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010974373558698019 25000000000000000000 2000210212967993 2000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000210212967993/2000000000000000 : ℝ)) (X := (25010974373558698019/25000000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003385883036205277/5000000000000000000 : ℝ) ≤ (1250202670284547/1250000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (5003385883036205277/5000000000000000000 : ℝ)^256 ≤ (1250202670284547/1250000000000000 : ℝ)^1069 := by
      have hnat : (5003385883036205277 : ℕ)^256*1250000000000000^1069 ≤ 1250202670284547^1069*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003385883036205277 5000000000000000000 1250202670284547 1250000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250202670284547/1250000000000000 : ℝ)) (X := (5003385883036205277/5000000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5019331936369653/50000000000000000000 : ℝ) ≤ ((18629606669927782371/18635000000000000000 : ℝ)+2*(570297436411/372700000000000 : ℝ)*(2757/25000 : ℝ))^(1069/256 : ℝ) := by
    rw [show (18629606669927782371/18635000000000000000 : ℝ)+2*(570297436411/372700000000000 : ℝ)*(2757/25000 : ℝ)=(5000240383701777/5000000000000000 : ℝ) by norm_num, show 1+2*(5019331936369653/50000000000000000000 : ℝ)=(25005019331936369653/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3385883036205277/10000000000000000000 : ℝ)+(5019331936369653/50000000000000000000 : ℝ) ≤ ((18629606669927782371/18635000000000000000 : ℝ)+(570297436411/372700000000000 : ℝ)*((2951/20000 : ℝ)+(2757/25000 : ℝ)))^(1069/256 : ℝ) := by
    rw [show (18629606669927782371/18635000000000000000 : ℝ)+(570297436411/372700000000000 : ℝ)*((2951/20000 : ℝ)+(2757/25000 : ℝ))=(2000210212967993/2000000000000000 : ℝ) by norm_num, show 1+(3385883036205277/10000000000000000000 : ℝ)+(5019331936369653/50000000000000000000 : ℝ)=(25010974373558698019/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3385883036205277/10000000000000000000 : ℝ) ≤ ((18629606669927782371/18635000000000000000 : ℝ)+2*(570297436411/372700000000000 : ℝ)*(2951/20000 : ℝ))^(1069/256 : ℝ) := by
    rw [show (18629606669927782371/18635000000000000000 : ℝ)+2*(570297436411/372700000000000 : ℝ)*(2951/20000 : ℝ)=(1250202670284547/1250000000000000 : ℝ) by norm_num, show 1+2*(3385883036205277/10000000000000000000 : ℝ)=(5003385883036205277/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18629606669927782371/18635000000000000000 : ℝ)*(X 1 0+X 2 0)+(570297436411/372700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (2757/25000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (18629606669927782371/18635000000000000000 : ℝ)) (alpha := (570297436411/372700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18629606669927782371/18635000000000000000 : ℝ)*(X 0 1+X 2 1)+(570297436411/372700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (2757/25000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (18629606669927782371/18635000000000000000 : ℝ)) (alpha := (570297436411/372700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18629606669927782371/18635000000000000000 : ℝ)*(X 0 2+X 1 2)+(570297436411/372700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (2757/25000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (18629606669927782371/18635000000000000000 : ℝ)) (alpha := (570297436411/372700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2065708653/10000000000 : ℝ)*X 0 0+(2707241287/5000000000 : ℝ)*X 0 1+(2621679803/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349537789/10000000000 : ℝ)*X 1 0+(-2152926679/10000000000 : ℝ)*X 1 1+(524335961/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668692223/1250000000 : ℝ)*X 2 0+(5243359609/10000000000 : ℝ)*X 2 1+(-1076463343/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((541645567/1250000000 : ℝ)*X 0 0+(4159071223/10000000000 : ℝ)*X 0 1+(225706607/500000000 : ℝ)*X 0 2+(541645567/1250000000 : ℝ)*X 1 0+(4159071223/10000000000 : ℝ)*X 1 1+(225706607/500000000 : ℝ)*X 1 2+(541645567/1250000000 : ℝ)*X 2 0+(4159071223/10000000000 : ℝ)*X 2 1+(225706607/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2065721359/10000000000 : ℝ)*X 0 0+(5243974347/10000000000 : ℝ)*X 0 1+(5413864613/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305590139/10000000000 : ℝ)*X 1 0+(-991210847/5000000000 : ℝ)*X 1 1+(1082772943/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652795329/5000000000 : ℝ)*X 2 0+(2706932169/5000000000 : ℝ)*X 2 1+(-3871917/19531250 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1083297759/2500000000 : ℝ)*X 0 0+(70513381/156250000 : ℝ)*X 0 1+(208017667/500000000 : ℝ)*X 0 2+(1083297759/2500000000 : ℝ)*X 1 0+(70513381/156250000 : ℝ)*X 1 1+(208017667/500000000 : ℝ)*X 1 2+(1083297759/2500000000 : ℝ)*X 2 0+(70513381/156250000 : ℝ)*X 2 1+(208017667/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (941851222056004736933806149/116468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1528527139/100000000000000 : ℝ)*(base19) + (1416234959/100000000000000 : ℝ)*(base23) + (2857461/5000000000000 : ℝ)*(lower2) + (208695947/100000000000000 : ℝ)*(upper3) + (59793063/50000000000000 : ℝ)*(upper5) + (1082532824996127/25000000000000 : ℝ)*(major0) + (1082532824996127/25000000000000 : ℝ)*(major1) + (1082532824996127/25000000000000 : ℝ)*(major2) + (730472910142139/12500000000000 : ℝ)*(sp0) + (5843812291711369/100000000000000 : ℝ)*(sp1) + (5843812404003549/100000000000000 : ℝ)*(sp2) + (704108099942677/25000000000000 : ℝ)*(sp3) + (6107820279/20000000000000 : ℝ)*(sp4) + (4027600539/25000000000000 : ℝ)*(sp7) + (563289702034573/20000000000000 : ℝ)*(f.failure) + (1460953455059627/25000000000000 : ℝ)*(f.sum) + (204266833618283/18635000000000000000000000000 : ℝ)*base65 + (48518521095352117/465875000000000000000000000000000 : ℝ)*base67 + (5841819021107602117/465875000000000000000000000000000 : ℝ)*base69 + (4005330883144352117/465875000000000000000000000000000 : ℝ)*base71 + (15122942594293/18635000000000000000000000000 : ℝ)*base73 + (3463881801435022883/465875000000000000000000000000000 : ℝ)*base76 + (4797703999528727117/465875000000000000000000000000000 : ℝ)*base77 + (1409501526185852117/465875000000000000000000000000000 : ℝ)*base79 + (90254644300539/9317500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (222487/100000000000000000000 : ℝ)*base89 + (222487/100000000000000000000 : ℝ)*base91 + (222487/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33027386531995029140733/9317500000000000000000000000 : ℝ) := by norm_num
    linear_combination (420011849/50000000000000 : ℝ)*(base19) + (325027219/20000000000000 : ℝ)*(base23) + (24997309/25000000000000 : ℝ)*(upper3) + (32298837/50000000000000 : ℝ)*(lower4) + (36141519/25000000000000 : ℝ)*(upper5) + (1090376722860711/25000000000000 : ℝ)*(major0) + (1090376722860711/25000000000000 : ℝ)*(major1) + (1090376722860711/25000000000000 : ℝ)*(major2) + (10125673419/50000000000000 : ℝ)*(sp1) + (30823222527/100000000000000 : ℝ)*(sp2) + (5886157519846911/100000000000000 : ℝ)*(sp4) + (735767053559547/12500000000000 : ℝ)*(sp5) + (5886125071488289/100000000000000 : ℝ)*(sp6) + (2836856144883373/100000000000000 : ℝ)*(sp7) + (2836856144883373/100000000000000 : ℝ)*(f.failure) + (5886157519846911/100000000000000 : ℝ)*(f.sum) + (111210691289781/18635000000000000000000000000 : ℝ)*base66 + (608458853949999219/465875000000000000000000000000000 : ℝ)*base68 + (6170590337740250781/465875000000000000000000000000000 : ℝ)*base69 + (3694331653715625781/465875000000000000000000000000000 : ℝ)*base71 + (53098368910863/9317500000000000000000000000 : ℝ)*base74 + (849039727944624219/465875000000000000000000000000000 : ℝ)*base76 + (6594614624132125781/465875000000000000000000000000000 : ℝ)*base77 + (5752304695489499219/465875000000000000000000000000000 : ℝ)*base80 + (35036230762893/9317500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2290313/500000000000000000000 : ℝ)*base90 + (2290313/500000000000000000000 : ℝ)*base92 + (2290313/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1317_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2757/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11079/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1317_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1317_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16207/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9683/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11079/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1317_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1317_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1317_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16207/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9683/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11079/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1317_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

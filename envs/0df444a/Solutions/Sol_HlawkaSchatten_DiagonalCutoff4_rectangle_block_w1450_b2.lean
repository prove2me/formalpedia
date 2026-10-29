-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1450_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:59:34.491783+00:00
-- url     : https://prove2.me/submissions/36c270d1-8243-46a4-87bc-1fed92f78ef7

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
theorem support_rectangle_w1450_s6_0 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-61069303/312500000 : ℝ)*x 0 + (135178527/250000000 : ℝ)*x 1 + (5247352411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61069303/312500000 : ℝ)^2205 ≤ (11927453919017/100000000000000 : ℝ)^1693 := by
    have hnat : (61069303 : ℕ)^2205*100000000000000^1693 ≤ 11927453919017^1693*312500000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61069303 312500000 11927453919017 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135178527/250000000 : ℝ)^2205 ≤ (44896380447007/100000000000000 : ℝ)^1693 := by
    have hnat : (135178527 : ℕ)^2205*100000000000000^1693 ≤ 44896380447007^1693*250000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135178527 250000000 44896380447007 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247352411/10000000000 : ℝ)^2205 ≤ (21588082811533/50000000000000 : ℝ)^1693 := by
    have hnat : (5247352411 : ℕ)^2205*50000000000000^1693 ≤ 21588082811533^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247352411 10000000000 21588082811533 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61069303/312500000 : ℝ), (135178527/250000000 : ℝ), (5247352411/10000000000 : ℝ)] ![(11927453919017/100000000000000 : ℝ), (44896380447007/100000000000000 : ℝ), (21588082811533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61069303/312500000 : ℝ)|^2205 ≤ (11927453919017/100000000000000 : ℝ)^1693
        have hw : |(-61069303/312500000 : ℝ)|=(61069303/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135178527/250000000 : ℝ)|^2205 ≤ (44896380447007/100000000000000 : ℝ)^1693
        have hw : |(135178527/250000000 : ℝ)|=(135178527/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247352411/10000000000 : ℝ)|^2205 ≤ (21588082811533/50000000000000 : ℝ)^1693
        have hw : |(5247352411/10000000000 : ℝ)|=(5247352411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s6_1 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5346877941/10000000000 : ℝ)*x 0 + (-2035554563/10000000000 : ℝ)*x 1 + (1311838097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346877941/10000000000 : ℝ)^2205 ≤ (22122891325333/50000000000000 : ℝ)^1693 := by
    have hnat : (5346877941 : ℕ)^2205*50000000000000^1693 ≤ 22122891325333^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346877941 10000000000 22122891325333 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2035554563/10000000000 : ℝ)^2205 ≤ (12578051955087/100000000000000 : ℝ)^1693 := by
    have hnat : (2035554563 : ℕ)^2205*100000000000000^1693 ≤ 12578051955087^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035554563 10000000000 12578051955087 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311838097/2500000000 : ℝ)^2205 ≤ (8635233075317/20000000000000 : ℝ)^1693 := by
    have hnat : (1311838097 : ℕ)^2205*20000000000000^1693 ≤ 8635233075317^1693*2500000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311838097 2500000000 8635233075317 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346877941/10000000000 : ℝ), (-2035554563/10000000000 : ℝ), (1311838097/2500000000 : ℝ)] ![(22122891325333/50000000000000 : ℝ), (12578051955087/100000000000000 : ℝ), (8635233075317/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346877941/10000000000 : ℝ)|^2205 ≤ (22122891325333/50000000000000 : ℝ)^1693
        have hw : |(5346877941/10000000000 : ℝ)|=(5346877941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2035554563/10000000000 : ℝ)|^2205 ≤ (12578051955087/100000000000000 : ℝ)^1693
        have hw : |(-2035554563/10000000000 : ℝ)|=(2035554563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311838097/2500000000 : ℝ)|^2205 ≤ (8635233075317/20000000000000 : ℝ)^1693
        have hw : |(1311838097/2500000000 : ℝ)|=(1311838097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s6_2 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069375637/2000000000 : ℝ)*x 0 + (5247352439/10000000000 : ℝ)*x 1 + (-2035554169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069375637/2000000000 : ℝ)^2205 ≤ (5530723160051/12500000000000 : ℝ)^1693 := by
    have hnat : (1069375637 : ℕ)^2205*12500000000000^1693 ≤ 5530723160051^1693*2000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069375637 2000000000 5530723160051 12500000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247352439/10000000000 : ℝ)^2205 ≤ (4317616592313/10000000000000 : ℝ)^1693 := by
    have hnat : (5247352439 : ℕ)^2205*10000000000000^1693 ≤ 4317616592313^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247352439 10000000000 4317616592313 10000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2035554169/10000000000 : ℝ)^2205 ≤ (12578048784217/100000000000000 : ℝ)^1693 := by
    have hnat : (2035554169 : ℕ)^2205*100000000000000^1693 ≤ 12578048784217^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035554169 10000000000 12578048784217 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069375637/2000000000 : ℝ), (5247352439/10000000000 : ℝ), (-2035554169/10000000000 : ℝ)] ![(5530723160051/12500000000000 : ℝ), (4317616592313/10000000000000 : ℝ), (12578048784217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069375637/2000000000 : ℝ)|^2205 ≤ (5530723160051/12500000000000 : ℝ)^1693
        have hw : |(1069375637/2000000000 : ℝ)|=(1069375637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247352439/10000000000 : ℝ)|^2205 ≤ (4317616592313/10000000000000 : ℝ)^1693
        have hw : |(5247352439/10000000000 : ℝ)|=(5247352439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2035554169/10000000000 : ℝ)|^2205 ≤ (12578048784217/100000000000000 : ℝ)^1693
        have hw : |(-2035554169/10000000000 : ℝ)|=(2035554169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s6_3 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (537393743/1250000000 : ℝ)*x 0 + (4128125053/10000000000 : ℝ)*x 1 + (4476463553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537393743/1250000000 : ℝ)^2205 ≤ (33305006250987/100000000000000 : ℝ)^1693 := by
    have hnat : (537393743 : ℕ)^2205*100000000000000^1693 ≤ 33305006250987^1693*1250000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537393743 1250000000 33305006250987 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4128125053/10000000000 : ℝ)^2205 ≤ (3948736607397/12500000000000 : ℝ)^1693 := by
    have hnat : (4128125053 : ℕ)^2205*12500000000000^1693 ≤ 3948736607397^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128125053 10000000000 3948736607397 12500000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4476463553/10000000000 : ℝ)^2205 ≤ (35105100878253/100000000000000 : ℝ)^1693 := by
    have hnat : (4476463553 : ℕ)^2205*100000000000000^1693 ≤ 35105100878253^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476463553 10000000000 35105100878253 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537393743/1250000000 : ℝ), (4128125053/10000000000 : ℝ), (4476463553/10000000000 : ℝ)] ![(33305006250987/100000000000000 : ℝ), (3948736607397/12500000000000 : ℝ), (35105100878253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537393743/1250000000 : ℝ)|^2205 ≤ (33305006250987/100000000000000 : ℝ)^1693
        have hw : |(537393743/1250000000 : ℝ)|=(537393743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4128125053/10000000000 : ℝ)|^2205 ≤ (3948736607397/12500000000000 : ℝ)^1693
        have hw : |(4128125053/10000000000 : ℝ)|=(4128125053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4476463553/10000000000 : ℝ)|^2205 ≤ (35105100878253/100000000000000 : ℝ)^1693
        have hw : |(4476463553/10000000000 : ℝ)|=(4476463553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s6_4 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-977114267/5000000000 : ℝ)*x 0 + (1311982459/2500000000 : ℝ)*x 1 + (5406560883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977114267/5000000000 : ℝ)^2205 ≤ (11927540073117/100000000000000 : ℝ)^1693 := by
    have hnat : (977114267 : ℕ)^2205*100000000000000^1693 ≤ 11927540073117^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977114267 5000000000 11927540073117 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311982459/2500000000 : ℝ)^2205 ≤ (43182353736749/100000000000000 : ℝ)^1693 := by
    have hnat : (1311982459 : ℕ)^2205*100000000000000^1693 ≤ 43182353736749^1693*2500000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311982459 2500000000 43182353736749 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406560883/10000000000 : ℝ)^2205 ≤ (44890106169891/100000000000000 : ℝ)^1693 := by
    have hnat : (5406560883 : ℕ)^2205*100000000000000^1693 ≤ 44890106169891^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406560883 10000000000 44890106169891 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-977114267/5000000000 : ℝ), (1311982459/2500000000 : ℝ), (5406560883/10000000000 : ℝ)] ![(11927540073117/100000000000000 : ℝ), (43182353736749/100000000000000 : ℝ), (44890106169891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-977114267/5000000000 : ℝ)|^2205 ≤ (11927540073117/100000000000000 : ℝ)^1693
        have hw : |(-977114267/5000000000 : ℝ)|=(977114267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311982459/2500000000 : ℝ)|^2205 ≤ (43182353736749/100000000000000 : ℝ)^1693
        have hw : |(1311982459/2500000000 : ℝ)|=(1311982459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406560883/10000000000 : ℝ)|^2205 ≤ (44890106169891/100000000000000 : ℝ)^1693
        have hw : |(5406560883/10000000000 : ℝ)|=(5406560883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s6_5 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (663156671/1250000000 : ℝ)*x 0 + (-1876345919/10000000000 : ℝ)*x 1 + (5406560883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663156671/1250000000 : ℝ)^2205 ≤ (10949424368437/25000000000000 : ℝ)^1693 := by
    have hnat : (663156671 : ℕ)^2205*25000000000000^1693 ≤ 10949424368437^1693*1250000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663156671 1250000000 10949424368437 25000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1876345919/10000000000 : ℝ)^2205 ≤ (11312196341303/100000000000000 : ℝ)^1693 := by
    have hnat : (1876345919 : ℕ)^2205*100000000000000^1693 ≤ 11312196341303^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876345919 10000000000 11312196341303 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406560883/10000000000 : ℝ)^2205 ≤ (44890106169891/100000000000000 : ℝ)^1693 := by
    have hnat : (5406560883 : ℕ)^2205*100000000000000^1693 ≤ 44890106169891^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406560883 10000000000 44890106169891 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663156671/1250000000 : ℝ), (-1876345919/10000000000 : ℝ), (5406560883/10000000000 : ℝ)] ![(10949424368437/25000000000000 : ℝ), (11312196341303/100000000000000 : ℝ), (44890106169891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663156671/1250000000 : ℝ)|^2205 ≤ (10949424368437/25000000000000 : ℝ)^1693
        have hw : |(663156671/1250000000 : ℝ)|=(663156671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1876345919/10000000000 : ℝ)|^2205 ≤ (11312196341303/100000000000000 : ℝ)^1693
        have hw : |(-1876345919/10000000000 : ℝ)|=(1876345919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406560883/10000000000 : ℝ)|^2205 ≤ (44890106169891/100000000000000 : ℝ)^1693
        have hw : |(5406560883/10000000000 : ℝ)|=(5406560883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s6_6 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (663156671/1250000000 : ℝ)*x 0 + (5406560883/10000000000 : ℝ)*x 1 + (-1876345919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663156671/1250000000 : ℝ)^2205 ≤ (10949424368437/25000000000000 : ℝ)^1693 := by
    have hnat : (663156671 : ℕ)^2205*25000000000000^1693 ≤ 10949424368437^1693*1250000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663156671 1250000000 10949424368437 25000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406560883/10000000000 : ℝ)^2205 ≤ (44890106169891/100000000000000 : ℝ)^1693 := by
    have hnat : (5406560883 : ℕ)^2205*100000000000000^1693 ≤ 44890106169891^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406560883 10000000000 44890106169891 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1876345919/10000000000 : ℝ)^2205 ≤ (11312196341303/100000000000000 : ℝ)^1693 := by
    have hnat : (1876345919 : ℕ)^2205*100000000000000^1693 ≤ 11312196341303^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876345919 10000000000 11312196341303 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663156671/1250000000 : ℝ), (5406560883/10000000000 : ℝ), (-1876345919/10000000000 : ℝ)] ![(10949424368437/25000000000000 : ℝ), (44890106169891/100000000000000 : ℝ), (11312196341303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663156671/1250000000 : ℝ)|^2205 ≤ (10949424368437/25000000000000 : ℝ)^1693
        have hw : |(663156671/1250000000 : ℝ)|=(663156671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406560883/10000000000 : ℝ)|^2205 ≤ (44890106169891/100000000000000 : ℝ)^1693
        have hw : |(5406560883/10000000000 : ℝ)|=(5406560883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1876345919/10000000000 : ℝ)|^2205 ≤ (11312196341303/100000000000000 : ℝ)^1693
        have hw : |(-1876345919/10000000000 : ℝ)|=(1876345919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s6_7 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4299173969/10000000000 : ℝ)*x 0 + (4475204781/10000000000 : ℝ)*x 1 + (4129390609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299173969/10000000000 : ℝ)^2205 ≤ (33305248656407/100000000000000 : ℝ)^1693 := by
    have hnat : (4299173969 : ℕ)^2205*100000000000000^1693 ≤ 33305248656407^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299173969 10000000000 33305248656407 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4475204781/10000000000 : ℝ)^2205 ≤ (7018448919107/20000000000000 : ℝ)^1693 := by
    have hnat : (4475204781 : ℕ)^2205*20000000000000^1693 ≤ 7018448919107^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475204781 10000000000 7018448919107 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4129390609/10000000000 : ℝ)^2205 ≤ (31602506731809/100000000000000 : ℝ)^1693 := by
    have hnat : (4129390609 : ℕ)^2205*100000000000000^1693 ≤ 31602506731809^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129390609 10000000000 31602506731809 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299173969/10000000000 : ℝ), (4475204781/10000000000 : ℝ), (4129390609/10000000000 : ℝ)] ![(33305248656407/100000000000000 : ℝ), (7018448919107/20000000000000 : ℝ), (31602506731809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299173969/10000000000 : ℝ)|^2205 ≤ (33305248656407/100000000000000 : ℝ)^1693
        have hw : |(4299173969/10000000000 : ℝ)|=(4299173969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4475204781/10000000000 : ℝ)|^2205 ≤ (7018448919107/20000000000000 : ℝ)^1693
        have hw : |(4475204781/10000000000 : ℝ)|=(4475204781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4129390609/10000000000 : ℝ)|^2205 ≤ (31602506731809/100000000000000 : ℝ)^1693
        have hw : |(4129390609/10000000000 : ℝ)|=(4129390609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1450_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39749881/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5691/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (923/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11379/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11379/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11379/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11379/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11379/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11379/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11379/100000 : ℝ) ^ (4409/1024 : ℝ) ≤ (1725565023433809/20000000000000000000 : ℝ) := by
    have hpowers : (11379/100000 : ℝ)^4409 ≤ (1725565023433809/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11379 : ℕ)^4409*20000000000000000000^1024 ≤ 1725565023433809^1024*100000^4409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11379 100000 1725565023433809 20000000000000000000 4409 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11379/100000 : ℝ)) (X := (1725565023433809/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14771/100000 : ℝ) ^ (4409/1024 : ℝ) ≤ (13265635258074469/50000000000000000000 : ℝ) := by
    have hpowers : (14771/100000 : ℝ)^4409 ≤ (13265635258074469/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14771 : ℕ)^4409*50000000000000000000^1024 ≤ 13265635258074469^1024*100000^4409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14771 100000 13265635258074469 50000000000000000000 4409 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14771/100000 : ℝ)) (X := (13265635258074469/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001725565023433809/10000000000000000000 : ℝ) ≤ (2500100184937137/2500000000000000 : ℝ) ^ (4409/1024 : ℝ) := by
    have hpowers : (10001725565023433809/10000000000000000000 : ℝ)^1024 ≤ (2500100184937137/2500000000000000 : ℝ)^4409 := by
      have hnat : (10001725565023433809 : ℕ)^1024*2500000000000000^4409 ≤ 2500100184937137^4409*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001725565023433809 10000000000000000000 2500100184937137 2500000000000000 1024 4409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500100184937137/2500000000000000 : ℝ)) (X := (10001725565023433809/10000000000000000000 : ℝ)) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035159095633317983/100000000000000000000 : ℝ) ≤ (10000816467583227/10000000000000000 : ℝ) ^ (4409/1024 : ℝ) := by
    have hpowers : (100035159095633317983/100000000000000000000 : ℝ)^1024 ≤ (10000816467583227/10000000000000000 : ℝ)^4409 := by
      have hnat : (100035159095633317983 : ℕ)^1024*10000000000000000^4409 ≤ 10000816467583227^4409*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035159095633317983 100000000000000000000 10000816467583227 10000000000000000 1024 4409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000816467583227/10000000000000000 : ℝ)) (X := (100035159095633317983/100000000000000000000 : ℝ)) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013265635258074469/25000000000000000000 : ℝ) ≤ (5000616097708953/5000000000000000 : ℝ) ^ (4409/1024 : ℝ) := by
    have hpowers : (25013265635258074469/25000000000000000000 : ℝ)^1024 ≤ (5000616097708953/5000000000000000 : ℝ)^4409 := by
      have hnat : (25013265635258074469 : ℕ)^1024*5000000000000000^4409 ≤ 5000616097708953^4409*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013265635258074469 25000000000000000000 5000616097708953 5000000000000000 1024 4409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000616097708953/5000000000000000 : ℝ)) (X := (25013265635258074469/25000000000000000000 : ℝ)) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1725565023433809/20000000000000000000 : ℝ) ≤ ((16955949087582725067/16960000000000000000 : ℝ)+2*(415727834679/339200000000000 : ℝ)*(11379/100000 : ℝ))^(4409/1024 : ℝ) := by
    rw [show (16955949087582725067/16960000000000000000 : ℝ)+2*(415727834679/339200000000000 : ℝ)*(11379/100000 : ℝ)=(2500100184937137/2500000000000000 : ℝ) by norm_num, show 1+2*(1725565023433809/20000000000000000000 : ℝ)=(10001725565023433809/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13265635258074469/50000000000000000000 : ℝ)+(1725565023433809/20000000000000000000 : ℝ) ≤ ((16955949087582725067/16960000000000000000 : ℝ)+(415727834679/339200000000000 : ℝ)*((14771/100000 : ℝ)+(11379/100000 : ℝ)))^(4409/1024 : ℝ) := by
    rw [show (16955949087582725067/16960000000000000000 : ℝ)+(415727834679/339200000000000 : ℝ)*((14771/100000 : ℝ)+(11379/100000 : ℝ))=(10000816467583227/10000000000000000 : ℝ) by norm_num, show 1+(13265635258074469/50000000000000000000 : ℝ)+(1725565023433809/20000000000000000000 : ℝ)=(100035159095633317983/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13265635258074469/50000000000000000000 : ℝ) ≤ ((16955949087582725067/16960000000000000000 : ℝ)+2*(415727834679/339200000000000 : ℝ)*(14771/100000 : ℝ))^(4409/1024 : ℝ) := by
    rw [show (16955949087582725067/16960000000000000000 : ℝ)+2*(415727834679/339200000000000 : ℝ)*(14771/100000 : ℝ)=(5000616097708953/5000000000000000 : ℝ) by norm_num, show 1+2*(13265635258074469/50000000000000000000 : ℝ)=(25013265635258074469/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16955949087582725067/16960000000000000000 : ℝ)*(X 1 0+X 2 0)+(415727834679/339200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4409/1024 : ℝ)) (lo := (11379/100000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (16955949087582725067/16960000000000000000 : ℝ)) (alpha := (415727834679/339200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16955949087582725067/16960000000000000000 : ℝ)*(X 0 1+X 2 1)+(415727834679/339200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4409/1024 : ℝ)) (lo := (11379/100000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (16955949087582725067/16960000000000000000 : ℝ)) (alpha := (415727834679/339200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16955949087582725067/16960000000000000000 : ℝ)*(X 0 2+X 1 2)+(415727834679/339200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4409/1024 : ℝ)) (lo := (11379/100000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (16955949087582725067/16960000000000000000 : ℝ)) (alpha := (415727834679/339200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-61069303/312500000 : ℝ)*X 0 0+(135178527/250000000 : ℝ)*X 0 1+(5247352411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346877941/10000000000 : ℝ)*X 1 0+(-2035554563/10000000000 : ℝ)*X 1 1+(1311838097/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069375637/2000000000 : ℝ)*X 2 0+(5247352439/10000000000 : ℝ)*X 2 1+(-2035554169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((537393743/1250000000 : ℝ)*X 0 0+(4128125053/10000000000 : ℝ)*X 0 1+(4476463553/10000000000 : ℝ)*X 0 2+(537393743/1250000000 : ℝ)*X 1 0+(4128125053/10000000000 : ℝ)*X 1 1+(4476463553/10000000000 : ℝ)*X 1 2+(537393743/1250000000 : ℝ)*X 2 0+(4128125053/10000000000 : ℝ)*X 2 1+(4476463553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-977114267/5000000000 : ℝ)*X 0 0+(1311982459/2500000000 : ℝ)*X 0 1+(5406560883/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663156671/1250000000 : ℝ)*X 1 0+(-1876345919/10000000000 : ℝ)*X 1 1+(5406560883/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663156671/1250000000 : ℝ)*X 2 0+(5406560883/10000000000 : ℝ)*X 2 1+(-1876345919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4299173969/10000000000 : ℝ)*X 0 0+(4475204781/10000000000 : ℝ)*X 0 1+(4129390609/10000000000 : ℝ)*X 0 2+(4299173969/10000000000 : ℝ)*X 1 0+(4475204781/10000000000 : ℝ)*X 1 1+(4129390609/10000000000 : ℝ)*X 1 2+(4299173969/10000000000 : ℝ)*X 2 0+(4475204781/10000000000 : ℝ)*X 2 1+(4129390609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20386666968012153234544473/2650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1905378493/100000000000000 : ℝ)*(base19) + (207154841/10000000000000 : ℝ)*(base23) + (5606349/10000000000000 : ℝ)*(upper3) + (7981827/12500000000000 : ℝ)*(upper4) + (263120659/50000000000000 : ℝ)*(upper5) + (28528633930127/625000000000 : ℝ)*(major0) + (28528633930127/625000000000 : ℝ)*(major1) + (28528633930127/625000000000 : ℝ)*(major2) + (1564573905850931/25000000000000 : ℝ)*(sp0) + (1251669234272453/20000000000000 : ℝ)*(sp1) + (6258346005192347/100000000000000 : ℝ)*(sp2) + (1435397662407217/50000000000000 : ℝ)*(sp3) + (26226668517/50000000000000 : ℝ)*(sp4) + (30719439/160000000000 : ℝ)*(sp7) + (287081452446381/10000000000000 : ℝ)*(f.failure) + (3129174038370379/50000000000000 : ℝ)*(f.sum) + (387432475067/106000000000000000000000000 : ℝ)*base65 + (84985260901556491/10600000000000000000000000000000 : ℝ)*base68 + (80170607033243509/10600000000000000000000000000000 : ℝ)*base69 + (59777855619443509/10600000000000000000000000000000 : ℝ)*base71 + (648772435941/106000000000000000000000000 : ℝ)*base73 + (96458363152843509/10600000000000000000000000000000 : ℝ)*base75 + (99475345021443509/10600000000000000000000000000000 : ℝ)*base77 + (76804065615043509/10600000000000000000000000000000 : ℝ)*base79 + (407517808429/106000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3630661/250000000000000000000 : ℝ)*base89 + (3630661/250000000000000000000 : ℝ)*base91 + (3630661/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (891901051048065882921/80000000000000000000000000 : ℝ) := by norm_num
    linear_combination (932693341/50000000000000 : ℝ)*(base19) + (2026112123/100000000000000 : ℝ)*(base23) + (630002509/100000000000000 : ℝ)*(lower1) + (45370299/20000000000000 : ℝ)*(upper3) + (73003739/100000000000000 : ℝ)*(lower4) + (57256679/25000000000000 : ℝ)*(upper5) + (1149450377357689/25000000000000 : ℝ)*(major0) + (1149450377357689/25000000000000 : ℝ)*(major1) + (1149450377357689/25000000000000 : ℝ)*(major2) + (736651877/25000000000000 : ℝ)*(sp2) + (3151947463882327/50000000000000 : ℝ)*(sp4) + (1575973265594493/25000000000000 : ℝ)*(sp5) + (6303889955045023/100000000000000 : ℝ)*(sp6) + (361463464933923/12500000000000 : ℝ)*(sp7) + (361463464933923/12500000000000 : ℝ)*(f.failure) + (3151947463882327/50000000000000 : ℝ)*(f.sum) + (146897466973/80000000000000000000000000 : ℝ)*base66 + (132427588786698871/8000000000000000000000000000000 : ℝ)*base67 + (4908080733301129/8000000000000000000000000000000 : ℝ)*base70 + (1653639515634698871/8000000000000000000000000000000 : ℝ)*base71 + (260659449053/80000000000000000000000000 : ℝ)*base74 + (912345199085301129/8000000000000000000000000000000 : ℝ)*base76 + (44817189650698871/8000000000000000000000000000000 : ℝ)*base77 + (37351055829301129/8000000000000000000000000000000 : ℝ)*base80 + (93050132467/80000000000000000000000000 : ℝ)*base81 + (386837/312500000000000000000 : ℝ)*base90 + (386837/312500000000000000000 : ℝ)*base92 + (386837/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1450_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39749881/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5691/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (923/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1450_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1450_s7_0 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1954219357/10000000000 : ℝ)*x 0 + (5407120433/10000000000 : ℝ)*x 1 + (2623686007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1954219357/10000000000 : ℝ)^2205 ≤ (11927467122731/100000000000000 : ℝ)^1693 := by
    have hnat : (1954219357 : ℕ)^2205*100000000000000^1693 ≤ 11927467122731^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954219357 10000000000 11927467122731 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407120433/10000000000 : ℝ)^2205 ≤ (44896157165903/100000000000000 : ℝ)^1693 := by
    have hnat : (5407120433 : ℕ)^2205*100000000000000^1693 ≤ 44896157165903^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407120433 10000000000 44896157165903 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623686007/5000000000 : ℝ)^2205 ≤ (43176375699947/100000000000000 : ℝ)^1693 := by
    have hnat : (2623686007 : ℕ)^2205*100000000000000^1693 ≤ 43176375699947^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623686007 5000000000 43176375699947 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1954219357/10000000000 : ℝ), (5407120433/10000000000 : ℝ), (2623686007/5000000000 : ℝ)] ![(11927467122731/100000000000000 : ℝ), (44896157165903/100000000000000 : ℝ), (43176375699947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1954219357/10000000000 : ℝ)|^2205 ≤ (11927467122731/100000000000000 : ℝ)^1693
        have hw : |(-1954219357/10000000000 : ℝ)|=(1954219357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407120433/10000000000 : ℝ)|^2205 ≤ (44896157165903/100000000000000 : ℝ)^1693
        have hw : |(5407120433/10000000000 : ℝ)|=(5407120433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623686007/5000000000 : ℝ)|^2205 ≤ (43176375699947/100000000000000 : ℝ)^1693
        have hw : |(2623686007/5000000000 : ℝ)|=(2623686007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s7_1 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668359093/1250000000 : ℝ)*x 0 + (-508883849/2500000000 : ℝ)*x 1 + (5247372009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668359093/1250000000 : ℝ)^2205 ≤ (22122863319667/50000000000000 : ℝ)^1693 := by
    have hnat : (668359093 : ℕ)^2205*50000000000000^1693 ≤ 22122863319667^1693*1250000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668359093 1250000000 22122863319667 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508883849/2500000000 : ℝ)^2205 ≤ (6288948850657/50000000000000 : ℝ)^1693 := by
    have hnat : (508883849 : ℕ)^2205*50000000000000^1693 ≤ 6288948850657^1693*2500000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508883849 2500000000 6288948850657 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247372009/10000000000 : ℝ)^2205 ≤ (10794093911591/25000000000000 : ℝ)^1693 := by
    have hnat : (5247372009 : ℕ)^2205*25000000000000^1693 ≤ 10794093911591^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247372009 10000000000 10794093911591 25000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668359093/1250000000 : ℝ), (-508883849/2500000000 : ℝ), (5247372009/10000000000 : ℝ)] ![(22122863319667/50000000000000 : ℝ), (6288948850657/50000000000000 : ℝ), (10794093911591/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668359093/1250000000 : ℝ)|^2205 ≤ (22122863319667/50000000000000 : ℝ)^1693
        have hw : |(668359093/1250000000 : ℝ)|=(668359093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-508883849/2500000000 : ℝ)|^2205 ≤ (6288948850657/50000000000000 : ℝ)^1693
        have hw : |(-508883849/2500000000 : ℝ)|=(508883849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247372009/10000000000 : ℝ)|^2205 ≤ (10794093911591/25000000000000 : ℝ)^1693
        have hw : |(5247372009/10000000000 : ℝ)|=(5247372009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s7_2 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668359093/1250000000 : ℝ)*x 0 + (5247372007/10000000000 : ℝ)*x 1 + (-2035535399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668359093/1250000000 : ℝ)^2205 ≤ (22122863319667/50000000000000 : ℝ)^1693 := by
    have hnat : (668359093 : ℕ)^2205*50000000000000^1693 ≤ 22122863319667^1693*1250000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668359093 1250000000 22122863319667 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247372007/10000000000 : ℝ)^2205 ≤ (43176375624931/100000000000000 : ℝ)^1693 := by
    have hnat : (5247372007 : ℕ)^2205*100000000000000^1693 ≤ 43176375624931^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247372007 10000000000 43176375624931 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2035535399/10000000000 : ℝ)^2205 ≤ (12577897725457/100000000000000 : ℝ)^1693 := by
    have hnat : (2035535399 : ℕ)^2205*100000000000000^1693 ≤ 12577897725457^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035535399 10000000000 12577897725457 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668359093/1250000000 : ℝ), (5247372007/10000000000 : ℝ), (-2035535399/10000000000 : ℝ)] ![(22122863319667/50000000000000 : ℝ), (43176375624931/100000000000000 : ℝ), (12577897725457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668359093/1250000000 : ℝ)|^2205 ≤ (22122863319667/50000000000000 : ℝ)^1693
        have hw : |(668359093/1250000000 : ℝ)|=(668359093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247372007/10000000000 : ℝ)|^2205 ≤ (43176375624931/100000000000000 : ℝ)^1693
        have hw : |(5247372007/10000000000 : ℝ)|=(5247372007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2035535399/10000000000 : ℝ)|^2205 ≤ (12577897725457/100000000000000 : ℝ)^1693
        have hw : |(-2035535399/10000000000 : ℝ)|=(2035535399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s7_3 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4299151107/10000000000 : ℝ)*x 0 + (4128169231/10000000000 : ℝ)*x 1 + (895283859/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299151107/10000000000 : ℝ)^2205 ≤ (33305017985317/100000000000000 : ℝ)^1693 := by
    have hnat : (4299151107 : ℕ)^2205*100000000000000^1693 ≤ 33305017985317^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299151107 10000000000 33305017985317 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4128169231/10000000000 : ℝ)^2205 ≤ (31590333164257/100000000000000 : ℝ)^1693 := by
    have hnat : (4128169231 : ℕ)^2205*100000000000000^1693 ≤ 31590333164257^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128169231 10000000000 31590333164257 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (895283859/2000000000 : ℝ)^2205 ≤ (8776162209283/25000000000000 : ℝ)^1693 := by
    have hnat : (895283859 : ℕ)^2205*25000000000000^1693 ≤ 8776162209283^1693*2000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895283859 2000000000 8776162209283 25000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299151107/10000000000 : ℝ), (4128169231/10000000000 : ℝ), (895283859/2000000000 : ℝ)] ![(33305017985317/100000000000000 : ℝ), (31590333164257/100000000000000 : ℝ), (8776162209283/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299151107/10000000000 : ℝ)|^2205 ≤ (33305017985317/100000000000000 : ℝ)^1693
        have hw : |(4299151107/10000000000 : ℝ)|=(4299151107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4128169231/10000000000 : ℝ)|^2205 ≤ (31590333164257/100000000000000 : ℝ)^1693
        have hw : |(4128169231/10000000000 : ℝ)|=(4128169231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(895283859/2000000000 : ℝ)|^2205 ≤ (8776162209283/25000000000000 : ℝ)^1693
        have hw : |(895283859/2000000000 : ℝ)|=(895283859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s7_4 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-977115241/5000000000 : ℝ)*x 0 + (524794913/1000000000 : ℝ)*x 1 + (5406540331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977115241/5000000000 : ℝ)^2205 ≤ (2385511111659/20000000000000 : ℝ)^1693 := by
    have hnat : (977115241 : ℕ)^2205*20000000000000^1693 ≤ 2385511111659^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977115241 5000000000 2385511111659 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524794913/1000000000 : ℝ)^2205 ≤ (43182560509089/100000000000000 : ℝ)^1693 := by
    have hnat : (524794913 : ℕ)^2205*100000000000000^1693 ≤ 43182560509089^1693*1000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524794913 1000000000 43182560509089 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406540331/10000000000 : ℝ)^2205 ≤ (44889883923349/100000000000000 : ℝ)^1693 := by
    have hnat : (5406540331 : ℕ)^2205*100000000000000^1693 ≤ 44889883923349^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406540331 10000000000 44889883923349 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-977115241/5000000000 : ℝ), (524794913/1000000000 : ℝ), (5406540331/10000000000 : ℝ)] ![(2385511111659/20000000000000 : ℝ), (43182560509089/100000000000000 : ℝ), (44889883923349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-977115241/5000000000 : ℝ)|^2205 ≤ (2385511111659/20000000000000 : ℝ)^1693
        have hw : |(-977115241/5000000000 : ℝ)|=(977115241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524794913/1000000000 : ℝ)|^2205 ≤ (43182560509089/100000000000000 : ℝ)^1693
        have hw : |(524794913/1000000000 : ℝ)|=(524794913/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406540331/10000000000 : ℝ)|^2205 ≤ (44889883923349/100000000000000 : ℝ)^1693
        have hw : |(5406540331/10000000000 : ℝ)|=(5406540331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s7_5 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (663157323/1250000000 : ℝ)*x 0 + (-1876367109/10000000000 : ℝ)*x 1 + (540654031/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663157323/1250000000 : ℝ)^2205 ≤ (43797753557161/100000000000000 : ℝ)^1693 := by
    have hnat : (663157323 : ℕ)^2205*100000000000000^1693 ≤ 43797753557161^1693*1250000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663157323 1250000000 43797753557161 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1876367109/10000000000 : ℝ)^2205 ≤ (5656181363763/50000000000000 : ℝ)^1693 := by
    have hnat : (1876367109 : ℕ)^2205*50000000000000^1693 ≤ 5656181363763^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876367109 10000000000 5656181363763 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540654031/1000000000 : ℝ)^2205 ≤ (22444941848129/50000000000000 : ℝ)^1693 := by
    have hnat : (540654031 : ℕ)^2205*50000000000000^1693 ≤ 22444941848129^1693*1000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540654031 1000000000 22444941848129 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663157323/1250000000 : ℝ), (-1876367109/10000000000 : ℝ), (540654031/1000000000 : ℝ)] ![(43797753557161/100000000000000 : ℝ), (5656181363763/50000000000000 : ℝ), (22444941848129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663157323/1250000000 : ℝ)|^2205 ≤ (43797753557161/100000000000000 : ℝ)^1693
        have hw : |(663157323/1250000000 : ℝ)|=(663157323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1876367109/10000000000 : ℝ)|^2205 ≤ (5656181363763/50000000000000 : ℝ)^1693
        have hw : |(-1876367109/10000000000 : ℝ)|=(1876367109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540654031/1000000000 : ℝ)|^2205 ≤ (22444941848129/50000000000000 : ℝ)^1693
        have hw : |(540654031/1000000000 : ℝ)|=(540654031/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s7_6 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652629297/5000000000 : ℝ)*x 0 + (5406540297/10000000000 : ℝ)*x 1 + (-1876367113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652629297/5000000000 : ℝ)^2205 ≤ (43797753664683/100000000000000 : ℝ)^1693 := by
    have hnat : (2652629297 : ℕ)^2205*100000000000000^1693 ≤ 43797753664683^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652629297 5000000000 43797753664683 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406540297/10000000000 : ℝ)^2205 ≤ (22444941777839/50000000000000 : ℝ)^1693 := by
    have hnat : (5406540297 : ℕ)^2205*50000000000000^1693 ≤ 22444941777839^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406540297 10000000000 22444941777839 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1876367113/10000000000 : ℝ)^2205 ≤ (5656181379467/50000000000000 : ℝ)^1693 := by
    have hnat : (1876367113 : ℕ)^2205*50000000000000^1693 ≤ 5656181379467^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876367113 10000000000 5656181379467 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652629297/5000000000 : ℝ), (5406540297/10000000000 : ℝ), (-1876367113/10000000000 : ℝ)] ![(43797753664683/100000000000000 : ℝ), (22444941777839/50000000000000 : ℝ), (5656181379467/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652629297/5000000000 : ℝ)|^2205 ≤ (43797753664683/100000000000000 : ℝ)^1693
        have hw : |(2652629297/5000000000 : ℝ)|=(2652629297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406540297/10000000000 : ℝ)|^2205 ≤ (22444941777839/50000000000000 : ℝ)^1693
        have hw : |(5406540297/10000000000 : ℝ)|=(5406540297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1876367113/10000000000 : ℝ)|^2205 ≤ (5656181379467/50000000000000 : ℝ)^1693
        have hw : |(-1876367113/10000000000 : ℝ)|=(1876367113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s7_7 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (268698461/625000000 : ℝ)*x 0 + (2237580569/5000000000 : ℝ)*x 1 + (2064716951/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268698461/625000000 : ℝ)^2205 ≤ (666105257053/2000000000000 : ℝ)^1693 := by
    have hnat : (268698461 : ℕ)^2205*2000000000000^1693 ≤ 666105257053^1693*625000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268698461 625000000 666105257053 2000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237580569/5000000000 : ℝ)^2205 ≤ (17545899436893/50000000000000 : ℝ)^1693 := by
    have hnat : (2237580569 : ℕ)^2205*50000000000000^1693 ≤ 17545899436893^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237580569 5000000000 17545899436893 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064716951/5000000000 : ℝ)^2205 ≤ (31602938256423/100000000000000 : ℝ)^1693 := by
    have hnat : (2064716951 : ℕ)^2205*100000000000000^1693 ≤ 31602938256423^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064716951 5000000000 31602938256423 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268698461/625000000 : ℝ), (2237580569/5000000000 : ℝ), (2064716951/5000000000 : ℝ)] ![(666105257053/2000000000000 : ℝ), (17545899436893/50000000000000 : ℝ), (31602938256423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268698461/625000000 : ℝ)|^2205 ≤ (666105257053/2000000000000 : ℝ)^1693
        have hw : |(268698461/625000000 : ℝ)|=(268698461/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2237580569/5000000000 : ℝ)|^2205 ≤ (17545899436893/50000000000000 : ℝ)^1693
        have hw : |(2237580569/5000000000 : ℝ)|=(2237580569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2064716951/5000000000 : ℝ)|^2205 ≤ (31602938256423/100000000000000 : ℝ)^1693
        have hw : |(2064716951/5000000000 : ℝ)|=(2064716951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1450_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39749881/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5691/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11383/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14767/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5691/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5691/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5691/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5691/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5691/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5691/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5691/50000 : ℝ) ^ (4409/1024 : ℝ) ≤ (8637623352762797/100000000000000000000 : ℝ) := by
    have hpowers : (5691/50000 : ℝ)^4409 ≤ (8637623352762797/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5691 : ℕ)^4409*100000000000000000000^1024 ≤ 8637623352762797^1024*50000^4409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5691 50000 8637623352762797 100000000000000000000 4409 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5691/50000 : ℝ)) (X := (8637623352762797/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (923/6250 : ℝ) ^ (4409/1024 : ℝ) ≤ (6627019287876903/25000000000000000000 : ℝ) := by
    have hpowers : (923/6250 : ℝ)^4409 ≤ (6627019287876903/25000000000000000000 : ℝ)^1024 := by
      have hnat : (923 : ℕ)^4409*25000000000000000000^1024 ≤ 6627019287876903^1024*6250^4409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        923 6250 6627019287876903 25000000000000000000 4409 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (923/6250 : ℝ)) (X := (6627019287876903/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008637623352762797/50000000000000000000 : ℝ) ≤ (2500100298705151/2500000000000000 : ℝ) ^ (4409/1024 : ℝ) := by
    have hpowers : (50008637623352762797/50000000000000000000 : ℝ)^1024 ≤ (2500100298705151/2500000000000000 : ℝ)^4409 := by
      have hnat : (50008637623352762797 : ℕ)^1024*2500000000000000^4409 ≤ 2500100298705151^4409*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008637623352762797 50000000000000000000 2500100298705151 2500000000000000 1024 4409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500100298705151/2500000000000000 : ℝ)) (X := (50008637623352762797/50000000000000000000 : ℝ)) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035145700504270409/100000000000000000000 : ℝ) ≤ (1250102019570291/1250000000000000 : ℝ) ^ (4409/1024 : ℝ) := by
    have hpowers : (100035145700504270409/100000000000000000000 : ℝ)^1024 ≤ (1250102019570291/1250000000000000 : ℝ)^4409 := by
      have hnat : (100035145700504270409 : ℕ)^1024*1250000000000000^4409 ≤ 1250102019570291^4409*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035145700504270409 100000000000000000000 1250102019570291 1250000000000000 1024 4409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250102019570291/1250000000000000 : ℝ)) (X := (100035145700504270409/100000000000000000000 : ℝ)) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506627019287876903/12500000000000000000 : ℝ) ≤ (2500307779576013/2500000000000000 : ℝ) ^ (4409/1024 : ℝ) := by
    have hpowers : (12506627019287876903/12500000000000000000 : ℝ)^1024 ≤ (2500307779576013/2500000000000000 : ℝ)^4409 := by
      have hnat : (12506627019287876903 : ℕ)^1024*2500000000000000^4409 ≤ 2500307779576013^4409*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506627019287876903 12500000000000000000 2500307779576013 2500000000000000 1024 4409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500307779576013/2500000000000000 : ℝ)) (X := (12506627019287876903/12500000000000000000 : ℝ)) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8637623352762797/100000000000000000000 : ℝ) ≤ ((4231489032071745001/4232500000000000000 : ℝ)+2*(103740435431/84650000000000 : ℝ)*(5691/50000 : ℝ))^(4409/1024 : ℝ) := by
    rw [show (4231489032071745001/4232500000000000000 : ℝ)+2*(103740435431/84650000000000 : ℝ)*(5691/50000 : ℝ)=(2500100298705151/2500000000000000 : ℝ) by norm_num, show 1+2*(8637623352762797/100000000000000000000 : ℝ)=(50008637623352762797/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6627019287876903/25000000000000000000 : ℝ)+(8637623352762797/100000000000000000000 : ℝ) ≤ ((4231489032071745001/4232500000000000000 : ℝ)+(103740435431/84650000000000 : ℝ)*((923/6250 : ℝ)+(5691/50000 : ℝ)))^(4409/1024 : ℝ) := by
    rw [show (4231489032071745001/4232500000000000000 : ℝ)+(103740435431/84650000000000 : ℝ)*((923/6250 : ℝ)+(5691/50000 : ℝ))=(1250102019570291/1250000000000000 : ℝ) by norm_num, show 1+(6627019287876903/25000000000000000000 : ℝ)+(8637623352762797/100000000000000000000 : ℝ)=(100035145700504270409/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6627019287876903/25000000000000000000 : ℝ) ≤ ((4231489032071745001/4232500000000000000 : ℝ)+2*(103740435431/84650000000000 : ℝ)*(923/6250 : ℝ))^(4409/1024 : ℝ) := by
    rw [show (4231489032071745001/4232500000000000000 : ℝ)+2*(103740435431/84650000000000 : ℝ)*(923/6250 : ℝ)=(2500307779576013/2500000000000000 : ℝ) by norm_num, show 1+2*(6627019287876903/25000000000000000000 : ℝ)=(12506627019287876903/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4231489032071745001/4232500000000000000 : ℝ)*(X 1 0+X 2 0)+(103740435431/84650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4409/1024 : ℝ)) (lo := (5691/50000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (4231489032071745001/4232500000000000000 : ℝ)) (alpha := (103740435431/84650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4231489032071745001/4232500000000000000 : ℝ)*(X 0 1+X 2 1)+(103740435431/84650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4409/1024 : ℝ)) (lo := (5691/50000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (4231489032071745001/4232500000000000000 : ℝ)) (alpha := (103740435431/84650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4231489032071745001/4232500000000000000 : ℝ)*(X 0 2+X 1 2)+(103740435431/84650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4409/1024 : ℝ)) (lo := (5691/50000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (4231489032071745001/4232500000000000000 : ℝ)) (alpha := (103740435431/84650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1954219357/10000000000 : ℝ)*X 0 0+(5407120433/10000000000 : ℝ)*X 0 1+(2623686007/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668359093/1250000000 : ℝ)*X 1 0+(-508883849/2500000000 : ℝ)*X 1 1+(5247372009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668359093/1250000000 : ℝ)*X 2 0+(5247372007/10000000000 : ℝ)*X 2 1+(-2035535399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4299151107/10000000000 : ℝ)*X 0 0+(4128169231/10000000000 : ℝ)*X 0 1+(895283859/2000000000 : ℝ)*X 0 2+(4299151107/10000000000 : ℝ)*X 1 0+(4128169231/10000000000 : ℝ)*X 1 1+(895283859/2000000000 : ℝ)*X 1 2+(4299151107/10000000000 : ℝ)*X 2 0+(4128169231/10000000000 : ℝ)*X 2 1+(895283859/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-977115241/5000000000 : ℝ)*X 0 0+(524794913/1000000000 : ℝ)*X 0 1+(5406540331/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663157323/1250000000 : ℝ)*X 1 0+(-1876367109/10000000000 : ℝ)*X 1 1+(540654031/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652629297/5000000000 : ℝ)*X 2 0+(5406540297/10000000000 : ℝ)*X 2 1+(-1876367113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((268698461/625000000 : ℝ)*X 0 0+(2237580569/5000000000 : ℝ)*X 0 1+(2064716951/5000000000 : ℝ)*X 0 2+(268698461/625000000 : ℝ)*X 1 0+(2237580569/5000000000 : ℝ)*X 1 1+(2064716951/5000000000 : ℝ)*X 1 2+(268698461/625000000 : ℝ)*X 2 0+(2237580569/5000000000 : ℝ)*X 2 1+(2064716951/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (714068772010440733049267421/211625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (610466387/100000000000000 : ℝ)*(base19) + (69109749/12500000000000 : ℝ)*(base23) + (3848973/12500000000000 : ℝ)*(lower2) + (87592277/100000000000000 : ℝ)*(upper3) + (5270833/12500000000000 : ℝ)*(upper5) + (4565690532984193/100000000000000 : ℝ)*(major0) + (4565690532984193/100000000000000 : ℝ)*(major1) + (4565690532984193/100000000000000 : ℝ)*(major2) + (195620510903821/3125000000000 : ℝ)*(sp0) + (6259868266687399/100000000000000 : ℝ)*(sp1) + (3129934162137897/50000000000000 : ℝ)*(sp2) + (358938184116501/12500000000000 : ℝ)*(sp3) + (6264115757/50000000000000 : ℝ)*(sp4) + (1650852167/25000000000000 : ℝ)*(sp7) + (2871512076340677/100000000000000 : ℝ)*(f.failure) + (3129934438576893/50000000000000 : ℝ)*(f.sum) + (9291286766693/4232500000000000000000000000 : ℝ)*base65 + (3660058906767919193/423250000000000000000000000000000 : ℝ)*base67 + (4200723870135419193/423250000000000000000000000000000 : ℝ)*base69 + (540353770891080807/423250000000000000000000000000000 : ℝ)*base72 + (25383032286173/4232500000000000000000000000 : ℝ)*base73 + (4638648942696169193/423250000000000000000000000000000 : ℝ)*base75 + (8095552090398919193/423250000000000000000000000000000 : ℝ)*base77 + (1075444921148580807/423250000000000000000000000000000 : ℝ)*base80 + (4875337099379/2116250000000000000000000000 : ℝ)*base81 + (1209437/2500000000000000000000 : ℝ)*base89 + (1209437/2500000000000000000000 : ℝ)*base91 + (1209437/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23180462735657415021417/4232500000000000000000000000 : ℝ) := by norm_num
    linear_combination (431922791/50000000000000 : ℝ)*(base19) + (195743159/20000000000000 : ℝ)*(base23) + (35902651/12500000000000 : ℝ)*(lower1) + (48170619/50000000000000 : ℝ)*(upper3) + (49353507/100000000000000 : ℝ)*(lower4) + (58478853/50000000000000 : ℝ)*(upper5) + (4598973297944859/100000000000000 : ℝ)*(major0) + (4598973297944859/100000000000000 : ℝ)*(major1) + (4598973297944859/100000000000000 : ℝ)*(major2) + (1269424621/100000000000000 : ℝ)*(sp2) + (1261100343548901/20000000000000 : ℝ)*(sp4) + (6305500853898923/100000000000000 : ℝ)*(sp5) + (6305499469604089/100000000000000 : ℝ)*(sp6) + (1446222347792959/50000000000000 : ℝ)*(sp7) + (1446222347792959/50000000000000 : ℝ)*(f.failure) + (1261100343548901/20000000000000 : ℝ)*(f.sum) + (2927491940753/2116250000000000000000000000 : ℝ)*base66 + (12832893857447150141/423250000000000000000000000000000 : ℝ)*base68 + (2000563569577599859/423250000000000000000000000000000 : ℝ)*base69 + (35665273769481650141/423250000000000000000000000000000 : ℝ)*base72 + (36989369231653/8465000000000000000000000000 : ℝ)*base73 + (59888908376408849859/423250000000000000000000000000000 : ℝ)*base75 + (1982241306380150141/423250000000000000000000000000000 : ℝ)*base78 + (2205420686530349859/423250000000000000000000000000000 : ℝ)*base79 + (803302307271/4232500000000000000000000000 : ℝ)*base82 + (4612121/1250000000000000000000 : ℝ)*base90 + (4612121/1250000000000000000000 : ℝ)*base92 + (4612121/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1450_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39749881/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5691/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1450_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1450_box_0 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-359012379/2000000000 : ℝ)*x 0 + (5385354189/10000000000 : ℝ)*x 1 + (2692677011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (359012379/2000000000 : ℝ)^2205 ≤ (10678170062147/100000000000000 : ℝ)^1693 := by
    have hnat : (359012379 : ℕ)^2205*100000000000000^1693 ≤ 10678170062147^1693*2000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359012379 2000000000 10678170062147 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385354189/10000000000 : ℝ)^2205 ≤ (22330457932043/50000000000000 : ℝ)^1693 := by
    have hnat : (5385354189 : ℕ)^2205*50000000000000^1693 ≤ 22330457932043^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385354189 10000000000 22330457932043 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692677011/5000000000 : ℝ)^2205 ≤ (22330457030157/50000000000000 : ℝ)^1693 := by
    have hnat : (2692677011 : ℕ)^2205*50000000000000^1693 ≤ 22330457030157^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692677011 5000000000 22330457030157 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-359012379/2000000000 : ℝ), (5385354189/10000000000 : ℝ), (2692677011/5000000000 : ℝ)] ![(10678170062147/100000000000000 : ℝ), (22330457932043/50000000000000 : ℝ), (22330457030157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-359012379/2000000000 : ℝ)|^2205 ≤ (10678170062147/100000000000000 : ℝ)^1693
        have hw : |(-359012379/2000000000 : ℝ)|=(359012379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385354189/10000000000 : ℝ)|^2205 ≤ (22330457932043/50000000000000 : ℝ)^1693
        have hw : |(5385354189/10000000000 : ℝ)|=(5385354189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692677011/5000000000 : ℝ)|^2205 ≤ (22330457030157/50000000000000 : ℝ)^1693
        have hw : |(2692677011/5000000000 : ℝ)|=(2692677011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_box_1 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2643099763/5000000000 : ℝ)*x 0 + (-1931369283/10000000000 : ℝ)*x 1 + (2692676989/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643099763/5000000000 : ℝ)^2205 ≤ (8718587673119/20000000000000 : ℝ)^1693 := by
    have hnat : (2643099763 : ℕ)^2205*20000000000000^1693 ≤ 8718587673119^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643099763 5000000000 8718587673119 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1931369283/10000000000 : ℝ)^2205 ≤ (2936537008969/25000000000000 : ℝ)^1693 := by
    have hnat : (1931369283 : ℕ)^2205*25000000000000^1693 ≤ 2936537008969^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931369283 10000000000 2936537008969 25000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692676989/5000000000 : ℝ)^2205 ≤ (44660913585069/100000000000000 : ℝ)^1693 := by
    have hnat : (2692676989 : ℕ)^2205*100000000000000^1693 ≤ 44660913585069^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692676989 5000000000 44660913585069 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643099763/5000000000 : ℝ), (-1931369283/10000000000 : ℝ), (2692676989/5000000000 : ℝ)] ![(8718587673119/20000000000000 : ℝ), (2936537008969/25000000000000 : ℝ), (44660913585069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643099763/5000000000 : ℝ)|^2205 ≤ (8718587673119/20000000000000 : ℝ)^1693
        have hw : |(2643099763/5000000000 : ℝ)|=(2643099763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1931369283/10000000000 : ℝ)|^2205 ≤ (2936537008969/25000000000000 : ℝ)^1693
        have hw : |(-1931369283/10000000000 : ℝ)|=(1931369283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692676989/5000000000 : ℝ)|^2205 ≤ (44660913585069/100000000000000 : ℝ)^1693
        have hw : |(2692676989/5000000000 : ℝ)|=(2692676989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_box_2 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5286199357/10000000000 : ℝ)*x 0 + (5385354189/10000000000 : ℝ)*x 1 + (-1931369223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286199357/10000000000 : ℝ)^2205 ≤ (10898234137613/25000000000000 : ℝ)^1693 := by
    have hnat : (5286199357 : ℕ)^2205*25000000000000^1693 ≤ 10898234137613^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286199357 10000000000 10898234137613 25000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385354189/10000000000 : ℝ)^2205 ≤ (22330457932043/50000000000000 : ℝ)^1693 := by
    have hnat : (5385354189 : ℕ)^2205*50000000000000^1693 ≤ 22330457932043^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385354189 10000000000 22330457932043 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1931369223/10000000000 : ℝ)^2205 ≤ (5873073780307/50000000000000 : ℝ)^1693 := by
    have hnat : (1931369223 : ℕ)^2205*50000000000000^1693 ≤ 5873073780307^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931369223 10000000000 5873073780307 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286199357/10000000000 : ℝ), (5385354189/10000000000 : ℝ), (-1931369223/10000000000 : ℝ)] ![(10898234137613/25000000000000 : ℝ), (22330457932043/50000000000000 : ℝ), (5873073780307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286199357/10000000000 : ℝ)|^2205 ≤ (10898234137613/25000000000000 : ℝ)^1693
        have hw : |(5286199357/10000000000 : ℝ)|=(5286199357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385354189/10000000000 : ℝ)|^2205 ≤ (22330457932043/50000000000000 : ℝ)^1693
        have hw : |(5385354189/10000000000 : ℝ)|=(5385354189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1931369223/10000000000 : ℝ)|^2205 ≤ (5873073780307/50000000000000 : ℝ)^1693
        have hw : |(-1931369223/10000000000 : ℝ)|=(1931369223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_box_3 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (222251751/500000000 : ℝ)*x 0 + (422987799/1000000000 : ℝ)*x 1 + (4229877829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (222251751/500000000 : ℝ)^2205 ≤ (34784437872991/100000000000000 : ℝ)^1693 := by
    have hnat : (222251751 : ℕ)^2205*100000000000000^1693 ≤ 34784437872991^1693*500000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222251751 500000000 34784437872991 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422987799/1000000000 : ℝ)^2205 ≤ (32607781861787/100000000000000 : ℝ)^1693 := by
    have hnat : (422987799 : ℕ)^2205*100000000000000^1693 ≤ 32607781861787^1693*1000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422987799 1000000000 32607781861787 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229877829/10000000000 : ℝ)^2205 ≤ (6521556049061/20000000000000 : ℝ)^1693 := by
    have hnat : (4229877829 : ℕ)^2205*20000000000000^1693 ≤ 6521556049061^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229877829 10000000000 6521556049061 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(222251751/500000000 : ℝ), (422987799/1000000000 : ℝ), (4229877829/10000000000 : ℝ)] ![(34784437872991/100000000000000 : ℝ), (32607781861787/100000000000000 : ℝ), (6521556049061/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(222251751/500000000 : ℝ)|^2205 ≤ (34784437872991/100000000000000 : ℝ)^1693
        have hw : |(222251751/500000000 : ℝ)|=(222251751/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(422987799/1000000000 : ℝ)|^2205 ≤ (32607781861787/100000000000000 : ℝ)^1693
        have hw : |(422987799/1000000000 : ℝ)|=(422987799/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229877829/10000000000 : ℝ)|^2205 ≤ (6521556049061/20000000000000 : ℝ)^1693
        have hw : |(4229877829/10000000000 : ℝ)|=(4229877829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_box_4 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1058054219/5000000000 : ℝ)*x 0 + (263340993/500000000 : ℝ)*x 1 + (5266819989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058054219/5000000000 : ℝ)^2205 ≤ (13230185246919/100000000000000 : ℝ)^1693 := by
    have hnat : (1058054219 : ℕ)^2205*100000000000000^1693 ≤ 13230185246919^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058054219 5000000000 13230185246919 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263340993/500000000 : ℝ)^2205 ≤ (1355778333703/3125000000000 : ℝ)^1693 := by
    have hnat : (263340993 : ℕ)^2205*3125000000000^1693 ≤ 1355778333703^1693*500000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263340993 500000000 1355778333703 3125000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266819989/10000000000 : ℝ)^2205 ≤ (43384908062481/100000000000000 : ℝ)^1693 := by
    have hnat : (5266819989 : ℕ)^2205*100000000000000^1693 ≤ 43384908062481^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266819989 10000000000 43384908062481 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1058054219/5000000000 : ℝ), (263340993/500000000 : ℝ), (5266819989/10000000000 : ℝ)] ![(13230185246919/100000000000000 : ℝ), (1355778333703/3125000000000 : ℝ), (43384908062481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1058054219/5000000000 : ℝ)|^2205 ≤ (13230185246919/100000000000000 : ℝ)^1693
        have hw : |(-1058054219/5000000000 : ℝ)|=(1058054219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263340993/500000000 : ℝ)|^2205 ≤ (1355778333703/3125000000000 : ℝ)^1693
        have hw : |(263340993/500000000 : ℝ)|=(263340993/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266819989/10000000000 : ℝ)|^2205 ≤ (43384908062481/100000000000000 : ℝ)^1693
        have hw : |(5266819989/10000000000 : ℝ)|=(5266819989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_box_5 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5369084959/10000000000 : ℝ)*x 0 + (-123726579/625000000 : ℝ)*x 1 + (5266819901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369084959/10000000000 : ℝ)^2205 ≤ (11121317956527/25000000000000 : ℝ)^1693 := by
    have hnat : (5369084959 : ℕ)^2205*25000000000000^1693 ≤ 11121317956527^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369084959 10000000000 11121317956527 25000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123726579/625000000 : ℝ)^2205 ≤ (6064910517037/50000000000000 : ℝ)^1693 := by
    have hnat : (123726579 : ℕ)^2205*50000000000000^1693 ≤ 6064910517037^1693*625000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123726579 625000000 6064910517037 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266819901/10000000000 : ℝ)^2205 ≤ (43384907118367/100000000000000 : ℝ)^1693 := by
    have hnat : (5266819901 : ℕ)^2205*100000000000000^1693 ≤ 43384907118367^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266819901 10000000000 43384907118367 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369084959/10000000000 : ℝ), (-123726579/625000000 : ℝ), (5266819901/10000000000 : ℝ)] ![(11121317956527/25000000000000 : ℝ), (6064910517037/50000000000000 : ℝ), (43384907118367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369084959/10000000000 : ℝ)|^2205 ≤ (11121317956527/25000000000000 : ℝ)^1693
        have hw : |(5369084959/10000000000 : ℝ)|=(5369084959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-123726579/625000000 : ℝ)|^2205 ≤ (6064910517037/50000000000000 : ℝ)^1693
        have hw : |(-123726579/625000000 : ℝ)|=(123726579/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266819901/10000000000 : ℝ)|^2205 ≤ (43384907118367/100000000000000 : ℝ)^1693
        have hw : |(5266819901/10000000000 : ℝ)|=(5266819901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_box_6 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (671135601/1250000000 : ℝ)*x 0 + (5266820079/10000000000 : ℝ)*x 1 + (-197962523/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671135601/1250000000 : ℝ)^2205 ≤ (8897054039329/20000000000000 : ℝ)^1693 := by
    have hnat : (671135601 : ℕ)^2205*20000000000000^1693 ≤ 8897054039329^1693*1250000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671135601 1250000000 8897054039329 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266820079/10000000000 : ℝ)^2205 ≤ (43384909028053/100000000000000 : ℝ)^1693 := by
    have hnat : (5266820079 : ℕ)^2205*100000000000000^1693 ≤ 43384909028053^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266820079 10000000000 43384909028053 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197962523/1000000000 : ℝ)^2205 ≤ (6064910381371/50000000000000 : ℝ)^1693 := by
    have hnat : (197962523 : ℕ)^2205*50000000000000^1693 ≤ 6064910381371^1693*1000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197962523 1000000000 6064910381371 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671135601/1250000000 : ℝ), (5266820079/10000000000 : ℝ), (-197962523/1000000000 : ℝ)] ![(8897054039329/20000000000000 : ℝ), (43384909028053/100000000000000 : ℝ), (6064910381371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671135601/1250000000 : ℝ)|^2205 ≤ (8897054039329/20000000000000 : ℝ)^1693
        have hw : |(671135601/1250000000 : ℝ)|=(671135601/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266820079/10000000000 : ℝ)|^2205 ≤ (43384909028053/100000000000000 : ℝ)^1693
        have hw : |(5266820079/10000000000 : ℝ)|=(5266820079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-197962523/1000000000 : ℝ)|^2205 ≤ (6064910381371/50000000000000 : ℝ)^1693
        have hw : |(-197962523/1000000000 : ℝ)|=(197962523/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_box_7 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1038047749/2500000000 : ℝ)*x 0 + (10940623/25000000 : ℝ)*x 1 + (109406251/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038047749/2500000000 : ℝ)^2205 ≤ (7957489897957/25000000000000 : ℝ)^1693 := by
    have hnat : (1038047749 : ℕ)^2205*25000000000000^1693 ≤ 7957489897957^1693*2500000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038047749 2500000000 7957489897957 25000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10940623/25000000 : ℝ)^2205 ≤ (17042507968473/50000000000000 : ℝ)^1693 := by
    have hnat : (10940623 : ℕ)^2205*50000000000000^1693 ≤ 17042507968473^1693*25000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10940623 25000000 17042507968473 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109406251/250000000 : ℝ)^2205 ≤ (17042512228991/50000000000000 : ℝ)^1693 := by
    have hnat : (109406251 : ℕ)^2205*50000000000000^1693 ≤ 17042512228991^1693*250000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109406251 250000000 17042512228991 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038047749/2500000000 : ℝ), (10940623/25000000 : ℝ), (109406251/250000000 : ℝ)] ![(7957489897957/25000000000000 : ℝ), (17042507968473/50000000000000 : ℝ), (17042512228991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038047749/2500000000 : ℝ)|^2205 ≤ (7957489897957/25000000000000 : ℝ)^1693
        have hw : |(1038047749/2500000000 : ℝ)|=(1038047749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10940623/25000000 : ℝ)|^2205 ≤ (17042507968473/50000000000000 : ℝ)^1693
        have hw : |(10940623/25000000 : ℝ)|=(10940623/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109406251/250000000 : ℝ)|^2205 ≤ (17042512228991/50000000000000 : ℝ)^1693
        have hw : |(109406251/250000000 : ℝ)|=(109406251/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_box_8 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1024221029/5000000000 : ℝ)*x 0 + (1296184519/2500000000 : ℝ)*x 1 + (5399314661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1024221029/5000000000 : ℝ)^2205 ≤ (2536373660399/20000000000000 : ℝ)^1693 := by
    have hnat : (1024221029 : ℕ)^2205*20000000000000^1693 ≤ 2536373660399^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024221029 5000000000 2536373660399 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296184519/2500000000 : ℝ)^2205 ≤ (21253184666099/50000000000000 : ℝ)^1693 := by
    have hnat : (1296184519 : ℕ)^2205*50000000000000^1693 ≤ 21253184666099^1693*2500000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296184519 2500000000 21253184666099 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399314661/10000000000 : ℝ)^2205 ≤ (44811762348037/100000000000000 : ℝ)^1693 := by
    have hnat : (5399314661 : ℕ)^2205*100000000000000^1693 ≤ 44811762348037^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399314661 10000000000 44811762348037 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1024221029/5000000000 : ℝ), (1296184519/2500000000 : ℝ), (5399314661/10000000000 : ℝ)] ![(2536373660399/20000000000000 : ℝ), (21253184666099/50000000000000 : ℝ), (44811762348037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1024221029/5000000000 : ℝ)|^2205 ≤ (2536373660399/20000000000000 : ℝ)^1693
        have hw : |(-1024221029/5000000000 : ℝ)|=(1024221029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296184519/2500000000 : ℝ)|^2205 ≤ (21253184666099/50000000000000 : ℝ)^1693
        have hw : |(1296184519/2500000000 : ℝ)|=(1296184519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399314661/10000000000 : ℝ)|^2205 ≤ (44811762348037/100000000000000 : ℝ)^1693
        have hw : |(5399314661/10000000000 : ℝ)|=(5399314661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_box_9 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2638216947/5000000000 : ℝ)*x 0 + (-962780349/5000000000 : ℝ)*x 1 + (5399314539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638216947/5000000000 : ℝ)^2205 ≤ (21744039986549/50000000000000 : ℝ)^1693 := by
    have hnat : (2638216947 : ℕ)^2205*50000000000000^1693 ≤ 21744039986549^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638216947 5000000000 21744039986549 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (962780349/5000000000 : ℝ)^2205 ≤ (11700158984759/100000000000000 : ℝ)^1693 := by
    have hnat : (962780349 : ℕ)^2205*100000000000000^1693 ≤ 11700158984759^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962780349 5000000000 11700158984759 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399314539/10000000000 : ℝ)^2205 ≤ (280073506433/625000000000 : ℝ)^1693 := by
    have hnat : (5399314539 : ℕ)^2205*625000000000^1693 ≤ 280073506433^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399314539 10000000000 280073506433 625000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638216947/5000000000 : ℝ), (-962780349/5000000000 : ℝ), (5399314539/10000000000 : ℝ)] ![(21744039986549/50000000000000 : ℝ), (11700158984759/100000000000000 : ℝ), (280073506433/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638216947/5000000000 : ℝ)|^2205 ≤ (21744039986549/50000000000000 : ℝ)^1693
        have hw : |(2638216947/5000000000 : ℝ)|=(2638216947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-962780349/5000000000 : ℝ)|^2205 ≤ (11700158984759/100000000000000 : ℝ)^1693
        have hw : |(-962780349/5000000000 : ℝ)|=(962780349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399314539/10000000000 : ℝ)|^2205 ≤ (280073506433/625000000000 : ℝ)^1693
        have hw : |(5399314539/10000000000 : ℝ)|=(5399314539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_box_10 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (164888553/312500000 : ℝ)*x 0 + (2699657313/5000000000 : ℝ)*x 1 + (-1925560847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164888553/312500000 : ℝ)^2205 ≤ (43488077847669/100000000000000 : ℝ)^1693 := by
    have hnat : (164888553 : ℕ)^2205*100000000000000^1693 ≤ 43488077847669^1693*312500000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164888553 312500000 43488077847669 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699657313/5000000000 : ℝ)^2205 ≤ (8962352393941/20000000000000 : ℝ)^1693 := by
    have hnat : (2699657313 : ℕ)^2205*20000000000000^1693 ≤ 8962352393941^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699657313 5000000000 8962352393941 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1925560847/10000000000 : ℝ)^2205 ≤ (5850080081959/50000000000000 : ℝ)^1693 := by
    have hnat : (1925560847 : ℕ)^2205*50000000000000^1693 ≤ 5850080081959^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925560847 10000000000 5850080081959 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164888553/312500000 : ℝ), (2699657313/5000000000 : ℝ), (-1925560847/10000000000 : ℝ)] ![(43488077847669/100000000000000 : ℝ), (8962352393941/20000000000000 : ℝ), (5850080081959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164888553/312500000 : ℝ)|^2205 ≤ (43488077847669/100000000000000 : ℝ)^1693
        have hw : |(164888553/312500000 : ℝ)|=(164888553/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699657313/5000000000 : ℝ)|^2205 ≤ (8962352393941/20000000000000 : ℝ)^1693
        have hw : |(2699657313/5000000000 : ℝ)|=(2699657313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1925560847/10000000000 : ℝ)|^2205 ≤ (5850080081959/50000000000000 : ℝ)^1693
        have hw : |(-1925560847/10000000000 : ℝ)|=(1925560847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_box_11 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (111974223/250000000 : ℝ)*x 0 + (2106311979/5000000000 : ℝ)*x 1 + (4212623961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (111974223/250000000 : ℝ)^2205 ≤ (2195668270571/6250000000000 : ℝ)^1693 := by
    have hnat : (111974223 : ℕ)^2205*6250000000000^1693 ≤ 2195668270571^1693*250000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111974223 250000000 2195668270571 6250000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2106311979/5000000000 : ℝ)^2205 ≤ (32434653810599/100000000000000 : ℝ)^1693 := by
    have hnat : (2106311979 : ℕ)^2205*100000000000000^1693 ≤ 32434653810599^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106311979 5000000000 32434653810599 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4212623961/10000000000 : ℝ)^2205 ≤ (32434653840683/100000000000000 : ℝ)^1693 := by
    have hnat : (4212623961 : ℕ)^2205*100000000000000^1693 ≤ 32434653840683^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212623961 10000000000 32434653840683 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(111974223/250000000 : ℝ), (2106311979/5000000000 : ℝ), (4212623961/10000000000 : ℝ)] ![(2195668270571/6250000000000 : ℝ), (32434653810599/100000000000000 : ℝ), (32434653840683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(111974223/250000000 : ℝ)|^2205 ≤ (2195668270571/6250000000000 : ℝ)^1693
        have hw : |(111974223/250000000 : ℝ)|=(111974223/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2106311979/5000000000 : ℝ)|^2205 ≤ (32434653810599/100000000000000 : ℝ)^1693
        have hw : |(2106311979/5000000000 : ℝ)|=(2106311979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4212623961/10000000000 : ℝ)|^2205 ≤ (32434653840683/100000000000000 : ℝ)^1693
        have hw : |(4212623961/10000000000 : ℝ)|=(4212623961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_box_12 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1862874029/10000000000 : ℝ)*x 0 + (5465452251/10000000000 : ℝ)*x 1 + (164240131/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1862874029/10000000000 : ℝ)^2205 ≤ (2801632197507/25000000000000 : ℝ)^1693 := by
    have hnat : (1862874029 : ℕ)^2205*25000000000000^1693 ≤ 2801632197507^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862874029 10000000000 2801632197507 25000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465452251/10000000000 : ℝ)^2205 ≤ (45527996090781/100000000000000 : ℝ)^1693 := by
    have hnat : (5465452251 : ℕ)^2205*100000000000000^1693 ≤ 45527996090781^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465452251 10000000000 45527996090781 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164240131/312500000 : ℝ)^2205 ≤ (43265475098971/100000000000000 : ℝ)^1693 := by
    have hnat : (164240131 : ℕ)^2205*100000000000000^1693 ≤ 43265475098971^1693*312500000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164240131 312500000 43265475098971 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1862874029/10000000000 : ℝ), (5465452251/10000000000 : ℝ), (164240131/312500000 : ℝ)] ![(2801632197507/25000000000000 : ℝ), (45527996090781/100000000000000 : ℝ), (43265475098971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1862874029/10000000000 : ℝ)|^2205 ≤ (2801632197507/25000000000000 : ℝ)^1693
        have hw : |(-1862874029/10000000000 : ℝ)|=(1862874029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465452251/10000000000 : ℝ)|^2205 ≤ (45527996090781/100000000000000 : ℝ)^1693
        have hw : |(5465452251/10000000000 : ℝ)|=(5465452251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164240131/312500000 : ℝ)|^2205 ≤ (43265475098971/100000000000000 : ℝ)^1693
        have hw : |(164240131/312500000 : ℝ)|=(164240131/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_box_13 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1344217549/2500000000 : ℝ)*x 0 + (-1984059787/10000000000 : ℝ)*x 1 + (328480267/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344217549/2500000000 : ℝ)^2205 ≤ (4456930187689/10000000000000 : ℝ)^1693 := by
    have hnat : (1344217549 : ℕ)^2205*10000000000000^1693 ≤ 4456930187689^1693*2500000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344217549 2500000000 4456930187689 10000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1984059787/10000000000 : ℝ)^2205 ≤ (6082611075231/50000000000000 : ℝ)^1693 := by
    have hnat : (1984059787 : ℕ)^2205*50000000000000^1693 ≤ 6082611075231^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984059787 10000000000 6082611075231 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328480267/625000000 : ℝ)^2205 ≤ (43265475956707/100000000000000 : ℝ)^1693 := by
    have hnat : (328480267 : ℕ)^2205*100000000000000^1693 ≤ 43265475956707^1693*625000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328480267 625000000 43265475956707 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344217549/2500000000 : ℝ), (-1984059787/10000000000 : ℝ), (328480267/625000000 : ℝ)] ![(4456930187689/10000000000000 : ℝ), (6082611075231/50000000000000 : ℝ), (43265475956707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344217549/2500000000 : ℝ)|^2205 ≤ (4456930187689/10000000000000 : ℝ)^1693
        have hw : |(1344217549/2500000000 : ℝ)|=(1344217549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1984059787/10000000000 : ℝ)|^2205 ≤ (6082611075231/50000000000000 : ℝ)^1693
        have hw : |(-1984059787/10000000000 : ℝ)|=(1984059787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328480267/625000000 : ℝ)|^2205 ≤ (43265475956707/100000000000000 : ℝ)^1693
        have hw : |(328480267/625000000 : ℝ)|=(328480267/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_box_14 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5376870101/10000000000 : ℝ)*x 0 + (2627842157/5000000000 : ℝ)*x 1 + (-992029929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376870101/10000000000 : ℝ)^2205 ≤ (22284650425641/50000000000000 : ℝ)^1693 := by
    have hnat : (5376870101 : ℕ)^2205*50000000000000^1693 ≤ 22284650425641^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376870101 10000000000 22284650425641 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627842157/5000000000 : ℝ)^2205 ≤ (43265476407019/100000000000000 : ℝ)^1693 := by
    have hnat : (2627842157 : ℕ)^2205*100000000000000^1693 ≤ 43265476407019^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627842157 5000000000 43265476407019 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (992029929/5000000000 : ℝ)^2205 ≤ (3041305679363/25000000000000 : ℝ)^1693 := by
    have hnat : (992029929 : ℕ)^2205*25000000000000^1693 ≤ 3041305679363^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992029929 5000000000 3041305679363 25000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376870101/10000000000 : ℝ), (2627842157/5000000000 : ℝ), (-992029929/5000000000 : ℝ)] ![(22284650425641/50000000000000 : ℝ), (43265476407019/100000000000000 : ℝ), (3041305679363/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376870101/10000000000 : ℝ)|^2205 ≤ (22284650425641/50000000000000 : ℝ)^1693
        have hw : |(5376870101/10000000000 : ℝ)|=(5376870101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627842157/5000000000 : ℝ)|^2205 ≤ (43265476407019/100000000000000 : ℝ)^1693
        have hw : |(2627842157/5000000000 : ℝ)|=(2627842157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-992029929/5000000000 : ℝ)|^2205 ≤ (3041305679363/25000000000000 : ℝ)^1693
        have hw : |(-992029929/5000000000 : ℝ)|=(992029929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_box_15 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1031057483/2500000000 : ℝ)*x 0 + (877997853/2000000000 : ℝ)*x 1 + (2194994517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031057483/2500000000 : ℝ)^2205 ≤ (1577553864693/5000000000000 : ℝ)^1693 := by
    have hnat : (1031057483 : ℕ)^2205*5000000000000^1693 ≤ 1577553864693^1693*2500000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031057483 2500000000 1577553864693 5000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (877997853/2000000000 : ℝ)^2205 ≤ (2139028907247/6250000000000 : ℝ)^1693 := by
    have hnat : (877997853 : ℕ)^2205*6250000000000^1693 ≤ 2139028907247^1693*2000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877997853 2000000000 2139028907247 6250000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2194994517/5000000000 : ℝ)^2205 ≤ (6844892034089/20000000000000 : ℝ)^1693 := by
    have hnat : (2194994517 : ℕ)^2205*20000000000000^1693 ≤ 6844892034089^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194994517 5000000000 6844892034089 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1031057483/2500000000 : ℝ), (877997853/2000000000 : ℝ), (2194994517/5000000000 : ℝ)] ![(1577553864693/5000000000000 : ℝ), (2139028907247/6250000000000 : ℝ), (6844892034089/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1031057483/2500000000 : ℝ)|^2205 ≤ (1577553864693/5000000000000 : ℝ)^1693
        have hw : |(1031057483/2500000000 : ℝ)|=(1031057483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(877997853/2000000000 : ℝ)|^2205 ≤ (2139028907247/6250000000000 : ℝ)^1693
        have hw : |(877997853/2000000000 : ℝ)|=(877997853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2194994517/5000000000 : ℝ)|^2205 ≤ (6844892034089/20000000000000 : ℝ)^1693
        have hw : |(2194994517/5000000000 : ℝ)|=(2194994517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1450_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39749881/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62913/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14789/25000 : ℝ) ∧ (80563/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84763/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11383/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11383/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11383/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14767/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11383/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11383/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14767/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11383/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11383/100000 : ℝ) ^ (4409/1024 : ℝ) ≤ (8640891328992947/100000000000000000000 : ℝ) := by
    have hpowers : (11383/100000 : ℝ)^4409 ≤ (8640891328992947/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11383 : ℕ)^4409*100000000000000000000^1024 ≤ 8640891328992947^1024*100000^4409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11383 100000 8640891328992947 100000000000000000000 4409 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11383/100000 : ℝ)) (X := (8640891328992947/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14767/100000 : ℝ) ^ (4409/1024 : ℝ) ≤ (13250174745110987/50000000000000000000 : ℝ) := by
    have hpowers : (14767/100000 : ℝ)^4409 ≤ (13250174745110987/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14767 : ℕ)^4409*50000000000000000000^1024 ≤ 13250174745110987^1024*100000^4409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14767 100000 13250174745110987 50000000000000000000 4409 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14767/100000 : ℝ)) (X := (13250174745110987/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008640891328992947/50000000000000000000 : ℝ) ≤ (10000401346599411/10000000000000000 : ℝ) ^ (4409/1024 : ℝ) := by
    have hpowers : (50008640891328992947/50000000000000000000 : ℝ)^1024 ≤ (10000401346599411/10000000000000000 : ℝ)^4409 := by
      have hnat : (50008640891328992947 : ℕ)^1024*10000000000000000^4409 ≤ 10000401346599411^4409*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008640891328992947 50000000000000000000 10000401346599411 10000000000000000 1024 4409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000401346599411/10000000000000000 : ℝ)) (X := (50008640891328992947/50000000000000000000 : ℝ)) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035141240819214921/100000000000000000000 : ℝ) ≤ (2000163210602619/2000000000000000 : ℝ) ^ (4409/1024 : ℝ) := by
    have hpowers : (100035141240819214921/100000000000000000000 : ℝ)^1024 ≤ (2000163210602619/2000000000000000 : ℝ)^4409 := by
      have hnat : (100035141240819214921 : ℕ)^1024*2000000000000000^4409 ≤ 2000163210602619^4409*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035141240819214921 100000000000000000000 2000163210602619 2000000000000000 1024 4409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000163210602619/2000000000000000 : ℝ)) (X := (100035141240819214921/100000000000000000000 : ℝ)) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013250174745110987/25000000000000000000 : ℝ) ≤ (10001230759426779/10000000000000000 : ℝ) ^ (4409/1024 : ℝ) := by
    have hpowers : (25013250174745110987/25000000000000000000 : ℝ)^1024 ≤ (10001230759426779/10000000000000000 : ℝ)^4409 := by
      have hnat : (25013250174745110987 : ℕ)^1024*10000000000000000^4409 ≤ 10001230759426779^4409*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013250174745110987 25000000000000000000 10001230759426779 10000000000000000 1024 4409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001230759426779/10000000000000000 : ℝ)) (X := (25013250174745110987/25000000000000000000 : ℝ)) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8640891328992947/100000000000000000000 : ℝ) ≤ ((140966320627826987/141000000000000000 : ℝ)+2*(34558867807/28200000000000 : ℝ)*(11383/100000 : ℝ))^(4409/1024 : ℝ) := by
    rw [show (140966320627826987/141000000000000000 : ℝ)+2*(34558867807/28200000000000 : ℝ)*(11383/100000 : ℝ)=(10000401346599411/10000000000000000 : ℝ) by norm_num, show 1+2*(8640891328992947/100000000000000000000 : ℝ)=(50008640891328992947/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13250174745110987/50000000000000000000 : ℝ)+(8640891328992947/100000000000000000000 : ℝ) ≤ ((140966320627826987/141000000000000000 : ℝ)+(34558867807/28200000000000 : ℝ)*((14767/100000 : ℝ)+(11383/100000 : ℝ)))^(4409/1024 : ℝ) := by
    rw [show (140966320627826987/141000000000000000 : ℝ)+(34558867807/28200000000000 : ℝ)*((14767/100000 : ℝ)+(11383/100000 : ℝ))=(2000163210602619/2000000000000000 : ℝ) by norm_num, show 1+(13250174745110987/50000000000000000000 : ℝ)+(8640891328992947/100000000000000000000 : ℝ)=(100035141240819214921/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13250174745110987/50000000000000000000 : ℝ) ≤ ((140966320627826987/141000000000000000 : ℝ)+2*(34558867807/28200000000000 : ℝ)*(14767/100000 : ℝ))^(4409/1024 : ℝ) := by
    rw [show (140966320627826987/141000000000000000 : ℝ)+2*(34558867807/28200000000000 : ℝ)*(14767/100000 : ℝ)=(10001230759426779/10000000000000000 : ℝ) by norm_num, show 1+2*(13250174745110987/50000000000000000000 : ℝ)=(25013250174745110987/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (140966320627826987/141000000000000000 : ℝ)*(X 1 0+X 2 0)+(34558867807/28200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4409/1024 : ℝ)) (lo := (11383/100000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (140966320627826987/141000000000000000 : ℝ)) (alpha := (34558867807/28200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (140966320627826987/141000000000000000 : ℝ)*(X 0 1+X 2 1)+(34558867807/28200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4409/1024 : ℝ)) (lo := (11383/100000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (140966320627826987/141000000000000000 : ℝ)) (alpha := (34558867807/28200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (140966320627826987/141000000000000000 : ℝ)*(X 0 2+X 1 2)+(34558867807/28200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4409/1024 : ℝ)) (lo := (11383/100000 : ℝ)) (hi := (14767/100000 : ℝ)) (c := (140966320627826987/141000000000000000 : ℝ)) (alpha := (34558867807/28200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-359012379/2000000000 : ℝ)*X 0 0+(5385354189/10000000000 : ℝ)*X 0 1+(2692677011/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2643099763/5000000000 : ℝ)*X 1 0+(-1931369283/10000000000 : ℝ)*X 1 1+(2692676989/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5286199357/10000000000 : ℝ)*X 2 0+(5385354189/10000000000 : ℝ)*X 2 1+(-1931369223/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((222251751/500000000 : ℝ)*X 0 0+(422987799/1000000000 : ℝ)*X 0 1+(4229877829/10000000000 : ℝ)*X 0 2+(222251751/500000000 : ℝ)*X 1 0+(422987799/1000000000 : ℝ)*X 1 1+(4229877829/10000000000 : ℝ)*X 1 2+(222251751/500000000 : ℝ)*X 2 0+(422987799/1000000000 : ℝ)*X 2 1+(4229877829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1058054219/5000000000 : ℝ)*X 0 0+(263340993/500000000 : ℝ)*X 0 1+(5266819989/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5369084959/10000000000 : ℝ)*X 1 0+(-123726579/625000000 : ℝ)*X 1 1+(5266819901/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((671135601/1250000000 : ℝ)*X 2 0+(5266820079/10000000000 : ℝ)*X 2 1+(-197962523/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1038047749/2500000000 : ℝ)*X 0 0+(10940623/25000000 : ℝ)*X 0 1+(109406251/250000000 : ℝ)*X 0 2+(1038047749/2500000000 : ℝ)*X 1 0+(10940623/25000000 : ℝ)*X 1 1+(109406251/250000000 : ℝ)*X 1 2+(1038047749/2500000000 : ℝ)*X 2 0+(10940623/25000000 : ℝ)*X 2 1+(109406251/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1024221029/5000000000 : ℝ)*X 0 0+(1296184519/2500000000 : ℝ)*X 0 1+(5399314661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2638216947/5000000000 : ℝ)*X 1 0+(-962780349/5000000000 : ℝ)*X 1 1+(5399314539/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((164888553/312500000 : ℝ)*X 2 0+(2699657313/5000000000 : ℝ)*X 2 1+(-1925560847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((111974223/250000000 : ℝ)*X 0 0+(2106311979/5000000000 : ℝ)*X 0 1+(4212623961/10000000000 : ℝ)*X 0 2+(111974223/250000000 : ℝ)*X 1 0+(2106311979/5000000000 : ℝ)*X 1 1+(4212623961/10000000000 : ℝ)*X 1 2+(111974223/250000000 : ℝ)*X 2 0+(2106311979/5000000000 : ℝ)*X 2 1+(4212623961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1862874029/10000000000 : ℝ)*X 0 0+(5465452251/10000000000 : ℝ)*X 0 1+(164240131/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1344217549/2500000000 : ℝ)*X 1 0+(-1984059787/10000000000 : ℝ)*X 1 1+(328480267/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5376870101/10000000000 : ℝ)*X 2 0+(2627842157/5000000000 : ℝ)*X 2 1+(-992029929/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1031057483/2500000000 : ℝ)*X 0 0+(877997853/2000000000 : ℝ)*X 0 1+(2194994517/5000000000 : ℝ)*X 0 2+(1031057483/2500000000 : ℝ)*X 1 0+(877997853/2000000000 : ℝ)*X 1 1+(2194994517/5000000000 : ℝ)*X 1 2+(1031057483/2500000000 : ℝ)*X 2 0+(877997853/2000000000 : ℝ)*X 2 1+(2194994517/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62913/100000 : ℝ) ≤ (-73919696731670258403866573/117500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2926191/100000000000000 : ℝ)*(upper0) + (49393399/100000000000000 : ℝ)*(lower3) + (110744367/100000000000000 : ℝ)*(lower4) + (75024397/50000000000000 : ℝ)*(upper5) + (1519816649674037/50000000000000 : ℝ)*(major0) + (1519816649674037/50000000000000 : ℝ)*(major1) + (1519816649674037/50000000000000 : ℝ)*(major2) + (4673270433/100000000000000 : ℝ)*(sp2) + (458948761/12500000000000 : ℝ)*(sp3) + (209425597304193/5000000000000 : ℝ)*(sp4) + (83770013797551/2000000000000 : ℝ)*(sp5) + (2094253636406713/50000000000000 : ℝ)*(sp6) + (1911721107754581/100000000000000 : ℝ)*(sp7) + (1125620631/10000000000000 : ℝ)*(sp13) + (1911724779344669/100000000000000 : ℝ)*(f.failure) + (209425597304193/5000000000000 : ℝ)*(f.sum) + (2089620278879/705000000000000000000000000 : ℝ)*base65 + (11180679480131519/7050000000000000000000000000000 : ℝ)*base67 + (11430516294468481/7050000000000000000000000000000 : ℝ)*base70 + (32768246711831519/7050000000000000000000000000000 : ℝ)*base71 + (11649874723891/705000000000000000000000000 : ℝ)*base74 + (20799975670968481/7050000000000000000000000000000 : ℝ)*base76 + (36689198829881519/7050000000000000000000000000000 : ℝ)*base77 + (217877450501418481/7050000000000000000000000000000 : ℝ)*base80 + (197804141753/352500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (734389/2500000000000000000000 : ℝ)*base89 + (734389/2500000000000000000000 : ℝ)*base91 + (734389/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14789/25000 : ℝ) ≤ (173776715210917250842674524127/293750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9202267/100000000000000 : ℝ)*(upper0) + (3297053/5000000000000 : ℝ)*(upper3) + (1752117/12500000000000 : ℝ)*(upper4) + (777987066673971/25000000000000 : ℝ)*(major0) + (777987066673971/25000000000000 : ℝ)*(major1) + (777987066673971/25000000000000 : ℝ)*(major2) + (2123484909681803/50000000000000 : ℝ)*(sp0) + (4246909200206899/100000000000000 : ℝ)*(sp1) + (265435507046341/6250000000000 : ℝ)*(sp2) + (978598420866929/50000000000000 : ℝ)*(sp3) + (953137/31250000000 : ℝ)*(sp6) + (1074733/80000000000 : ℝ)*(sp8) + (61962572957/100000000000000 : ℝ)*(sp9) + (9185308013/100000000000000 : ℝ)*(sp11) + (195720602704187/10000000000000 : ℝ)*(f.failure) + (265435697673741/6250000000000 : ℝ)*(f.sum) + (15372446169/29375000000000000000000000 : ℝ)*base66 + (4245014126986541/1175000000000000000000000000000 : ℝ)*base68 + (5740033542061541/1175000000000000000000000000000 : ℝ)*base70 + (4659657403813459/1175000000000000000000000000000 : ℝ)*base71 + (3561595031287/235000000000000000000000000 : ℝ)*base74 + (4597759011086541/1175000000000000000000000000000 : ℝ)*base76 + (3697808054186541/1175000000000000000000000000000 : ℝ)*base78 + (38327313520736541/1175000000000000000000000000000 : ℝ)*base80 + (1113708041047/235000000000000000000000000 : ℝ)*base82 + (1451747/250000000000000000000 : ℝ)*base89 + (1451747/250000000000000000000 : ℝ)*base91 + (1451747/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (80563/100000 : ℝ) ≤ (189330021078655123734823399/235000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39304289/50000000000000 : ℝ)*(upper2) + (23811819/50000000000000 : ℝ)*(lower3) + (124546731/100000000000000 : ℝ)*(lower5) + (1709323937840093/50000000000000 : ℝ)*(major0) + (1709323937840093/50000000000000 : ℝ)*(major1) + (1709323937840093/50000000000000 : ℝ)*(major2) + (4389731293/100000000000000 : ℝ)*(sp0) + (1399411011/10000000000000 : ℝ)*(sp2) + (44910752989/100000000000000 : ℝ)*(sp3) + (4660336383019683/100000000000000 : ℝ)*(sp8) + (291271311804589/6250000000000 : ℝ)*(sp9) + (2330163497381657/50000000000000 : ℝ)*(sp10) + (1075027264797569/50000000000000 : ℝ)*(sp11) + (216122449/100000000000000 : ℝ)*(sp12) + (2150099440348127/100000000000000 : ℝ)*(f.failure) + (291271311804589/6250000000000 : ℝ)*(f.sum) + (2914203972701/705000000000000000000000000 : ℝ)*base65 + (22386337144655209/7050000000000000000000000000000 : ℝ)*base68 + (41419887086555209/7050000000000000000000000000000 : ℝ)*base70 + (38798346294444791/7050000000000000000000000000000 : ℝ)*base71 + (979375540841/705000000000000000000000000 : ℝ)*base73 + (17153804140505209/7050000000000000000000000000000 : ℝ)*base76 + (42083683250544791/7050000000000000000000000000000 : ℝ)*base77 + (6687775646844791/7050000000000000000000000000000 : ℝ)*base79 + (10155827761/11015625000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (3177113/2500000000000000000000 : ℝ)*base90 + (3177113/2500000000000000000000 : ℝ)*base92 + (3177113/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-84763/100000 : ℝ) ≤ (-995937600347782292327338670663/1175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14034637/50000000000000 : ℝ)*(lower0) + (16919761/25000000000000 : ℝ)*(upper3) + (2476711/10000000000000 : ℝ)*(lower4) + (1728186712566983/50000000000000 : ℝ)*(major0) + (1728186712566983/50000000000000 : ℝ)*(major1) + (1728186712566983/50000000000000 : ℝ)*(major2) + (534661643/20000000000000 : ℝ)*(sp0) + (57658524121/100000000000000 : ℝ)*(sp5) + (31299379589/100000000000000 : ℝ)*(sp6) + (5042454271/20000000000000 : ℝ)*(sp7) + (4767171453863591/100000000000000 : ℝ)*(sp12) + (2383558234323843/50000000000000 : ℝ)*(sp13) + (4767142827792217/100000000000000 : ℝ)*(sp14) + (543450264942699/25000000000000 : ℝ)*(sp15) + (2173826272042151/100000000000000 : ℝ)*(f.failure) + (2383587063585903/50000000000000 : ℝ)*(f.sum) + (3934572304759/705000000000000000000000000 : ℝ)*base66 + (65325003296175221/7050000000000000000000000000000 : ℝ)*base67 + (71589826818675221/7050000000000000000000000000000 : ℝ)*base69 + (11106830027625221/7050000000000000000000000000000 : ℝ)*base71 + (3671577360911/705000000000000000000000000 : ℝ)*base73 + (22579760821125221/7050000000000000000000000000000 : ℝ)*base75 + (102225081422925221/7050000000000000000000000000000 : ℝ)*base77 + (82880238660525221/7050000000000000000000000000000 : ℝ)*base79 + (701625407359/705000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (20765969/2500000000000000000000 : ℝ)*base90 + (20765969/2500000000000000000000 : ℝ)*base92 + (20765969/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1450_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39749881/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14767/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11383/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62913/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14789/25000 : ℝ) else (80563/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84763/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1450_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1450_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39749881/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62913/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14789/25000 : ℝ) else (80563/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84763/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1450_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1450_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1450_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39749881/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62913/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14789/25000 : ℝ) else (80563/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84763/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1450_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

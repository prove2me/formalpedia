-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1151_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:36:05.312961+00:00
-- url     : https://prove2.me/submissions/956004f5-180b-4935-8b98-e040d528c261

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
theorem support_rectangle_w1151_s3_0 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1079441831/5000000000 : ℝ)*x 0 + (5428257919/10000000000 : ℝ)*x 1 + (5232923627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079441831/5000000000 : ℝ)^1043 ≤ (3277958192259/25000000000000 : ℝ)^787 := by
    have hnat : (1079441831 : ℕ)^1043*25000000000000^787 ≤ 3277958192259^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079441831 5000000000 3277958192259 25000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428257919/10000000000 : ℝ)^1043 ≤ (44498899376671/100000000000000 : ℝ)^787 := by
    have hnat : (5428257919 : ℕ)^1043*100000000000000^787 ≤ 44498899376671^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428257919 10000000000 44498899376671 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5232923627/10000000000 : ℝ)^1043 ≤ (42389267844029/100000000000000 : ℝ)^787 := by
    have hnat : (5232923627 : ℕ)^1043*100000000000000^787 ≤ 42389267844029^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232923627 10000000000 42389267844029 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1079441831/5000000000 : ℝ), (5428257919/10000000000 : ℝ), (5232923627/10000000000 : ℝ)] ![(3277958192259/25000000000000 : ℝ), (44498899376671/100000000000000 : ℝ), (42389267844029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1079441831/5000000000 : ℝ)|^1043 ≤ (3277958192259/25000000000000 : ℝ)^787
        have hw : |(-1079441831/5000000000 : ℝ)|=(1079441831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428257919/10000000000 : ℝ)|^1043 ≤ (44498899376671/100000000000000 : ℝ)^787
        have hw : |(5428257919/10000000000 : ℝ)|=(5428257919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5232923627/10000000000 : ℝ)|^1043 ≤ (42389267844029/100000000000000 : ℝ)^787
        have hw : |(5232923627/10000000000 : ℝ)|=(5232923627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s3_1 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5353579251/10000000000 : ℝ)*x 0 + (-1129356183/5000000000 : ℝ)*x 1 + (5232923447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353579251/10000000000 : ℝ)^1043 ≤ (43689395259793/100000000000000 : ℝ)^787 := by
    have hnat : (5353579251 : ℕ)^1043*100000000000000^787 ≤ 43689395259793^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353579251 10000000000 43689395259793 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129356183/5000000000 : ℝ)^1043 ≤ (6960669404527/50000000000000 : ℝ)^787 := by
    have hnat : (1129356183 : ℕ)^1043*50000000000000^787 ≤ 6960669404527^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129356183 5000000000 6960669404527 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5232923447/10000000000 : ℝ)^1043 ≤ (10597316477911/25000000000000 : ℝ)^787 := by
    have hnat : (5232923447 : ℕ)^1043*25000000000000^787 ≤ 10597316477911^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232923447 10000000000 10597316477911 25000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353579251/10000000000 : ℝ), (-1129356183/5000000000 : ℝ), (5232923447/10000000000 : ℝ)] ![(43689395259793/100000000000000 : ℝ), (6960669404527/50000000000000 : ℝ), (10597316477911/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353579251/10000000000 : ℝ)|^1043 ≤ (43689395259793/100000000000000 : ℝ)^787
        have hw : |(5353579251/10000000000 : ℝ)|=(5353579251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1129356183/5000000000 : ℝ)|^1043 ≤ (6960669404527/50000000000000 : ℝ)^787
        have hw : |(-1129356183/5000000000 : ℝ)|=(1129356183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5232923447/10000000000 : ℝ)|^1043 ≤ (10597316477911/25000000000000 : ℝ)^787
        have hw : |(5232923447/10000000000 : ℝ)|=(5232923447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s3_2 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5353579331/10000000000 : ℝ)*x 0 + (2616461751/5000000000 : ℝ)*x 1 + (-564678047/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353579331/10000000000 : ℝ)^1043 ≤ (43689396125023/100000000000000 : ℝ)^787 := by
    have hnat : (5353579331 : ℕ)^1043*100000000000000^787 ≤ 43689396125023^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353579331 10000000000 43689396125023 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2616461751/5000000000 : ℝ)^1043 ≤ (8477853300419/20000000000000 : ℝ)^787 := by
    have hnat : (2616461751 : ℕ)^1043*20000000000000^787 ≤ 8477853300419^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616461751 5000000000 8477853300419 20000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564678047/2500000000 : ℝ)^1043 ≤ (13921337355103/100000000000000 : ℝ)^787 := by
    have hnat : (564678047 : ℕ)^1043*100000000000000^787 ≤ 13921337355103^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564678047 2500000000 13921337355103 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353579331/10000000000 : ℝ), (2616461751/5000000000 : ℝ), (-564678047/2500000000 : ℝ)] ![(43689396125023/100000000000000 : ℝ), (8477853300419/20000000000000 : ℝ), (13921337355103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353579331/10000000000 : ℝ)|^1043 ≤ (43689396125023/100000000000000 : ℝ)^787
        have hw : |(5353579331/10000000000 : ℝ)|=(5353579331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2616461751/5000000000 : ℝ)|^1043 ≤ (8477853300419/20000000000000 : ℝ)^787
        have hw : |(2616461751/5000000000 : ℝ)|=(2616461751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-564678047/2500000000 : ℝ)|^1043 ≤ (13921337355103/100000000000000 : ℝ)^787
        have hw : |(-564678047/2500000000 : ℝ)|=(564678047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s3_3 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (872241227/2000000000 : ℝ)*x 0 + (417086443/1000000000 : ℝ)*x 1 + (570020369/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872241227/2000000000 : ℝ)^1043 ≤ (2080921735051/6250000000000 : ℝ)^787 := by
    have hnat : (872241227 : ℕ)^1043*6250000000000^787 ≤ 2080921735051^787*2000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872241227 2000000000 2080921735051 6250000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417086443/1000000000 : ℝ)^1043 ≤ (3922843522089/12500000000000 : ℝ)^787 := by
    have hnat : (417086443 : ℕ)^1043*12500000000000^787 ≤ 3922843522089^787*1000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417086443 1000000000 3922843522089 12500000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (570020369/1250000000 : ℝ)^1043 ≤ (17661252020443/50000000000000 : ℝ)^787 := by
    have hnat : (570020369 : ℕ)^1043*50000000000000^787 ≤ 17661252020443^787*1250000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570020369 1250000000 17661252020443 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872241227/2000000000 : ℝ), (417086443/1000000000 : ℝ), (570020369/1250000000 : ℝ)] ![(2080921735051/6250000000000 : ℝ), (3922843522089/12500000000000 : ℝ), (17661252020443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872241227/2000000000 : ℝ)|^1043 ≤ (2080921735051/6250000000000 : ℝ)^787
        have hw : |(872241227/2000000000 : ℝ)|=(872241227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(417086443/1000000000 : ℝ)|^1043 ≤ (3922843522089/12500000000000 : ℝ)^787
        have hw : |(417086443/1000000000 : ℝ)|=(417086443/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(570020369/1250000000 : ℝ)|^1043 ≤ (17661252020443/50000000000000 : ℝ)^787
        have hw : |(570020369/1250000000 : ℝ)|=(570020369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s3_4 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2158901293/10000000000 : ℝ)*x 0 + (5233676709/10000000000 : ℝ)*x 1 + (5427500663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158901293/10000000000 : ℝ)^1043 ≤ (2622394936347/20000000000000 : ℝ)^787 := by
    have hnat : (2158901293 : ℕ)^1043*20000000000000^787 ≤ 2622394936347^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158901293 10000000000 2622394936347 20000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5233676709/10000000000 : ℝ)^1043 ≤ (42397352723079/100000000000000 : ℝ)^787 := by
    have hnat : (5233676709 : ℕ)^1043*100000000000000^787 ≤ 42397352723079^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233676709 10000000000 42397352723079 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427500663/10000000000 : ℝ)^1043 ≤ (44490672570981/100000000000000 : ℝ)^787 := by
    have hnat : (5427500663 : ℕ)^1043*100000000000000^787 ≤ 44490672570981^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427500663 10000000000 44490672570981 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2158901293/10000000000 : ℝ), (5233676709/10000000000 : ℝ), (5427500663/10000000000 : ℝ)] ![(2622394936347/20000000000000 : ℝ), (42397352723079/100000000000000 : ℝ), (44490672570981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2158901293/10000000000 : ℝ)|^1043 ≤ (2622394936347/20000000000000 : ℝ)^787
        have hw : |(-2158901293/10000000000 : ℝ)|=(2158901293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5233676709/10000000000 : ℝ)|^1043 ≤ (42397352723079/100000000000000 : ℝ)^787
        have hw : |(5233676709/10000000000 : ℝ)|=(5233676709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427500663/10000000000 : ℝ)|^1043 ≤ (44490672570981/100000000000000 : ℝ)^787
        have hw : |(5427500663/10000000000 : ℝ)|=(5427500663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s3_5 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1060811909/2000000000 : ℝ)*x 0 + (-516033893/2500000000 : ℝ)*x 1 + (1356875121/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060811909/2000000000 : ℝ)^1043 ≤ (43154628737959/100000000000000 : ℝ)^787 := by
    have hnat : (1060811909 : ℕ)^1043*100000000000000^787 ≤ 43154628737959^787*2000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060811909 2000000000 43154628737959 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (516033893/2500000000 : ℝ)^1043 ≤ (12354700612031/100000000000000 : ℝ)^787 := by
    have hnat : (516033893 : ℕ)^1043*100000000000000^787 ≤ 12354700612031^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516033893 2500000000 12354700612031 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356875121/2500000000 : ℝ)^1043 ≤ (355925365011/800000000000 : ℝ)^787 := by
    have hnat : (1356875121 : ℕ)^1043*800000000000^787 ≤ 355925365011^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356875121 2500000000 355925365011 800000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060811909/2000000000 : ℝ), (-516033893/2500000000 : ℝ), (1356875121/2500000000 : ℝ)] ![(43154628737959/100000000000000 : ℝ), (12354700612031/100000000000000 : ℝ), (355925365011/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060811909/2000000000 : ℝ)|^1043 ≤ (43154628737959/100000000000000 : ℝ)^787
        have hw : |(1060811909/2000000000 : ℝ)|=(1060811909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-516033893/2500000000 : ℝ)|^1043 ≤ (12354700612031/100000000000000 : ℝ)^787
        have hw : |(-516033893/2500000000 : ℝ)|=(516033893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356875121/2500000000 : ℝ)|^1043 ≤ (355925365011/800000000000 : ℝ)^787
        have hw : |(1356875121/2500000000 : ℝ)|=(1356875121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s3_6 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (165751881/312500000 : ℝ)*x 0 + (542750001/1000000000 : ℝ)*x 1 + (-2064135343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165751881/312500000 : ℝ)^1043 ≤ (43154635714383/100000000000000 : ℝ)^787 := by
    have hnat : (165751881 : ℕ)^1043*100000000000000^787 ≤ 43154635714383^787*312500000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165751881 312500000 43154635714383 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542750001/1000000000 : ℝ)^1043 ≤ (4449066547697/10000000000000 : ℝ)^787 := by
    have hnat : (542750001 : ℕ)^1043*10000000000000^787 ≤ 4449066547697^787*1000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542750001 1000000000 4449066547697 10000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064135343/10000000000 : ℝ)^1043 ≤ (2470939759103/20000000000000 : ℝ)^787 := by
    have hnat : (2064135343 : ℕ)^1043*20000000000000^787 ≤ 2470939759103^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064135343 10000000000 2470939759103 20000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165751881/312500000 : ℝ), (542750001/1000000000 : ℝ), (-2064135343/10000000000 : ℝ)] ![(43154635714383/100000000000000 : ℝ), (4449066547697/10000000000000 : ℝ), (2470939759103/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165751881/312500000 : ℝ)|^1043 ≤ (43154635714383/100000000000000 : ℝ)^787
        have hw : |(165751881/312500000 : ℝ)|=(165751881/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542750001/1000000000 : ℝ)|^1043 ≤ (4449066547697/10000000000000 : ℝ)^787
        have hw : |(542750001/1000000000 : ℝ)|=(542750001/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2064135343/10000000000 : ℝ)|^1043 ≤ (2470939759103/20000000000000 : ℝ)^787
        have hw : |(-2064135343/10000000000 : ℝ)|=(2064135343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s3_7 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4361241093/10000000000 : ℝ)*x 0 + (4558662153/10000000000 : ℝ)*x 1 + (130386681/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361241093/10000000000 : ℝ)^1043 ≤ (33295101453303/100000000000000 : ℝ)^787 := by
    have hnat : (4361241093 : ℕ)^1043*100000000000000^787 ≤ 33295101453303^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361241093 10000000000 33295101453303 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4558662153/10000000000 : ℝ)^1043 ≤ (35307098392543/100000000000000 : ℝ)^787 := by
    have hnat : (4558662153 : ℕ)^1043*100000000000000^787 ≤ 35307098392543^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4558662153 10000000000 35307098392543 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130386681/312500000 : ℝ)^1043 ≤ (15698900075103/50000000000000 : ℝ)^787 := by
    have hnat : (130386681 : ℕ)^1043*50000000000000^787 ≤ 15698900075103^787*312500000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130386681 312500000 15698900075103 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361241093/10000000000 : ℝ), (4558662153/10000000000 : ℝ), (130386681/312500000 : ℝ)] ![(33295101453303/100000000000000 : ℝ), (35307098392543/100000000000000 : ℝ), (15698900075103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361241093/10000000000 : ℝ)|^1043 ≤ (33295101453303/100000000000000 : ℝ)^787
        have hw : |(4361241093/10000000000 : ℝ)|=(4361241093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4558662153/10000000000 : ℝ)|^1043 ≤ (35307098392543/100000000000000 : ℝ)^787
        have hw : |(4558662153/10000000000 : ℝ)|=(4558662153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130386681/312500000 : ℝ)|^1043 ≤ (15698900075103/50000000000000 : ℝ)^787
        have hw : |(130386681/312500000 : ℝ)|=(130386681/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1151_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4119/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9111/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5331/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2959/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4119/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9111/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4119/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9111/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4119/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9111/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4119/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9111/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4119/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9111/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4119/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9111/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9111/100000 : ℝ) ^ (8343/2048 : ℝ) ≤ (2887503423443237/50000000000000000000 : ℝ) := by
    have hpowers : (9111/100000 : ℝ)^8343 ≤ (2887503423443237/50000000000000000000 : ℝ)^2048 := by
      have hnat : (9111 : ℕ)^8343*50000000000000000000^2048 ≤ 2887503423443237^2048*100000^8343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9111 100000 2887503423443237 50000000000000000000 8343 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9111/100000 : ℝ)) (X := (2887503423443237/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (4119/25000 : ℝ) ^ (8343/2048 : ℝ) ≤ (32257837689168139/50000000000000000000 : ℝ) := by
    have hpowers : (4119/25000 : ℝ)^8343 ≤ (32257837689168139/50000000000000000000 : ℝ)^2048 := by
      have hnat : (4119 : ℕ)^8343*50000000000000000000^2048 ≤ 32257837689168139^2048*25000^8343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4119 25000 32257837689168139 50000000000000000000 8343 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4119/25000 : ℝ)) (X := (32257837689168139/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002887503423443237/25000000000000000000 : ℝ) ≤ (2000056702379/2000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (25002887503423443237/25000000000000000000 : ℝ)^2048 ≤ (2000056702379/2000000000000 : ℝ)^8343 := by
      have hnat : (25002887503423443237 : ℕ)^2048*2000000000000^8343 ≤ 2000056702379^8343*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002887503423443237 25000000000000000000 2000056702379 2000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000056702379/2000000000000 : ℝ)) (X := (25002887503423443237/25000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3127196583819538211/3125000000000000000 : ℝ) ≤ (5000862502449771/5000000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (3127196583819538211/3125000000000000000 : ℝ)^2048 ≤ (5000862502449771/5000000000000000 : ℝ)^8343 := by
      have hnat : (3127196583819538211 : ℕ)^2048*5000000000000000^8343 ≤ 5000862502449771^8343*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127196583819538211 3125000000000000000 5000862502449771 5000000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000862502449771/5000000000000000 : ℝ)) (X := (3127196583819538211/3125000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25032257837689168139/25000000000000000000 : ℝ) ≤ (2500791624476021/2500000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (25032257837689168139/25000000000000000000 : ℝ)^2048 ≤ (2500791624476021/2500000000000000 : ℝ)^8343 := by
      have hnat : (25032257837689168139 : ℕ)^2048*2500000000000000^8343 ≤ 2500791624476021^8343*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25032257837689168139 25000000000000000000 2500791624476021 2500000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500791624476021/2500000000000000 : ℝ)) (X := (25032257837689168139/25000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2887503423443237/50000000000000000000 : ℝ) ≤ ((6135485098298159223/6137500000000000000 : ℝ)+2*(720746502271/368250000000000 : ℝ)*(9111/100000 : ℝ))^(8343/2048 : ℝ) := by
    rw [show (6135485098298159223/6137500000000000000 : ℝ)+2*(720746502271/368250000000000 : ℝ)*(9111/100000 : ℝ)=(2000056702379/2000000000000 : ℝ) by norm_num, show 1+2*(2887503423443237/50000000000000000000 : ℝ)=(25002887503423443237/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32257837689168139/50000000000000000000 : ℝ)+(2887503423443237/50000000000000000000 : ℝ) ≤ ((6135485098298159223/6137500000000000000 : ℝ)+(720746502271/368250000000000 : ℝ)*((4119/25000 : ℝ)+(9111/100000 : ℝ)))^(8343/2048 : ℝ) := by
    rw [show (6135485098298159223/6137500000000000000 : ℝ)+(720746502271/368250000000000 : ℝ)*((4119/25000 : ℝ)+(9111/100000 : ℝ))=(5000862502449771/5000000000000000 : ℝ) by norm_num, show 1+(32257837689168139/50000000000000000000 : ℝ)+(2887503423443237/50000000000000000000 : ℝ)=(3127196583819538211/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32257837689168139/50000000000000000000 : ℝ) ≤ ((6135485098298159223/6137500000000000000 : ℝ)+2*(720746502271/368250000000000 : ℝ)*(4119/25000 : ℝ))^(8343/2048 : ℝ) := by
    rw [show (6135485098298159223/6137500000000000000 : ℝ)+2*(720746502271/368250000000000 : ℝ)*(4119/25000 : ℝ)=(2500791624476021/2500000000000000 : ℝ) by norm_num, show 1+2*(32257837689168139/50000000000000000000 : ℝ)=(25032257837689168139/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6135485098298159223/6137500000000000000 : ℝ)*(X 1 0+X 2 0)+(720746502271/368250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (9111/100000 : ℝ)) (hi := (4119/25000 : ℝ)) (c := (6135485098298159223/6137500000000000000 : ℝ)) (alpha := (720746502271/368250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6135485098298159223/6137500000000000000 : ℝ)*(X 0 1+X 2 1)+(720746502271/368250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (9111/100000 : ℝ)) (hi := (4119/25000 : ℝ)) (c := (6135485098298159223/6137500000000000000 : ℝ)) (alpha := (720746502271/368250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6135485098298159223/6137500000000000000 : ℝ)*(X 0 2+X 1 2)+(720746502271/368250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (9111/100000 : ℝ)) (hi := (4119/25000 : ℝ)) (c := (6135485098298159223/6137500000000000000 : ℝ)) (alpha := (720746502271/368250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1079441831/5000000000 : ℝ)*X 0 0+(5428257919/10000000000 : ℝ)*X 0 1+(5232923627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353579251/10000000000 : ℝ)*X 1 0+(-1129356183/5000000000 : ℝ)*X 1 1+(5232923447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353579331/10000000000 : ℝ)*X 2 0+(2616461751/5000000000 : ℝ)*X 2 1+(-564678047/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((872241227/2000000000 : ℝ)*X 0 0+(417086443/1000000000 : ℝ)*X 0 1+(570020369/1250000000 : ℝ)*X 0 2+(872241227/2000000000 : ℝ)*X 1 0+(417086443/1000000000 : ℝ)*X 1 1+(570020369/1250000000 : ℝ)*X 1 2+(872241227/2000000000 : ℝ)*X 2 0+(417086443/1000000000 : ℝ)*X 2 1+(570020369/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2158901293/10000000000 : ℝ)*X 0 0+(5233676709/10000000000 : ℝ)*X 0 1+(5427500663/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060811909/2000000000 : ℝ)*X 1 0+(-516033893/2500000000 : ℝ)*X 1 1+(1356875121/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165751881/312500000 : ℝ)*X 2 0+(542750001/1000000000 : ℝ)*X 2 1+(-2064135343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4361241093/10000000000 : ℝ)*X 0 0+(4558662153/10000000000 : ℝ)*X 0 1+(130386681/312500000 : ℝ)*X 0 2+(4361241093/10000000000 : ℝ)*X 1 0+(4558662153/10000000000 : ℝ)*X 1 1+(130386681/312500000 : ℝ)*X 1 2+(4361241093/10000000000 : ℝ)*X 2 0+(4558662153/10000000000 : ℝ)*X 2 1+(130386681/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (172369259703740693705213441/153437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2114957/390625000000 : ℝ)*(base19) + (553244047/100000000000000 : ℝ)*(base23) + (43621197/100000000000000 : ℝ)*(lower2) + (2278637/3125000000000 : ℝ)*(upper5) + (3844087980697379/100000000000000 : ℝ)*(major0) + (3844087980697379/100000000000000 : ℝ)*(major1) + (192204399034869/5000000000000 : ℝ)*(major2) + (511943525242289/10000000000000 : ℝ)*(sp0) + (5119443239920439/100000000000000 : ℝ)*(sp1) + (1279861260932483/25000000000000 : ℝ)*(sp2) + (1284363374381769/50000000000000 : ℝ)*(sp3) + (10344551089/100000000000000 : ℝ)*(sp4) + (453906137/25000000000000 : ℝ)*(sp5) + (715642219/20000000000000 : ℝ)*(sp7) + (321091290871829/12500000000000 : ℝ)*(f.failure) + (5119445596973979/100000000000000 : ℝ)*(f.sum) + (51951467763089/36825000000000000000000000000 : ℝ)*base65 + (7927604351428723483/613750000000000000000000000000000 : ℝ)*base68 + (417228200387800361/92062500000000000000000000000000 : ℝ)*base69 + (3960975802863723483/613750000000000000000000000000000 : ℝ)*base72 + (31011038023367/4603125000000000000000000000 : ℝ)*base74 + (359374244735050361/92062500000000000000000000000000 : ℝ)*base75 + (916232228878470449/1841250000000000000000000000000000 : ℝ)*base78 + (10496320021235970449/1841250000000000000000000000000000 : ℝ)*base80 + (58693709122291/18412500000000000000000000000 : ℝ)*base82 + (152857/62500000000000000000 : ℝ)*base90 + (152857/62500000000000000000 : ℝ)*base92 + (777857/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35391746131453121599701/6137500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1013043709/100000000000000 : ℝ)*(base19) + (890938213/50000000000000 : ℝ)*(base23) + (74062367/100000000000000 : ℝ)*(upper3) + (7657279/25000000000000 : ℝ)*(lower4) + (24468759/20000000000000 : ℝ)*(upper5) + (3874034069014423/100000000000000 : ℝ)*(major0) + (3874034069014423/100000000000000 : ℝ)*(major1) + (3874034069014423/100000000000000 : ℝ)*(major2) + (953349493/6250000000000 : ℝ)*(sp1) + (24009170697/100000000000000 : ℝ)*(sp2) + (206373071198209/4000000000000 : ℝ)*(sp4) + (1289827628329907/25000000000000 : ℝ)*(sp5) + (2579650494454051/50000000000000 : ℝ)*(sp6) + (1294370582928873/50000000000000 : ℝ)*(sp7) + (1294370582928873/50000000000000 : ℝ)*(f.failure) + (206373071198209/4000000000000 : ℝ)*(f.sum) + (212040602077541/36825000000000000000000000000 : ℝ)*base65 + (14405309068945319987/1841250000000000000000000000000000 : ℝ)*base67 + (19852556370694680013/1841250000000000000000000000000000 : ℝ)*base70 + (10635755021196569987/1841250000000000000000000000000000 : ℝ)*base71 + (21410098028201/2301562500000000000000000000 : ℝ)*base73 + (5680609257255930013/1841250000000000000000000000000000 : ℝ)*base76 + (14453450380397819987/1841250000000000000000000000000000 : ℝ)*base77 + (19123388311050930013/1841250000000000000000000000000000 : ℝ)*base80 + (5818454947627/4603125000000000000000000000 : ℝ)*base81 + (1930309/250000000000000000000 : ℝ)*base90 + (1930309/250000000000000000000 : ℝ)*base92 + (1930309/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1151_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4119/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9111/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5331/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2959/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1151_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1151_s4_0 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1080907047/5000000000 : ℝ)*x 0 + (5401461271/10000000000 : ℝ)*x 1 + (525780301/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080907047/5000000000 : ℝ)^1043 ≤ (13135425120251/100000000000000 : ℝ)^787 := by
    have hnat : (1080907047 : ℕ)^1043*100000000000000^787 ≤ 13135425120251^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080907047 5000000000 13135425120251 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401461271/10000000000 : ℝ)^1043 ≤ (22104004409607/50000000000000 : ℝ)^787 := by
    have hnat : (5401461271 : ℕ)^1043*50000000000000^787 ≤ 22104004409607^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401461271 10000000000 22104004409607 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525780301/1000000000 : ℝ)^1043 ≤ (53320707559/125000000000 : ℝ)^787 := by
    have hnat : (525780301 : ℕ)^1043*125000000000^787 ≤ 53320707559^787*1000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525780301 1000000000 53320707559 125000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1080907047/5000000000 : ℝ), (5401461271/10000000000 : ℝ), (525780301/1000000000 : ℝ)] ![(13135425120251/100000000000000 : ℝ), (22104004409607/50000000000000 : ℝ), (53320707559/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1080907047/5000000000 : ℝ)|^1043 ≤ (13135425120251/100000000000000 : ℝ)^787
        have hw : |(-1080907047/5000000000 : ℝ)|=(1080907047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401461271/10000000000 : ℝ)|^1043 ≤ (22104004409607/50000000000000 : ℝ)^787
        have hw : |(5401461271/10000000000 : ℝ)|=(5401461271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525780301/1000000000 : ℝ)|^1043 ≤ (53320707559/125000000000 : ℝ)^787
        have hw : |(525780301/1000000000 : ℝ)|=(525780301/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s4_1 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2673440553/5000000000 : ℝ)*x 0 + (-2234813019/10000000000 : ℝ)*x 1 + (5257803699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673440553/5000000000 : ℝ)^1043 ≤ (43616967090311/100000000000000 : ℝ)^787 := by
    have hnat : (2673440553 : ℕ)^1043*100000000000000^787 ≤ 43616967090311^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673440553 5000000000 43616967090311 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2234813019/10000000000 : ℝ)^1043 ≤ (13726459439603/100000000000000 : ℝ)^787 := by
    have hnat : (2234813019 : ℕ)^1043*100000000000000^787 ≤ 13726459439603^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234813019 10000000000 13726459439603 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5257803699/10000000000 : ℝ)^1043 ≤ (42656573455361/100000000000000 : ℝ)^787 := by
    have hnat : (5257803699 : ℕ)^1043*100000000000000^787 ≤ 42656573455361^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257803699 10000000000 42656573455361 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673440553/5000000000 : ℝ), (-2234813019/10000000000 : ℝ), (5257803699/10000000000 : ℝ)] ![(43616967090311/100000000000000 : ℝ), (13726459439603/100000000000000 : ℝ), (42656573455361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673440553/5000000000 : ℝ)|^1043 ≤ (43616967090311/100000000000000 : ℝ)^787
        have hw : |(2673440553/5000000000 : ℝ)|=(2673440553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2234813019/10000000000 : ℝ)|^1043 ≤ (13726459439603/100000000000000 : ℝ)^787
        have hw : |(-2234813019/10000000000 : ℝ)|=(2234813019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5257803699/10000000000 : ℝ)|^1043 ≤ (42656573455361/100000000000000 : ℝ)^787
        have hw : |(5257803699/10000000000 : ℝ)|=(5257803699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s4_2 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5346881147/10000000000 : ℝ)*x 0 + (525780317/1000000000 : ℝ)*x 1 + (-2234813663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346881147/10000000000 : ℝ)^1043 ≤ (43616967533561/100000000000000 : ℝ)^787 := by
    have hnat : (5346881147 : ℕ)^1043*100000000000000^787 ≤ 43616967533561^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346881147 10000000000 43616967533561 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525780317/1000000000 : ℝ)^1043 ≤ (5332070970941/12500000000000 : ℝ)^787 := by
    have hnat : (525780317 : ℕ)^1043*12500000000000^787 ≤ 5332070970941^787*1000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525780317 1000000000 5332070970941 12500000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2234813663/10000000000 : ℝ)^1043 ≤ (13726464681793/100000000000000 : ℝ)^787 := by
    have hnat : (2234813663 : ℕ)^1043*100000000000000^787 ≤ 13726464681793^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2234813663 10000000000 13726464681793 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346881147/10000000000 : ℝ), (525780317/1000000000 : ℝ), (-2234813663/10000000000 : ℝ)] ![(43616967533561/100000000000000 : ℝ), (5332070970941/12500000000000 : ℝ), (13726464681793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346881147/10000000000 : ℝ)|^1043 ≤ (43616967533561/100000000000000 : ℝ)^787
        have hw : |(5346881147/10000000000 : ℝ)|=(5346881147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525780317/1000000000 : ℝ)|^1043 ≤ (5332070970941/12500000000000 : ℝ)^787
        have hw : |(525780317/1000000000 : ℝ)|=(525780317/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2234813663/10000000000 : ℝ)|^1043 ≤ (13726464681793/100000000000000 : ℝ)^787
        have hw : |(-2234813663/10000000000 : ℝ)|=(2234813663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s4_3 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4362956003/10000000000 : ℝ)*x 0 + (4222132097/10000000000 : ℝ)*x 1 + (2254221163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362956003/10000000000 : ℝ)^1043 ≤ (16656226714433/50000000000000 : ℝ)^787 := by
    have hnat : (4362956003 : ℕ)^1043*50000000000000^787 ≤ 16656226714433^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362956003 10000000000 16656226714433 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222132097/10000000000 : ℝ)^1043 ≤ (7973749852769/25000000000000 : ℝ)^787 := by
    have hnat : (4222132097 : ℕ)^1043*25000000000000^787 ≤ 7973749852769^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222132097 10000000000 7973749852769 25000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2254221163/5000000000 : ℝ)^1043 ≤ (34792547150091/100000000000000 : ℝ)^787 := by
    have hnat : (2254221163 : ℕ)^1043*100000000000000^787 ≤ 34792547150091^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254221163 5000000000 34792547150091 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362956003/10000000000 : ℝ), (4222132097/10000000000 : ℝ), (2254221163/5000000000 : ℝ)] ![(16656226714433/50000000000000 : ℝ), (7973749852769/25000000000000 : ℝ), (34792547150091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362956003/10000000000 : ℝ)|^1043 ≤ (16656226714433/50000000000000 : ℝ)^787
        have hw : |(4362956003/10000000000 : ℝ)|=(4362956003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222132097/10000000000 : ℝ)|^1043 ≤ (7973749852769/25000000000000 : ℝ)^787
        have hw : |(4222132097/10000000000 : ℝ)|=(4222132097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2254221163/5000000000 : ℝ)|^1043 ≤ (34792547150091/100000000000000 : ℝ)^787
        have hw : |(2254221163/5000000000 : ℝ)|=(2254221163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s4_4 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-432364313/2000000000 : ℝ)*x 0 + (5258210899/10000000000 : ℝ)*x 1 + (5401051387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432364313/2000000000 : ℝ)^1043 ≤ (6567742640577/50000000000000 : ℝ)^787 := by
    have hnat : (432364313 : ℕ)^1043*50000000000000^787 ≤ 6567742640577^787*2000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432364313 2000000000 6567742640577 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5258210899/10000000000 : ℝ)^1043 ≤ (8532190348851/20000000000000 : ℝ)^787 := by
    have hnat : (5258210899 : ℕ)^1043*20000000000000^787 ≤ 8532190348851^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5258210899 10000000000 8532190348851 20000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401051387/10000000000 : ℝ)^1043 ≤ (44203562968563/100000000000000 : ℝ)^787 := by
    have hnat : (5401051387 : ℕ)^1043*100000000000000^787 ≤ 44203562968563^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401051387 10000000000 44203562968563 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-432364313/2000000000 : ℝ), (5258210899/10000000000 : ℝ), (5401051387/10000000000 : ℝ)] ![(6567742640577/50000000000000 : ℝ), (8532190348851/20000000000000 : ℝ), (44203562968563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-432364313/2000000000 : ℝ)|^1043 ≤ (6567742640577/50000000000000 : ℝ)^787
        have hw : |(-432364313/2000000000 : ℝ)|=(432364313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5258210899/10000000000 : ℝ)|^1043 ≤ (8532190348851/20000000000000 : ℝ)^787
        have hw : |(5258210899/10000000000 : ℝ)|=(5258210899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401051387/10000000000 : ℝ)|^1043 ≤ (44203562968563/100000000000000 : ℝ)^787
        have hw : |(5401051387/10000000000 : ℝ)|=(5401051387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s4_5 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5310463149/10000000000 : ℝ)*x 0 + (-261445579/1250000000 : ℝ)*x 1 + (5401051313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310463149/10000000000 : ℝ)^1043 ≤ (43223690599949/100000000000000 : ℝ)^787 := by
    have hnat : (5310463149 : ℕ)^1043*100000000000000^787 ≤ 43223690599949^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310463149 10000000000 43223690599949 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261445579/1250000000 : ℝ)^1043 ≤ (12572747220901/100000000000000 : ℝ)^787 := by
    have hnat : (261445579 : ℕ)^1043*100000000000000^787 ≤ 12572747220901^787*1250000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261445579 1250000000 12572747220901 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401051313/10000000000 : ℝ)^1043 ≤ (11050890541481/25000000000000 : ℝ)^787 := by
    have hnat : (5401051313 : ℕ)^1043*25000000000000^787 ≤ 11050890541481^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401051313 10000000000 11050890541481 25000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310463149/10000000000 : ℝ), (-261445579/1250000000 : ℝ), (5401051313/10000000000 : ℝ)] ![(43223690599949/100000000000000 : ℝ), (12572747220901/100000000000000 : ℝ), (11050890541481/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310463149/10000000000 : ℝ)|^1043 ≤ (43223690599949/100000000000000 : ℝ)^787
        have hw : |(5310463149/10000000000 : ℝ)|=(5310463149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-261445579/1250000000 : ℝ)|^1043 ≤ (12572747220901/100000000000000 : ℝ)^787
        have hw : |(-261445579/1250000000 : ℝ)|=(261445579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401051313/10000000000 : ℝ)|^1043 ≤ (11050890541481/25000000000000 : ℝ)^787
        have hw : |(5401051313/10000000000 : ℝ)|=(5401051313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s4_6 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5310463039/10000000000 : ℝ)*x 0 + (5401051323/10000000000 : ℝ)*x 1 + (-2091564767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310463039/10000000000 : ℝ)^1043 ≤ (43223689413383/100000000000000 : ℝ)^787 := by
    have hnat : (5310463039 : ℕ)^1043*100000000000000^787 ≤ 43223689413383^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310463039 10000000000 43223689413383 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401051323/10000000000 : ℝ)^1043 ≤ (44203562274389/100000000000000 : ℝ)^787 := by
    have hnat : (5401051323 : ℕ)^1043*100000000000000^787 ≤ 44203562274389^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401051323 10000000000 44203562274389 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2091564767/10000000000 : ℝ)^1043 ≤ (12572748296381/100000000000000 : ℝ)^787 := by
    have hnat : (2091564767 : ℕ)^1043*100000000000000^787 ≤ 12572748296381^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091564767 10000000000 12572748296381 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310463039/10000000000 : ℝ), (5401051323/10000000000 : ℝ), (-2091564767/10000000000 : ℝ)] ![(43223689413383/100000000000000 : ℝ), (44203562274389/100000000000000 : ℝ), (12572748296381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310463039/10000000000 : ℝ)|^1043 ≤ (43223689413383/100000000000000 : ℝ)^787
        have hw : |(5310463039/10000000000 : ℝ)|=(5310463039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401051323/10000000000 : ℝ)|^1043 ≤ (44203562274389/100000000000000 : ℝ)^787
        have hw : |(5401051323/10000000000 : ℝ)|=(5401051323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2091564767/10000000000 : ℝ)|^1043 ≤ (12572748296381/100000000000000 : ℝ)^787
        have hw : |(-2091564767/10000000000 : ℝ)|=(2091564767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s4_7 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4362969891/10000000000 : ℝ)*x 0 + (4507628297/10000000000 : ℝ)*x 1 + (2111474799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4362969891/10000000000 : ℝ)^1043 ≤ (4164074245111/12500000000000 : ℝ)^787 := by
    have hnat : (4362969891 : ℕ)^1043*12500000000000^787 ≤ 4164074245111^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4362969891 10000000000 4164074245111 12500000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4507628297/10000000000 : ℝ)^1043 ≤ (34784221916941/100000000000000 : ℝ)^787 := by
    have hnat : (4507628297 : ℕ)^1043*100000000000000^787 ≤ 34784221916941^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507628297 10000000000 34784221916941 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2111474799/5000000000 : ℝ)^1043 ≤ (3987898012849/12500000000000 : ℝ)^787 := by
    have hnat : (2111474799 : ℕ)^1043*12500000000000^787 ≤ 3987898012849^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111474799 5000000000 3987898012849 12500000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4362969891/10000000000 : ℝ), (4507628297/10000000000 : ℝ), (2111474799/5000000000 : ℝ)] ![(4164074245111/12500000000000 : ℝ), (34784221916941/100000000000000 : ℝ), (3987898012849/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4362969891/10000000000 : ℝ)|^1043 ≤ (4164074245111/12500000000000 : ℝ)^787
        have hw : |(4362969891/10000000000 : ℝ)|=(4362969891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4507628297/10000000000 : ℝ)|^1043 ≤ (34784221916941/100000000000000 : ℝ)^787
        have hw : |(4507628297/10000000000 : ℝ)|=(4507628297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2111474799/5000000000 : ℝ)|^1043 ≤ (3987898012849/12500000000000 : ℝ)^787
        have hw : |(2111474799/5000000000 : ℝ)|=(2111474799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1151_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2959/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5331/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1399/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2959/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5331/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2959/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5331/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2959/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5331/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2959/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5331/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2959/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5331/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2959/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5331/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5331/50000 : ℝ) ^ (8343/2048 : ℝ) ≤ (2739156281537061/25000000000000000000 : ℝ) := by
    have hpowers : (5331/50000 : ℝ)^8343 ≤ (2739156281537061/25000000000000000000 : ℝ)^2048 := by
      have hnat : (5331 : ℕ)^8343*25000000000000000000^2048 ≤ 2739156281537061^2048*50000^8343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5331 50000 2739156281537061 25000000000000000000 8343 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5331/50000 : ℝ)) (X := (2739156281537061/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2959/20000 : ℝ) ^ (8343/2048 : ℝ) ≤ (1664684964577543/4000000000000000000 : ℝ) := by
    have hpowers : (2959/20000 : ℝ)^8343 ≤ (1664684964577543/4000000000000000000 : ℝ)^2048 := by
      have hnat : (2959 : ℕ)^8343*4000000000000000000^2048 ≤ 1664684964577543^2048*20000^8343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2959 20000 1664684964577543 4000000000000000000 8343 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2959/20000 : ℝ)) (X := (1664684964577543/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502739156281537061/12500000000000000000 : ℝ) ≤ (10000537871591513/10000000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (12502739156281537061/12500000000000000000 : ℝ)^2048 ≤ (10000537871591513/10000000000000000 : ℝ)^8343 := by
      have hnat : (12502739156281537061 : ℕ)^2048*10000000000000000^8343 ≤ 10000537871591513^8343*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502739156281537061 12500000000000000000 10000537871591513 10000000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000537871591513/10000000000000000 : ℝ)) (X := (12502739156281537061/12500000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052573749240586819/100000000000000000000 : ℝ) ≤ (10001290299525709/10000000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (100052573749240586819/100000000000000000000 : ℝ)^2048 ≤ (10001290299525709/10000000000000000 : ℝ)^8343 := by
      have hnat : (100052573749240586819 : ℕ)^2048*10000000000000000^8343 ≤ 10001290299525709^8343*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052573749240586819 100000000000000000000 10001290299525709 10000000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001290299525709/10000000000000000 : ℝ)) (X := (100052573749240586819/100000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001664684964577543/2000000000000000000 : ℝ) ≤ (2000408545491981/2000000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (2001664684964577543/2000000000000000000 : ℝ)^2048 ≤ (2000408545491981/2000000000000000 : ℝ)^8343 := by
      have hnat : (2001664684964577543 : ℕ)^2048*2000000000000000^8343 ≤ 2000408545491981^8343*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001664684964577543 2000000000000000000 2000408545491981 2000000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000408545491981/2000000000000000 : ℝ)) (X := (2001664684964577543/2000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2739156281537061/25000000000000000000 : ℝ) ≤ ((1652647130000757109/1653200000000000000 : ℝ)+2*(188106983549/103325000000000 : ℝ)*(5331/50000 : ℝ))^(8343/2048 : ℝ) := by
    rw [show (1652647130000757109/1653200000000000000 : ℝ)+2*(188106983549/103325000000000 : ℝ)*(5331/50000 : ℝ)=(10000537871591513/10000000000000000 : ℝ) by norm_num, show 1+2*(2739156281537061/25000000000000000000 : ℝ)=(12502739156281537061/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1664684964577543/4000000000000000000 : ℝ)+(2739156281537061/25000000000000000000 : ℝ) ≤ ((1652647130000757109/1653200000000000000 : ℝ)+(188106983549/103325000000000 : ℝ)*((2959/20000 : ℝ)+(5331/50000 : ℝ)))^(8343/2048 : ℝ) := by
    rw [show (1652647130000757109/1653200000000000000 : ℝ)+(188106983549/103325000000000 : ℝ)*((2959/20000 : ℝ)+(5331/50000 : ℝ))=(10001290299525709/10000000000000000 : ℝ) by norm_num, show 1+(1664684964577543/4000000000000000000 : ℝ)+(2739156281537061/25000000000000000000 : ℝ)=(100052573749240586819/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1664684964577543/4000000000000000000 : ℝ) ≤ ((1652647130000757109/1653200000000000000 : ℝ)+2*(188106983549/103325000000000 : ℝ)*(2959/20000 : ℝ))^(8343/2048 : ℝ) := by
    rw [show (1652647130000757109/1653200000000000000 : ℝ)+2*(188106983549/103325000000000 : ℝ)*(2959/20000 : ℝ)=(2000408545491981/2000000000000000 : ℝ) by norm_num, show 1+2*(1664684964577543/4000000000000000000 : ℝ)=(2001664684964577543/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1652647130000757109/1653200000000000000 : ℝ)*(X 1 0+X 2 0)+(188106983549/103325000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (5331/50000 : ℝ)) (hi := (2959/20000 : ℝ)) (c := (1652647130000757109/1653200000000000000 : ℝ)) (alpha := (188106983549/103325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1652647130000757109/1653200000000000000 : ℝ)*(X 0 1+X 2 1)+(188106983549/103325000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (5331/50000 : ℝ)) (hi := (2959/20000 : ℝ)) (c := (1652647130000757109/1653200000000000000 : ℝ)) (alpha := (188106983549/103325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1652647130000757109/1653200000000000000 : ℝ)*(X 0 2+X 1 2)+(188106983549/103325000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (5331/50000 : ℝ)) (hi := (2959/20000 : ℝ)) (c := (1652647130000757109/1653200000000000000 : ℝ)) (alpha := (188106983549/103325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1080907047/5000000000 : ℝ)*X 0 0+(5401461271/10000000000 : ℝ)*X 0 1+(525780301/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673440553/5000000000 : ℝ)*X 1 0+(-2234813019/10000000000 : ℝ)*X 1 1+(5257803699/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346881147/10000000000 : ℝ)*X 2 0+(525780317/1000000000 : ℝ)*X 2 1+(-2234813663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4362956003/10000000000 : ℝ)*X 0 0+(4222132097/10000000000 : ℝ)*X 0 1+(2254221163/5000000000 : ℝ)*X 0 2+(4362956003/10000000000 : ℝ)*X 1 0+(4222132097/10000000000 : ℝ)*X 1 1+(2254221163/5000000000 : ℝ)*X 1 2+(4362956003/10000000000 : ℝ)*X 2 0+(4222132097/10000000000 : ℝ)*X 2 1+(2254221163/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-432364313/2000000000 : ℝ)*X 0 0+(5258210899/10000000000 : ℝ)*X 0 1+(5401051387/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310463149/10000000000 : ℝ)*X 1 0+(-261445579/1250000000 : ℝ)*X 1 1+(5401051313/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310463039/10000000000 : ℝ)*X 2 0+(5401051323/10000000000 : ℝ)*X 2 1+(-2091564767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4362969891/10000000000 : ℝ)*X 0 0+(4507628297/10000000000 : ℝ)*X 0 1+(2111474799/5000000000 : ℝ)*X 0 2+(4362969891/10000000000 : ℝ)*X 1 0+(4507628297/10000000000 : ℝ)*X 1 1+(2111474799/5000000000 : ℝ)*X 1 2+(4362969891/10000000000 : ℝ)*X 2 0+(4507628297/10000000000 : ℝ)*X 2 1+(2111474799/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1233471424029241502569040673/82660000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26282691/5000000000000 : ℝ)*(base19) + (1169805397/100000000000000 : ℝ)*(base23) + (94419/2500000000000 : ℝ)*(lower2) + (470374357/100000000000000 : ℝ)*(upper3) + (159828369/50000000000000 : ℝ)*(lower4) + (1306723898518351/25000000000000 : ℝ)*(major0) + (1306723898518351/25000000000000 : ℝ)*(major1) + (1045379118814681/20000000000000 : ℝ)*(major2) + (6961010434693981/100000000000000 : ℝ)*(sp0) + (870128494465941/12500000000000 : ℝ)*(sp1) + (6961027311575951/100000000000000 : ℝ)*(sp2) + (174636778707909/5000000000000 : ℝ)*(sp3) + (18046687367/100000000000000 : ℝ)*(sp4) + (5327039929/20000000000000 : ℝ)*(sp7) + (139710488374313/4000000000000 : ℝ)*(f.failure) + (1740257120345337/25000000000000 : ℝ)*(f.sum) + (7442640950299/2583125000000000000000000000 : ℝ)*base65 + (511320548848382741/41330000000000000000000000000000 : ℝ)*base68 + (83302923351208429/33064000000000000000000000000000 : ℝ)*base69 + (95352630972402741/41330000000000000000000000000000 : ℝ)*base72 + (163033119937/20665000000000000000000000000 : ℝ)*base73 + (779858401287296429/33064000000000000000000000000000 : ℝ)*base75 + (233040021139168741/41330000000000000000000000000000 : ℝ)*base78 + (903469526069041259/41330000000000000000000000000000 : ℝ)*base79 + (88829451400021/20665000000000000000000000000 : ℝ)*base82 + (129829/20000000000000000000 : ℝ)*base90 + (129829/20000000000000000000 : ℝ)*base92 + (329829/20000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (337261557034199383398526317/41330000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (294850779/12500000000000 : ℝ)*(base19) + (572227621/25000000000000 : ℝ)*(base23) + (4744971/6250000000000 : ℝ)*(upper2) + (143665463/100000000000000 : ℝ)*(upper3) + (305540937/100000000000000 : ℝ)*(upper5) + (5256773585291629/100000000000000 : ℝ)*(major0) + (5256773585291629/100000000000000 : ℝ)*(major1) + (5256773585291629/100000000000000 : ℝ)*(major2) + (12416700449/20000000000000 : ℝ)*(sp1) + (52190246593/100000000000000 : ℝ)*(sp2) + (56006554838227/800000000000 : ℝ)*(sp4) + (7000754912469897/100000000000000 : ℝ)*(sp5) + (7000764875621297/100000000000000 : ℝ)*(sp6) + (1756363771898903/50000000000000 : ℝ)*(sp7) + (1756363771898903/50000000000000 : ℝ)*(f.failure) + (56006554838227/800000000000 : ℝ)*(f.sum) + (64992666715069/20665000000000000000000000000 : ℝ)*base65 + (1495933214323836561/165320000000000000000000000000000 : ℝ)*base67 + (655659073700083439/165320000000000000000000000000000 : ℝ)*base70 + (214183735569996561/165320000000000000000000000000000 : ℝ)*base71 + (104229228812989/20665000000000000000000000000 : ℝ)*base73 + (910041531959796561/165320000000000000000000000000000 : ℝ)*base75 + (448439674113076561/165320000000000000000000000000000 : ℝ)*base77 + (3610141819366716561/165320000000000000000000000000000 : ℝ)*base79 + (12203474704833/10332500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3466299/250000000000000000000 : ℝ)*base90 + (3466299/250000000000000000000 : ℝ)*base92 + (3466299/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1151_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2959/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5331/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1151_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1151_s5_0 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-540608261/2500000000 : ℝ)*x 0 + (5394681319/10000000000 : ℝ)*x 1 + (1052835289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540608261/2500000000 : ℝ)^1043 ≤ (328510237509/2500000000000 : ℝ)^787 := by
    have hnat : (540608261 : ℕ)^1043*2500000000000^787 ≤ 328510237509^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540608261 2500000000 328510237509 2500000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394681319/10000000000 : ℝ)^1043 ≤ (22067241727253/50000000000000 : ℝ)^787 := by
    have hnat : (5394681319 : ℕ)^1043*50000000000000^787 ≤ 22067241727253^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394681319 10000000000 22067241727253 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052835289/2000000000 : ℝ)^1043 ≤ (41723737331/97656250000 : ℝ)^787 := by
    have hnat : (1052835289 : ℕ)^1043*97656250000^787 ≤ 41723737331^787*2000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052835289 2000000000 41723737331 97656250000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-540608261/2500000000 : ℝ), (5394681319/10000000000 : ℝ), (1052835289/2000000000 : ℝ)] ![(328510237509/2500000000000 : ℝ), (22067241727253/50000000000000 : ℝ), (41723737331/97656250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-540608261/2500000000 : ℝ)|^1043 ≤ (328510237509/2500000000000 : ℝ)^787
        have hw : |(-540608261/2500000000 : ℝ)|=(540608261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394681319/10000000000 : ℝ)|^1043 ≤ (22067241727253/50000000000000 : ℝ)^787
        have hw : |(5394681319/10000000000 : ℝ)|=(5394681319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052835289/2000000000 : ℝ)|^1043 ≤ (41723737331/97656250000 : ℝ)^787
        have hw : |(1052835289/2000000000 : ℝ)|=(1052835289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s5_1 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (167036851/312500000 : ℝ)*x 0 + (-557162789/2500000000 : ℝ)*x 1 + (5264176419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167036851/312500000 : ℝ)^1043 ≤ (1089964228511/2500000000000 : ℝ)^787 := by
    have hnat : (167036851 : ℕ)^1043*2500000000000^787 ≤ 1089964228511^787*312500000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167036851 312500000 1089964228511 2500000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (557162789/2500000000 : ℝ)^1043 ≤ (13676324091787/100000000000000 : ℝ)^787 := by
    have hnat : (557162789 : ℕ)^1043*100000000000000^787 ≤ 13676324091787^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557162789 2500000000 13676324091787 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264176419/10000000000 : ℝ)^1043 ≤ (534063834341/1250000000000 : ℝ)^787 := by
    have hnat : (5264176419 : ℕ)^1043*1250000000000^787 ≤ 534063834341^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264176419 10000000000 534063834341 1250000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167036851/312500000 : ℝ), (-557162789/2500000000 : ℝ), (5264176419/10000000000 : ℝ)] ![(1089964228511/2500000000000 : ℝ), (13676324091787/100000000000000 : ℝ), (534063834341/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167036851/312500000 : ℝ)|^1043 ≤ (1089964228511/2500000000000 : ℝ)^787
        have hw : |(167036851/312500000 : ℝ)|=(167036851/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-557162789/2500000000 : ℝ)|^1043 ≤ (13676324091787/100000000000000 : ℝ)^787
        have hw : |(-557162789/2500000000 : ℝ)|=(557162789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264176419/10000000000 : ℝ)|^1043 ≤ (534063834341/1250000000000 : ℝ)^787
        have hw : |(5264176419/10000000000 : ℝ)|=(5264176419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s5_2 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (668147409/1250000000 : ℝ)*x 0 + (5264176393/10000000000 : ℝ)*x 1 + (-1114325569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668147409/1250000000 : ℝ)^1043 ≤ (21799284786417/50000000000000 : ℝ)^787 := by
    have hnat : (668147409 : ℕ)^1043*50000000000000^787 ≤ 21799284786417^787*1250000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668147409 1250000000 21799284786417 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264176393/10000000000 : ℝ)^1043 ≤ (42725106467617/100000000000000 : ℝ)^787 := by
    have hnat : (5264176393 : ℕ)^1043*100000000000000^787 ≤ 42725106467617^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264176393 10000000000 42725106467617 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1114325569/5000000000 : ℝ)^1043 ≤ (13676323945397/100000000000000 : ℝ)^787 := by
    have hnat : (1114325569 : ℕ)^1043*100000000000000^787 ≤ 13676323945397^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114325569 5000000000 13676323945397 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668147409/1250000000 : ℝ), (5264176393/10000000000 : ℝ), (-1114325569/5000000000 : ℝ)] ![(21799284786417/50000000000000 : ℝ), (42725106467617/100000000000000 : ℝ), (13676323945397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668147409/1250000000 : ℝ)|^1043 ≤ (21799284786417/50000000000000 : ℝ)^787
        have hw : |(668147409/1250000000 : ℝ)|=(668147409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264176393/10000000000 : ℝ)|^1043 ≤ (42725106467617/100000000000000 : ℝ)^787
        have hw : |(5264176393/10000000000 : ℝ)|=(5264176393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1114325569/5000000000 : ℝ)|^1043 ≤ (13676323945397/100000000000000 : ℝ)^787
        have hw : |(-1114325569/5000000000 : ℝ)|=(1114325569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s5_3 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4363316209/10000000000 : ℝ)*x 0 + (264699579/625000000 : ℝ)*x 1 + (44952879/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4363316209/10000000000 : ℝ)^1043 ≤ (8329024595893/25000000000000 : ℝ)^787 := by
    have hnat : (4363316209 : ℕ)^1043*25000000000000^787 ≤ 8329024595893^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4363316209 10000000000 8329024595893 25000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264699579/625000000 : ℝ)^1043 ≤ (16012913696539/50000000000000 : ℝ)^787 := by
    have hnat : (264699579 : ℕ)^1043*50000000000000^787 ≤ 16012913696539^787*625000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264699579 625000000 16012913696539 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44952879/100000000 : ℝ)^1043 ≤ (541532409503/1562500000000 : ℝ)^787 := by
    have hnat : (44952879 : ℕ)^1043*1562500000000^787 ≤ 541532409503^787*100000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44952879 100000000 541532409503 1562500000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4363316209/10000000000 : ℝ), (264699579/625000000 : ℝ), (44952879/100000000 : ℝ)] ![(8329024595893/25000000000000 : ℝ), (16012913696539/50000000000000 : ℝ), (541532409503/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4363316209/10000000000 : ℝ)|^1043 ≤ (8329024595893/25000000000000 : ℝ)^787
        have hw : |(4363316209/10000000000 : ℝ)|=(4363316209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264699579/625000000 : ℝ)|^1043 ≤ (16012913696539/50000000000000 : ℝ)^787
        have hw : |(264699579/625000000 : ℝ)|=(264699579/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(44952879/100000000 : ℝ)|^1043 ≤ (541532409503/1562500000000 : ℝ)^787
        have hw : |(44952879/100000000 : ℝ)|=(44952879/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s5_4 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2162438129/10000000000 : ℝ)*x 0 + (526451379/1000000000 : ℝ)*x 1 + (5394342867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162438129/10000000000 : ℝ)^1043 ≤ (3285112612897/25000000000000 : ℝ)^787 := by
    have hnat : (2162438129 : ℕ)^1043*25000000000000^787 ≤ 3285112612897^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162438129 10000000000 3285112612897 25000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526451379/1000000000 : ℝ)^1043 ≤ (42728735643701/100000000000000 : ℝ)^787 := by
    have hnat : (526451379 : ℕ)^1043*100000000000000^787 ≤ 42728735643701^787*1000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526451379 1000000000 42728735643701 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394342867/10000000000 : ℝ)^1043 ≤ (44130813890369/100000000000000 : ℝ)^787 := by
    have hnat : (5394342867 : ℕ)^1043*100000000000000^787 ≤ 44130813890369^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394342867 10000000000 44130813890369 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2162438129/10000000000 : ℝ), (526451379/1000000000 : ℝ), (5394342867/10000000000 : ℝ)] ![(3285112612897/25000000000000 : ℝ), (42728735643701/100000000000000 : ℝ), (44130813890369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2162438129/10000000000 : ℝ)|^1043 ≤ (3285112612897/25000000000000 : ℝ)^787
        have hw : |(-2162438129/10000000000 : ℝ)|=(2162438129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526451379/1000000000 : ℝ)|^1043 ≤ (42728735643701/100000000000000 : ℝ)^787
        have hw : |(526451379/1000000000 : ℝ)|=(526451379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394342867/10000000000 : ℝ)|^1043 ≤ (44130813890369/100000000000000 : ℝ)^787
        have hw : |(5394342867/10000000000 : ℝ)|=(5394342867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s5_5 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312094083/10000000000 : ℝ)*x 0 + (-419696813/2000000000 : ℝ)*x 1 + (2697171487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312094083/10000000000 : ℝ)^1043 ≤ (43241284296619/100000000000000 : ℝ)^787 := by
    have hnat : (5312094083 : ℕ)^1043*100000000000000^787 ≤ 43241284296619^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312094083 10000000000 43241284296619 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (419696813/2000000000 : ℝ)^1043 ≤ (12627900637547/100000000000000 : ℝ)^787 := by
    have hnat : (419696813 : ℕ)^1043*100000000000000^787 ≤ 12627900637547^787*2000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419696813 2000000000 12627900637547 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697171487/5000000000 : ℝ)^1043 ≤ (44130815050473/100000000000000 : ℝ)^787 := by
    have hnat : (2697171487 : ℕ)^1043*100000000000000^787 ≤ 44130815050473^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697171487 5000000000 44130815050473 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312094083/10000000000 : ℝ), (-419696813/2000000000 : ℝ), (2697171487/5000000000 : ℝ)] ![(43241284296619/100000000000000 : ℝ), (12627900637547/100000000000000 : ℝ), (44130815050473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312094083/10000000000 : ℝ)|^1043 ≤ (43241284296619/100000000000000 : ℝ)^787
        have hw : |(5312094083/10000000000 : ℝ)|=(5312094083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-419696813/2000000000 : ℝ)|^1043 ≤ (12627900637547/100000000000000 : ℝ)^787
        have hw : |(-419696813/2000000000 : ℝ)|=(419696813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697171487/5000000000 : ℝ)|^1043 ≤ (44130815050473/100000000000000 : ℝ)^787
        have hw : |(2697171487/5000000000 : ℝ)|=(2697171487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s5_6 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2656046839/5000000000 : ℝ)*x 0 + (1348585817/2500000000 : ℝ)*x 1 + (-2098484213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656046839/5000000000 : ℝ)^1043 ≤ (5405159990933/12500000000000 : ℝ)^787 := by
    have hnat : (2656046839 : ℕ)^1043*12500000000000^787 ≤ 5405159990933^787*5000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656046839 5000000000 5405159990933 12500000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348585817/2500000000 : ℝ)^1043 ≤ (44130818238047/100000000000000 : ℝ)^787 := by
    have hnat : (1348585817 : ℕ)^1043*100000000000000^787 ≤ 44130818238047^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348585817 2500000000 44130818238047 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2098484213/10000000000 : ℝ)^1043 ≤ (12627901817859/100000000000000 : ℝ)^787 := by
    have hnat : (2098484213 : ℕ)^1043*100000000000000^787 ≤ 12627901817859^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098484213 10000000000 12627901817859 100000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656046839/5000000000 : ℝ), (1348585817/2500000000 : ℝ), (-2098484213/10000000000 : ℝ)] ![(5405159990933/12500000000000 : ℝ), (44130818238047/100000000000000 : ℝ), (12627901817859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656046839/5000000000 : ℝ)|^1043 ≤ (5405159990933/12500000000000 : ℝ)^787
        have hw : |(2656046839/5000000000 : ℝ)|=(2656046839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348585817/2500000000 : ℝ)|^1043 ≤ (44130818238047/100000000000000 : ℝ)^787
        have hw : |(1348585817/2500000000 : ℝ)|=(1348585817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2098484213/10000000000 : ℝ)|^1043 ≤ (12627901817859/100000000000000 : ℝ)^787
        have hw : |(-2098484213/10000000000 : ℝ)|=(2098484213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1151_s5_7 (p : ℝ) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1090831739/2500000000 : ℝ)*x 0 + (4494615951/10000000000 : ℝ)*x 1 + (4235867481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090831739/2500000000 : ℝ)^1043 ≤ (3331620713487/10000000000000 : ℝ)^787 := by
    have hnat : (1090831739 : ℕ)^1043*10000000000000^787 ≤ 3331620713487^787*2500000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090831739 2500000000 3331620713487 10000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4494615951/10000000000 : ℝ)^1043 ≤ (17325604274471/50000000000000 : ℝ)^787 := by
    have hnat : (4494615951 : ℕ)^1043*50000000000000^787 ≤ 17325604274471^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494615951 10000000000 17325604274471 50000000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4235867481/10000000000 : ℝ)^1043 ≤ (1001018259233/3125000000000 : ℝ)^787 := by
    have hnat : (4235867481 : ℕ)^1043*3125000000000^787 ≤ 1001018259233^787*10000000000^1043 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235867481 10000000000 1001018259233 3125000000000 1043 787 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1043/256 : ℝ)) 1043 787 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090831739/2500000000 : ℝ), (4494615951/10000000000 : ℝ), (4235867481/10000000000 : ℝ)] ![(3331620713487/10000000000000 : ℝ), (17325604274471/50000000000000 : ℝ), (1001018259233/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090831739/2500000000 : ℝ)|^1043 ≤ (3331620713487/10000000000000 : ℝ)^787
        have hw : |(1090831739/2500000000 : ℝ)|=(1090831739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4494615951/10000000000 : ℝ)|^1043 ≤ (17325604274471/50000000000000 : ℝ)^787
        have hw : |(4494615951/10000000000 : ℝ)|=(4494615951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4235867481/10000000000 : ℝ)|^1043 ≤ (1001018259233/3125000000000 : ℝ)^787
        have hw : |(4235867481/10000000000 : ℝ)|=(4235867481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1151_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (354/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14093/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1399/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1399/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1399/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1399/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1399/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1399/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1399/12500 : ℝ) ^ (8343/2048 : ℝ) ≤ (333769258275479/2500000000000000000 : ℝ) := by
    have hpowers : (1399/12500 : ℝ)^8343 ≤ (333769258275479/2500000000000000000 : ℝ)^2048 := by
      have hnat : (1399 : ℕ)^8343*2500000000000000000^2048 ≤ 333769258275479^2048*12500^8343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1399 12500 333769258275479 2500000000000000000 8343 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1399/12500 : ℝ)) (X := (333769258275479/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8343/2048 : ℝ) ≤ (35563667029450929/100000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8343 ≤ (35563667029450929/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8343*100000000000000000000^2048 ≤ 35563667029450929^2048*20000^8343 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 35563667029450929 100000000000000000000 8343 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (35563667029450929/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250333769258275479/1250000000000000000 : ℝ) ≤ (5000327695358231/5000000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (1250333769258275479/1250000000000000000 : ℝ)^2048 ≤ (5000327695358231/5000000000000000 : ℝ)^8343 := by
      have hnat : (1250333769258275479 : ℕ)^2048*5000000000000000^8343 ≤ 5000327695358231^8343*1250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250333769258275479 1250000000000000000 5000327695358231 5000000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000327695358231/5000000000000000 : ℝ)) (X := (1250333769258275479/1250000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048914437360470089/100000000000000000000 : ℝ) ≤ (10001200506853699/10000000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (100048914437360470089/100000000000000000000 : ℝ)^2048 ≤ (10001200506853699/10000000000000000 : ℝ)^8343 := by
      have hnat : (100048914437360470089 : ℕ)^2048*10000000000000000^8343 ≤ 10001200506853699^8343*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048914437360470089 100000000000000000000 10001200506853699 10000000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001200506853699/10000000000000000 : ℝ)) (X := (100048914437360470089/100000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035563667029450929/50000000000000000000 : ℝ) ≤ (1250218202873867/1250000000000000 : ℝ) ^ (8343/2048 : ℝ) := by
    have hpowers : (50035563667029450929/50000000000000000000 : ℝ)^2048 ≤ (1250218202873867/1250000000000000 : ℝ)^8343 := by
      have hnat : (50035563667029450929 : ℕ)^2048*1250000000000000^8343 ≤ 1250218202873867^8343*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035563667029450929 50000000000000000000 1250218202873867 1250000000000000 2048 8343 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250218202873867/1250000000000000 : ℝ)) (X := (50035563667029450929/50000000000000000000 : ℝ)) (by norm_num) 8343 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(333769258275479/2500000000000000000 : ℝ) ≤ ((15209896237167140429/15215000000000000000 : ℝ)+2*(545116137237/304300000000000 : ℝ)*(1399/12500 : ℝ))^(8343/2048 : ℝ) := by
    rw [show (15209896237167140429/15215000000000000000 : ℝ)+2*(545116137237/304300000000000 : ℝ)*(1399/12500 : ℝ)=(5000327695358231/5000000000000000 : ℝ) by norm_num, show 1+2*(333769258275479/2500000000000000000 : ℝ)=(1250333769258275479/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35563667029450929/100000000000000000000 : ℝ)+(333769258275479/2500000000000000000 : ℝ) ≤ ((15209896237167140429/15215000000000000000 : ℝ)+(545116137237/304300000000000 : ℝ)*((2847/20000 : ℝ)+(1399/12500 : ℝ)))^(8343/2048 : ℝ) := by
    rw [show (15209896237167140429/15215000000000000000 : ℝ)+(545116137237/304300000000000 : ℝ)*((2847/20000 : ℝ)+(1399/12500 : ℝ))=(10001200506853699/10000000000000000 : ℝ) by norm_num, show 1+(35563667029450929/100000000000000000000 : ℝ)+(333769258275479/2500000000000000000 : ℝ)=(100048914437360470089/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35563667029450929/100000000000000000000 : ℝ) ≤ ((15209896237167140429/15215000000000000000 : ℝ)+2*(545116137237/304300000000000 : ℝ)*(2847/20000 : ℝ))^(8343/2048 : ℝ) := by
    rw [show (15209896237167140429/15215000000000000000 : ℝ)+2*(545116137237/304300000000000 : ℝ)*(2847/20000 : ℝ)=(1250218202873867/1250000000000000 : ℝ) by norm_num, show 1+2*(35563667029450929/100000000000000000000 : ℝ)=(50035563667029450929/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15209896237167140429/15215000000000000000 : ℝ)*(X 1 0+X 2 0)+(545116137237/304300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (1399/12500 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (15209896237167140429/15215000000000000000 : ℝ)) (alpha := (545116137237/304300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15209896237167140429/15215000000000000000 : ℝ)*(X 0 1+X 2 1)+(545116137237/304300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (1399/12500 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (15209896237167140429/15215000000000000000 : ℝ)) (alpha := (545116137237/304300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15209896237167140429/15215000000000000000 : ℝ)*(X 0 2+X 1 2)+(545116137237/304300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8343/2048 : ℝ)) (lo := (1399/12500 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (15209896237167140429/15215000000000000000 : ℝ)) (alpha := (545116137237/304300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-540608261/2500000000 : ℝ)*X 0 0+(5394681319/10000000000 : ℝ)*X 0 1+(1052835289/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167036851/312500000 : ℝ)*X 1 0+(-557162789/2500000000 : ℝ)*X 1 1+(5264176419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668147409/1250000000 : ℝ)*X 2 0+(5264176393/10000000000 : ℝ)*X 2 1+(-1114325569/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4363316209/10000000000 : ℝ)*X 0 0+(264699579/625000000 : ℝ)*X 0 1+(44952879/100000000 : ℝ)*X 0 2+(4363316209/10000000000 : ℝ)*X 1 0+(264699579/625000000 : ℝ)*X 1 1+(44952879/100000000 : ℝ)*X 1 2+(4363316209/10000000000 : ℝ)*X 2 0+(264699579/625000000 : ℝ)*X 2 1+(44952879/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2162438129/10000000000 : ℝ)*X 0 0+(526451379/1000000000 : ℝ)*X 0 1+(5394342867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312094083/10000000000 : ℝ)*X 1 0+(-419696813/2000000000 : ℝ)*X 1 1+(2697171487/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656046839/5000000000 : ℝ)*X 2 0+(1348585817/2500000000 : ℝ)*X 2 1+(-2098484213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1090831739/2500000000 : ℝ)*X 0 0+(4494615951/10000000000 : ℝ)*X 0 1+(4235867481/10000000000 : ℝ)*X 0 2+(1090831739/2500000000 : ℝ)*X 1 0+(4494615951/10000000000 : ℝ)*X 1 1+(4235867481/10000000000 : ℝ)*X 1 2+(1090831739/2500000000 : ℝ)*X 2 0+(4494615951/10000000000 : ℝ)*X 2 1+(4235867481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1151_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7412942331299837925033651021/760750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (406519489/25000000000000 : ℝ)*(base19) + (1546360653/100000000000000 : ℝ)*(base23) + (73260847/100000000000000 : ℝ)*(lower2) + (214290579/100000000000000 : ℝ)*(upper3) + (151969511/100000000000000 : ℝ)*(upper5) + (1438428746114443/25000000000000 : ℝ)*(major0) + (1438428746114443/25000000000000 : ℝ)*(major1) + (5753714984457773/100000000000000 : ℝ)*(major2) + (19156475934599/250000000000 : ℝ)*(sp0) + (766262991570681/10000000000000 : ℝ)*(sp1) + (7662629995424113/100000000000000 : ℝ)*(sp2) + (1922387538631789/50000000000000 : ℝ)*(sp3) + (8233589033/20000000000000 : ℝ)*(sp4) + (1439066167/6250000000000 : ℝ)*(sp7) + (15379192409289/400000000000 : ℝ)*(f.failure) + (3831315770892383/50000000000000 : ℝ)*(f.sum) + (22911411285381/6086000000000000000000000000 : ℝ)*base66 + (169014412273581091/22375000000000000000000000000000 : ℝ)*base67 + (38306441061839304617/1521500000000000000000000000000000 : ℝ)*base69 + (249117029966081091/22375000000000000000000000000000 : ℝ)*base71 + (8412634618311/6086000000000000000000000000 : ℝ)*base74 + (37505214087636804617/1521500000000000000000000000000000 : ℝ)*base75 + (3374760191696916047/380375000000000000000000000000000 : ℝ)*base77 + (6613578724018291047/380375000000000000000000000000000 : ℝ)*base79 + (7527044697103/7607500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4037/2000000000000000000 : ℝ)*base90 + (4037/2000000000000000000 : ℝ)*base92 + (24037/2000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (580936908608114519019/59433593750000000000000000 : ℝ) := by norm_num
    linear_combination (282962433/12500000000000 : ℝ)*(base19) + (1172232959/50000000000000 : ℝ)*(base23) + (140957121/50000000000000 : ℝ)*(upper3) + (62054053/20000000000000 : ℝ)*(lower4) + (13348183/50000000000000 : ℝ)*(upper5) + (5783582575229541/100000000000000 : ℝ)*(major0) + (5783582575229541/100000000000000 : ℝ)*(major1) + (5783582575229541/100000000000000 : ℝ)*(major2) + (64769622371/100000000000000 : ℝ)*(sp1) + (9780402389/12500000000000 : ℝ)*(sp2) + (7702408337756287/100000000000000 : ℝ)*(sp4) + (1925585326108613/25000000000000 : ℝ)*(sp5) + (3851163875035629/50000000000000 : ℝ)*(sp6) + (3864756486884299/100000000000000 : ℝ)*(sp7) + (3864756486884299/100000000000000 : ℝ)*(f.failure) + (7702408337756287/100000000000000 : ℝ)*(f.sum) + (17013918443351/7607500000000000000000000000 : ℝ)*base65 + (9003816166468563089/1521500000000000000000000000000000 : ℝ)*base67 + (4997882294735063089/1521500000000000000000000000000000 : ℝ)*base69 + (4235758539120936911/1521500000000000000000000000000000 : ℝ)*base72 + (9183559710889/7607500000000000000000000000 : ℝ)*base74 + (4115480963073063089/1521500000000000000000000000000000 : ℝ)*base75 + (3635689285320936911/1521500000000000000000000000000000 : ℝ)*base78 + (3561820881776436911/1521500000000000000000000000000000 : ℝ)*base80 + (25368592190141/7607500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4914367/500000000000000000000 : ℝ)*base90 + (4914367/500000000000000000000 : ℝ)*base92 + (4914367/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1151_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1399/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1151_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1151_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4119/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9111/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1151_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1151_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1151_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8343/2048 : ℝ) ≤ p) (hpb : p ≤ (1043/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7482467/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4119/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9111/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (354/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1151_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

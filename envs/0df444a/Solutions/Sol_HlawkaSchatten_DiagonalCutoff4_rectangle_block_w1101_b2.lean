-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1101_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:01:28.640081+00:00
-- url     : https://prove2.me/submissions/2044e551-be21-4ade-9cc1-069498b17ef6

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
theorem support_rectangle_w1101_s6_0 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2186608809/10000000000 : ℝ)*x 0 + (674275379/1250000000 : ℝ)*x 1 + (5264643303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186608809/10000000000 : ℝ)^4147 ≤ (531310902683/4000000000000 : ℝ)^3123 := by
    have hnat : (2186608809 : ℕ)^4147*4000000000000^3123 ≤ 531310902683^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186608809 10000000000 531310902683 4000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674275379/1250000000 : ℝ)^4147 ≤ (2753651562069/6250000000000 : ℝ)^3123 := by
    have hnat : (674275379 : ℕ)^4147*6250000000000^3123 ≤ 2753651562069^3123*1250000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674275379 1250000000 2753651562069 6250000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264643303/10000000000 : ℝ)^4147 ≤ (341270419341/800000000000 : ℝ)^3123 := by
    have hnat : (5264643303 : ℕ)^4147*800000000000^3123 ≤ 341270419341^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264643303 10000000000 341270419341 800000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2186608809/10000000000 : ℝ), (674275379/1250000000 : ℝ), (5264643303/10000000000 : ℝ)] ![(531310902683/4000000000000 : ℝ), (2753651562069/6250000000000 : ℝ), (341270419341/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2186608809/10000000000 : ℝ)|^4147 ≤ (531310902683/4000000000000 : ℝ)^3123
        have hw : |(-2186608809/10000000000 : ℝ)|=(2186608809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674275379/1250000000 : ℝ)|^4147 ≤ (2753651562069/6250000000000 : ℝ)^3123
        have hw : |(674275379/1250000000 : ℝ)|=(674275379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264643303/10000000000 : ℝ)|^4147 ≤ (341270419341/800000000000 : ℝ)^3123
        have hw : |(5264643303/10000000000 : ℝ)|=(5264643303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s6_1 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345003219/10000000000 : ℝ)*x 0 + (-2252340623/10000000000 : ℝ)*x 1 + (526464327/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345003219/10000000000 : ℝ)^4147 ≤ (43525610594001/100000000000000 : ℝ)^3123 := by
    have hnat : (5345003219 : ℕ)^4147*100000000000000^3123 ≤ 43525610594001^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345003219 10000000000 43525610594001 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252340623/10000000000 : ℝ)^4147 ≤ (6907793664037/50000000000000 : ℝ)^3123 := by
    have hnat : (2252340623 : ℕ)^4147*50000000000000^3123 ≤ 6907793664037^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252340623 10000000000 6907793664037 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526464327/1000000000 : ℝ)^4147 ≤ (21329401031277/50000000000000 : ℝ)^3123 := by
    have hnat : (526464327 : ℕ)^4147*50000000000000^3123 ≤ 21329401031277^3123*1000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526464327 1000000000 21329401031277 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345003219/10000000000 : ℝ), (-2252340623/10000000000 : ℝ), (526464327/1000000000 : ℝ)] ![(43525610594001/100000000000000 : ℝ), (6907793664037/50000000000000 : ℝ), (21329401031277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345003219/10000000000 : ℝ)|^4147 ≤ (43525610594001/100000000000000 : ℝ)^3123
        have hw : |(5345003219/10000000000 : ℝ)|=(5345003219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2252340623/10000000000 : ℝ)|^4147 ≤ (6907793664037/50000000000000 : ℝ)^3123
        have hw : |(-2252340623/10000000000 : ℝ)|=(2252340623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526464327/1000000000 : ℝ)|^4147 ≤ (21329401031277/50000000000000 : ℝ)^3123
        have hw : |(526464327/1000000000 : ℝ)|=(526464327/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s6_2 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345003251/10000000000 : ℝ)*x 0 + (5264643269/10000000000 : ℝ)*x 1 + (-2252340583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345003251/10000000000 : ℝ)^4147 ≤ (43525610940027/100000000000000 : ℝ)^3123 := by
    have hnat : (5345003251 : ℕ)^4147*100000000000000^3123 ≤ 43525610940027^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345003251 10000000000 43525610940027 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264643269/10000000000 : ℝ)^4147 ≤ (21329401025897/50000000000000 : ℝ)^3123 := by
    have hnat : (5264643269 : ℕ)^4147*50000000000000^3123 ≤ 21329401025897^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264643269 10000000000 21329401025897 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252340583/10000000000 : ℝ)^4147 ≤ (13815587002269/100000000000000 : ℝ)^3123 := by
    have hnat : (2252340583 : ℕ)^4147*100000000000000^3123 ≤ 13815587002269^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252340583 10000000000 13815587002269 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345003251/10000000000 : ℝ), (5264643269/10000000000 : ℝ), (-2252340583/10000000000 : ℝ)] ![(43525610940027/100000000000000 : ℝ), (21329401025897/50000000000000 : ℝ), (13815587002269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345003251/10000000000 : ℝ)|^4147 ≤ (43525610940027/100000000000000 : ℝ)^3123
        have hw : |(5345003251/10000000000 : ℝ)|=(5345003251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264643269/10000000000 : ℝ)|^4147 ≤ (21329401025897/50000000000000 : ℝ)^3123
        have hw : |(5264643269/10000000000 : ℝ)|=(5264643269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2252340583/10000000000 : ℝ)|^4147 ≤ (13815587002269/100000000000000 : ℝ)^3123
        have hw : |(-2252340583/10000000000 : ℝ)|=(2252340583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s6_3 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2185229867/5000000000 : ℝ)*x 0 + (4244495937/10000000000 : ℝ)*x 1 + (1125045149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185229867/5000000000 : ℝ)^4147 ≤ (4164564846893/12500000000000 : ℝ)^3123 := by
    have hnat : (2185229867 : ℕ)^4147*12500000000000^3123 ≤ 4164564846893^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185229867 5000000000 4164564846893 12500000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4244495937/10000000000 : ℝ)^4147 ≤ (2002968423481/6250000000000 : ℝ)^3123 := by
    have hnat : (4244495937 : ℕ)^4147*6250000000000^3123 ≤ 2002968423481^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244495937 10000000000 2002968423481 6250000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125045149/2500000000 : ℝ)^4147 ≤ (34635986431027/100000000000000 : ℝ)^3123 := by
    have hnat : (1125045149 : ℕ)^4147*100000000000000^3123 ≤ 34635986431027^3123*2500000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125045149 2500000000 34635986431027 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185229867/5000000000 : ℝ), (4244495937/10000000000 : ℝ), (1125045149/2500000000 : ℝ)] ![(4164564846893/12500000000000 : ℝ), (2002968423481/6250000000000 : ℝ), (34635986431027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185229867/5000000000 : ℝ)|^4147 ≤ (4164564846893/12500000000000 : ℝ)^3123
        have hw : |(2185229867/5000000000 : ℝ)|=(2185229867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4244495937/10000000000 : ℝ)|^4147 ≤ (2002968423481/6250000000000 : ℝ)^3123
        have hw : |(4244495937/10000000000 : ℝ)|=(4244495937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125045149/2500000000 : ℝ)|^4147 ≤ (34635986431027/100000000000000 : ℝ)^3123
        have hw : |(1125045149/2500000000 : ℝ)|=(1125045149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s6_4 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1093306937/5000000000 : ℝ)*x 0 + (1316242611/2500000000 : ℝ)*x 1 + (1348468679/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093306937/5000000000 : ℝ)^4147 ≤ (66414067117/500000000000 : ℝ)^3123 := by
    have hnat : (1093306937 : ℕ)^4147*500000000000^3123 ≤ 66414067117^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093306937 5000000000 66414067117 500000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316242611/2500000000 : ℝ)^4147 ≤ (42662322405437/100000000000000 : ℝ)^3123 := by
    have hnat : (1316242611 : ℕ)^4147*100000000000000^3123 ≤ 42662322405437^3123*2500000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316242611 2500000000 42662322405437 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348468679/2500000000 : ℝ)^4147 ≤ (44054864161429/100000000000000 : ℝ)^3123 := by
    have hnat : (1348468679 : ℕ)^4147*100000000000000^3123 ≤ 44054864161429^3123*2500000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348468679 2500000000 44054864161429 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1093306937/5000000000 : ℝ), (1316242611/2500000000 : ℝ), (1348468679/2500000000 : ℝ)] ![(66414067117/500000000000 : ℝ), (42662322405437/100000000000000 : ℝ), (44054864161429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1093306937/5000000000 : ℝ)|^4147 ≤ (66414067117/500000000000 : ℝ)^3123
        have hw : |(-1093306937/5000000000 : ℝ)|=(1093306937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316242611/2500000000 : ℝ)|^4147 ≤ (42662322405437/100000000000000 : ℝ)^3123
        have hw : |(1316242611/2500000000 : ℝ)|=(1316242611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348468679/2500000000 : ℝ)|^4147 ≤ (44054864161429/100000000000000 : ℝ)^3123
        have hw : |(1348468679/2500000000 : ℝ)|=(1348468679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s6_5 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656140103/5000000000 : ℝ)*x 0 + (-265388647/1250000000 : ℝ)*x 1 + (1348468679/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656140103/5000000000 : ℝ)^4147 ≤ (5396515238549/12500000000000 : ℝ)^3123 := by
    have hnat : (2656140103 : ℕ)^4147*12500000000000^3123 ≤ 5396515238549^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656140103 5000000000 5396515238549 12500000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265388647/1250000000 : ℝ)^4147 ≤ (3193253476783/25000000000000 : ℝ)^3123 := by
    have hnat : (265388647 : ℕ)^4147*25000000000000^3123 ≤ 3193253476783^3123*1250000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265388647 1250000000 3193253476783 25000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348468679/2500000000 : ℝ)^4147 ≤ (44054864161429/100000000000000 : ℝ)^3123 := by
    have hnat : (1348468679 : ℕ)^4147*100000000000000^3123 ≤ 44054864161429^3123*2500000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348468679 2500000000 44054864161429 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656140103/5000000000 : ℝ), (-265388647/1250000000 : ℝ), (1348468679/2500000000 : ℝ)] ![(5396515238549/12500000000000 : ℝ), (3193253476783/25000000000000 : ℝ), (44054864161429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656140103/5000000000 : ℝ)|^4147 ≤ (5396515238549/12500000000000 : ℝ)^3123
        have hw : |(2656140103/5000000000 : ℝ)|=(2656140103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-265388647/1250000000 : ℝ)|^4147 ≤ (3193253476783/25000000000000 : ℝ)^3123
        have hw : |(-265388647/1250000000 : ℝ)|=(265388647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348468679/2500000000 : ℝ)|^4147 ≤ (44054864161429/100000000000000 : ℝ)^3123
        have hw : |(1348468679/2500000000 : ℝ)|=(1348468679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s6_6 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656140103/5000000000 : ℝ)*x 0 + (1348468679/2500000000 : ℝ)*x 1 + (-265388647/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656140103/5000000000 : ℝ)^4147 ≤ (5396515238549/12500000000000 : ℝ)^3123 := by
    have hnat : (2656140103 : ℕ)^4147*12500000000000^3123 ≤ 5396515238549^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656140103 5000000000 5396515238549 12500000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348468679/2500000000 : ℝ)^4147 ≤ (44054864161429/100000000000000 : ℝ)^3123 := by
    have hnat : (1348468679 : ℕ)^4147*100000000000000^3123 ≤ 44054864161429^3123*2500000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348468679 2500000000 44054864161429 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265388647/1250000000 : ℝ)^4147 ≤ (3193253476783/25000000000000 : ℝ)^3123 := by
    have hnat : (265388647 : ℕ)^4147*25000000000000^3123 ≤ 3193253476783^3123*1250000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265388647 1250000000 3193253476783 25000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656140103/5000000000 : ℝ), (1348468679/2500000000 : ℝ), (-265388647/1250000000 : ℝ)] ![(5396515238549/12500000000000 : ℝ), (44054864161429/100000000000000 : ℝ), (3193253476783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656140103/5000000000 : ℝ)|^4147 ≤ (5396515238549/12500000000000 : ℝ)^3123
        have hw : |(2656140103/5000000000 : ℝ)|=(2656140103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348468679/2500000000 : ℝ)|^4147 ≤ (44054864161429/100000000000000 : ℝ)^3123
        have hw : |(1348468679/2500000000 : ℝ)|=(1348468679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-265388647/1250000000 : ℝ)|^4147 ≤ (3193253476783/25000000000000 : ℝ)^3123
        have hw : |(-265388647/1250000000 : ℝ)|=(265388647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s6_7 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1092617427/2500000000 : ℝ)*x 0 + (4499534959/10000000000 : ℝ)*x 1 + (169805759/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092617427/2500000000 : ℝ)^4147 ≤ (4164577467321/12500000000000 : ℝ)^3123 := by
    have hnat : (1092617427 : ℕ)^4147*12500000000000^3123 ≤ 4164577467321^3123*2500000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092617427 2500000000 4164577467321 12500000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4499534959/10000000000 : ℝ)^4147 ≤ (34629388042797/100000000000000 : ℝ)^3123 := by
    have hnat : (4499534959 : ℕ)^4147*100000000000000^3123 ≤ 34629388042797^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499534959 10000000000 34629388042797 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169805759/400000000 : ℝ)^4147 ≤ (4006749025241/12500000000000 : ℝ)^3123 := by
    have hnat : (169805759 : ℕ)^4147*12500000000000^3123 ≤ 4006749025241^3123*400000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169805759 400000000 4006749025241 12500000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092617427/2500000000 : ℝ), (4499534959/10000000000 : ℝ), (169805759/400000000 : ℝ)] ![(4164577467321/12500000000000 : ℝ), (34629388042797/100000000000000 : ℝ), (4006749025241/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092617427/2500000000 : ℝ)|^4147 ≤ (4164577467321/12500000000000 : ℝ)^3123
        have hw : |(1092617427/2500000000 : ℝ)|=(1092617427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4499534959/10000000000 : ℝ)|^4147 ≤ (34629388042797/100000000000000 : ℝ)^3123
        have hw : |(4499534959/10000000000 : ℝ)|=(4499534959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169805759/400000000 : ℝ)|^4147 ≤ (4006749025241/12500000000000 : ℝ)^3123
        have hw : |(169805759/400000000 : ℝ)|=(169805759/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1101_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7433719/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5627/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1129/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7017/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1759/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5627/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1759/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5627/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1759/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5627/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1759/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5627/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1759/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5627/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1759/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5627/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5627/50000 : ℝ) ^ (8293/2048 : ℝ) ≤ (720131011778371/5000000000000000000 : ℝ) := by
    have hpowers : (5627/50000 : ℝ)^8293 ≤ (720131011778371/5000000000000000000 : ℝ)^2048 := by
      have hnat : (5627 : ℕ)^8293*5000000000000000000^2048 ≤ 720131011778371^2048*50000^8293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5627 50000 720131011778371 5000000000000000000 8293 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5627/50000 : ℝ)) (X := (720131011778371/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1759/12500 : ℝ) ^ (8293/2048 : ℝ) ≤ (35597809592908799/100000000000000000000 : ℝ) := by
    have hpowers : (1759/12500 : ℝ)^8293 ≤ (35597809592908799/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1759 : ℕ)^8293*100000000000000000000^2048 ≤ 35597809592908799^2048*12500^8293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1759 12500 35597809592908799 100000000000000000000 8293 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1759/12500 : ℝ)) (X := (35597809592908799/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500720131011778371/2500000000000000000 : ℝ) ≤ (10000711283435117/10000000000000000 : ℝ) ^ (8293/2048 : ℝ) := by
    have hpowers : (2500720131011778371/2500000000000000000 : ℝ)^2048 ≤ (10000711283435117/10000000000000000 : ℝ)^8293 := by
      have hnat : (2500720131011778371 : ℕ)^2048*10000000000000000^8293 ≤ 10000711283435117^8293*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500720131011778371 2500000000000000000 10000711283435117 10000000000000000 2048 8293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000711283435117/10000000000000000 : ℝ)) (X := (2500720131011778371/2500000000000000000 : ℝ)) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050000429828476219/100000000000000000000 : ℝ) ≤ (5000617277267833/5000000000000000 : ℝ) ^ (8293/2048 : ℝ) := by
    have hpowers : (100050000429828476219/100000000000000000000 : ℝ)^2048 ≤ (5000617277267833/5000000000000000 : ℝ)^8293 := by
      have hnat : (100050000429828476219 : ℕ)^2048*5000000000000000^8293 ≤ 5000617277267833^8293*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050000429828476219 100000000000000000000 5000617277267833 5000000000000000 2048 8293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000617277267833/5000000000000000 : ℝ)) (X := (100050000429828476219/100000000000000000000 : ℝ)) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035597809592908799/50000000000000000000 : ℝ) ≤ (2000351565127243/2000000000000000 : ℝ) ^ (8293/2048 : ℝ) := by
    have hpowers : (50035597809592908799/50000000000000000000 : ℝ)^2048 ≤ (2000351565127243/2000000000000000 : ℝ)^8293 := by
      have hnat : (50035597809592908799 : ℕ)^2048*2000000000000000^8293 ≤ 2000351565127243^8293*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035597809592908799 50000000000000000000 2000351565127243 2000000000000000 2048 8293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000351565127243/2000000000000000 : ℝ)) (X := (50035597809592908799/50000000000000000000 : ℝ)) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(720131011778371/5000000000000000000 : ℝ) ≤ ((14085113305394501407/14090000000000000000 : ℝ)+2*(523271100549/281800000000000 : ℝ)*(5627/50000 : ℝ))^(8293/2048 : ℝ) := by
    rw [show (14085113305394501407/14090000000000000000 : ℝ)+2*(523271100549/281800000000000 : ℝ)*(5627/50000 : ℝ)=(10000711283435117/10000000000000000 : ℝ) by norm_num, show 1+2*(720131011778371/5000000000000000000 : ℝ)=(2500720131011778371/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35597809592908799/100000000000000000000 : ℝ)+(720131011778371/5000000000000000000 : ℝ) ≤ ((14085113305394501407/14090000000000000000 : ℝ)+(523271100549/281800000000000 : ℝ)*((1759/12500 : ℝ)+(5627/50000 : ℝ)))^(8293/2048 : ℝ) := by
    rw [show (14085113305394501407/14090000000000000000 : ℝ)+(523271100549/281800000000000 : ℝ)*((1759/12500 : ℝ)+(5627/50000 : ℝ))=(5000617277267833/5000000000000000 : ℝ) by norm_num, show 1+(35597809592908799/100000000000000000000 : ℝ)+(720131011778371/5000000000000000000 : ℝ)=(100050000429828476219/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35597809592908799/100000000000000000000 : ℝ) ≤ ((14085113305394501407/14090000000000000000 : ℝ)+2*(523271100549/281800000000000 : ℝ)*(1759/12500 : ℝ))^(8293/2048 : ℝ) := by
    rw [show (14085113305394501407/14090000000000000000 : ℝ)+2*(523271100549/281800000000000 : ℝ)*(1759/12500 : ℝ)=(2000351565127243/2000000000000000 : ℝ) by norm_num, show 1+2*(35597809592908799/100000000000000000000 : ℝ)=(50035597809592908799/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14085113305394501407/14090000000000000000 : ℝ)*(X 1 0+X 2 0)+(523271100549/281800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8293/2048 : ℝ)) (lo := (5627/50000 : ℝ)) (hi := (1759/12500 : ℝ)) (c := (14085113305394501407/14090000000000000000 : ℝ)) (alpha := (523271100549/281800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14085113305394501407/14090000000000000000 : ℝ)*(X 0 1+X 2 1)+(523271100549/281800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8293/2048 : ℝ)) (lo := (5627/50000 : ℝ)) (hi := (1759/12500 : ℝ)) (c := (14085113305394501407/14090000000000000000 : ℝ)) (alpha := (523271100549/281800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14085113305394501407/14090000000000000000 : ℝ)*(X 0 2+X 1 2)+(523271100549/281800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8293/2048 : ℝ)) (lo := (5627/50000 : ℝ)) (hi := (1759/12500 : ℝ)) (c := (14085113305394501407/14090000000000000000 : ℝ)) (alpha := (523271100549/281800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2186608809/10000000000 : ℝ)*X 0 0+(674275379/1250000000 : ℝ)*X 0 1+(5264643303/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345003219/10000000000 : ℝ)*X 1 0+(-2252340623/10000000000 : ℝ)*X 1 1+(526464327/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345003251/10000000000 : ℝ)*X 2 0+(5264643269/10000000000 : ℝ)*X 2 1+(-2252340583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2185229867/5000000000 : ℝ)*X 0 0+(4244495937/10000000000 : ℝ)*X 0 1+(1125045149/2500000000 : ℝ)*X 0 2+(2185229867/5000000000 : ℝ)*X 1 0+(4244495937/10000000000 : ℝ)*X 1 1+(1125045149/2500000000 : ℝ)*X 1 2+(2185229867/5000000000 : ℝ)*X 2 0+(4244495937/10000000000 : ℝ)*X 2 1+(1125045149/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1093306937/5000000000 : ℝ)*X 0 0+(1316242611/2500000000 : ℝ)*X 0 1+(1348468679/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656140103/5000000000 : ℝ)*X 1 0+(-265388647/1250000000 : ℝ)*X 1 1+(1348468679/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656140103/5000000000 : ℝ)*X 2 0+(1348468679/2500000000 : ℝ)*X 2 1+(-265388647/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1092617427/2500000000 : ℝ)*X 0 0+(4499534959/10000000000 : ℝ)*X 0 1+(169805759/400000000 : ℝ)*X 0 2+(1092617427/2500000000 : ℝ)*X 1 0+(4499534959/10000000000 : ℝ)*X 1 1+(169805759/400000000 : ℝ)*X 1 2+(1092617427/2500000000 : ℝ)*X 2 0+(4499534959/10000000000 : ℝ)*X 2 1+(169805759/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (964210580996489983351826913/176125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (611682811/50000000000000 : ℝ)*(base19) + (1178526293/100000000000000 : ℝ)*(base23) + (48665869/100000000000000 : ℝ)*(lower2) + (126676763/100000000000000 : ℝ)*(upper3) + (65809451/50000000000000 : ℝ)*(upper5) + (2907403514320747/50000000000000 : ℝ)*(major0) + (2907403514320747/50000000000000 : ℝ)*(major1) + (2907403514320747/50000000000000 : ℝ)*(major2) + (7718478566057563/100000000000000 : ℝ)*(sp0) + (7718510396529373/100000000000000 : ℝ)*(sp1) + (7718510441368703/100000000000000 : ℝ)*(sp2) + (977771150319139/25000000000000 : ℝ)*(sp3) + (33053837433/100000000000000 : ℝ)*(sp4) + (8826812697/50000000000000 : ℝ)*(sp7) + (78222045098039/2000000000000 : ℝ)*(f.failure) + (1929627904973749/25000000000000 : ℝ)*(f.sum) + (287425643121/55039062500000000000000000 : ℝ)*base65 + (3363889559758941029/704500000000000000000000000000000 : ℝ)*base67 + (3567039139602441029/704500000000000000000000000000000 : ℝ)*base69 + (12951183726402441029/704500000000000000000000000000000 : ℝ)*base71 + (3255014498163/1761250000000000000000000000 : ℝ)*base74 + (6294669336583941029/704500000000000000000000000000000 : ℝ)*base75 + (7800160282255441029/704500000000000000000000000000000 : ℝ)*base77 + (1743206247316558971/704500000000000000000000000000000 : ℝ)*base80 + (10305849745319/3522500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (22959/10000000000000000000 : ℝ)*base90 + (22959/10000000000000000000 : ℝ)*base92 + (22959/10000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1564943798553933068198195703/352250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (412414591/50000000000000 : ℝ)*(base19) + (448375947/50000000000000 : ℝ)*(base23) + (89675181/100000000000000 : ℝ)*(upper3) + (32652597/100000000000000 : ℝ)*(lower4) + (90664539/100000000000000 : ℝ)*(upper5) + (2922162693809919/50000000000000 : ℝ)*(major0) + (2922162693809919/50000000000000 : ℝ)*(major1) + (2922162693809919/50000000000000 : ℝ)*(major2) + (11229908941/50000000000000 : ℝ)*(sp1) + (377457873/1562500000000 : ℝ)*(sp2) + (3878847001971913/50000000000000 : ℝ)*(sp4) + (3878835359648381/50000000000000 : ℝ)*(sp5) + (387883447494403/5000000000000 : ℝ)*(sp6) + (245684788950349/6250000000000 : ℝ)*(sp7) + (245684788950349/6250000000000 : ℝ)*(f.failure) + (3878847001971913/50000000000000 : ℝ)*(f.sum) + (16179880369871/7045000000000000000000000000 : ℝ)*base65 + (3905609581412606033/704500000000000000000000000000000 : ℝ)*base67 + (13516701505140606033/704500000000000000000000000000000 : ℝ)*base69 + (4814685953403606033/704500000000000000000000000000000 : ℝ)*base71 + (21102928271079/7045000000000000000000000000 : ℝ)*base74 + (14641280542518606033/704500000000000000000000000000000 : ℝ)*base75 + (4932779103044606033/704500000000000000000000000000000 : ℝ)*base77 + (9928767708584606033/704500000000000000000000000000000 : ℝ)*base79 + (18314362323349/7045000000000000000000000000 : ℝ)*base82 + (42931/31250000000000000000 : ℝ)*base89 + (42931/31250000000000000000 : ℝ)*base91 + (42931/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1101_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7433719/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5627/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1101_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1101_s7_0 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-87465751/400000000 : ℝ)*x 0 + (1078762431/2000000000 : ℝ)*x 1 + (5265011087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87465751/400000000 : ℝ)^4147 ≤ (13283054617517/100000000000000 : ℝ)^3123 := by
    have hnat : (87465751 : ℕ)^4147*100000000000000^3123 ≤ 13283054617517^3123*400000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87465751 400000000 13283054617517 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078762431/2000000000 : ℝ)^4147 ≤ (22027092824413/50000000000000 : ℝ)^3123 := by
    have hnat : (1078762431 : ℕ)^4147*50000000000000^3123 ≤ 22027092824413^3123*2000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078762431 2000000000 22027092824413 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265011087/10000000000 : ℝ)^4147 ≤ (8532551944599/20000000000000 : ℝ)^3123 := by
    have hnat : (5265011087 : ℕ)^4147*20000000000000^3123 ≤ 8532551944599^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265011087 10000000000 8532551944599 20000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87465751/400000000 : ℝ), (1078762431/2000000000 : ℝ), (5265011087/10000000000 : ℝ)] ![(13283054617517/100000000000000 : ℝ), (22027092824413/50000000000000 : ℝ), (8532551944599/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87465751/400000000 : ℝ)|^4147 ≤ (13283054617517/100000000000000 : ℝ)^3123
        have hw : |(-87465751/400000000 : ℝ)|=(87465751/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078762431/2000000000 : ℝ)|^4147 ≤ (22027092824413/50000000000000 : ℝ)^3123
        have hw : |(1078762431/2000000000 : ℝ)|=(1078762431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265011087/10000000000 : ℝ)|^4147 ≤ (8532551944599/20000000000000 : ℝ)^3123
        have hw : |(5265011087/10000000000 : ℝ)|=(5265011087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s7_1 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344904989/10000000000 : ℝ)*x 0 + (-281498141/1250000000 : ℝ)*x 1 + (5265011087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344904989/10000000000 : ℝ)^4147 ≤ (4352454840503/10000000000000 : ℝ)^3123 := by
    have hnat : (5344904989 : ℕ)^4147*10000000000000^3123 ≤ 4352454840503^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344904989 10000000000 4352454840503 10000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281498141/1250000000 : ℝ)^4147 ≤ (1381269185459/10000000000000 : ℝ)^3123 := by
    have hnat : (281498141 : ℕ)^4147*10000000000000^3123 ≤ 1381269185459^3123*1250000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281498141 1250000000 1381269185459 10000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265011087/10000000000 : ℝ)^4147 ≤ (8532551944599/20000000000000 : ℝ)^3123 := by
    have hnat : (5265011087 : ℕ)^4147*20000000000000^3123 ≤ 8532551944599^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265011087 10000000000 8532551944599 20000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344904989/10000000000 : ℝ), (-281498141/1250000000 : ℝ), (5265011087/10000000000 : ℝ)] ![(4352454840503/10000000000000 : ℝ), (1381269185459/10000000000000 : ℝ), (8532551944599/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344904989/10000000000 : ℝ)|^4147 ≤ (4352454840503/10000000000000 : ℝ)^3123
        have hw : |(5344904989/10000000000 : ℝ)|=(5344904989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-281498141/1250000000 : ℝ)|^4147 ≤ (1381269185459/10000000000000 : ℝ)^3123
        have hw : |(-281498141/1250000000 : ℝ)|=(281498141/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265011087/10000000000 : ℝ)|^4147 ≤ (8532551944599/20000000000000 : ℝ)^3123
        have hw : |(5265011087/10000000000 : ℝ)|=(5265011087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s7_2 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534490499/1000000000 : ℝ)*x 0 + (5265011087/10000000000 : ℝ)*x 1 + (-2251985127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534490499/1000000000 : ℝ)^4147 ≤ (43524548415843/100000000000000 : ℝ)^3123 := by
    have hnat : (534490499 : ℕ)^4147*100000000000000^3123 ≤ 43524548415843^3123*1000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534490499 1000000000 43524548415843 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265011087/10000000000 : ℝ)^4147 ≤ (8532551944599/20000000000000 : ℝ)^3123 := by
    have hnat : (5265011087 : ℕ)^4147*20000000000000^3123 ≤ 8532551944599^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265011087 10000000000 8532551944599 20000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251985127/10000000000 : ℝ)^4147 ≤ (2762538369289/20000000000000 : ℝ)^3123 := by
    have hnat : (2251985127 : ℕ)^4147*20000000000000^3123 ≤ 2762538369289^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251985127 10000000000 2762538369289 20000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534490499/1000000000 : ℝ), (5265011087/10000000000 : ℝ), (-2251985127/10000000000 : ℝ)] ![(43524548415843/100000000000000 : ℝ), (8532551944599/20000000000000 : ℝ), (2762538369289/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534490499/1000000000 : ℝ)|^4147 ≤ (43524548415843/100000000000000 : ℝ)^3123
        have hw : |(534490499/1000000000 : ℝ)|=(534490499/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265011087/10000000000 : ℝ)|^4147 ≤ (8532551944599/20000000000000 : ℝ)^3123
        have hw : |(5265011087/10000000000 : ℝ)|=(5265011087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2251985127/10000000000 : ℝ)|^4147 ≤ (2762538369289/20000000000000 : ℝ)^3123
        have hw : |(-2251985127/10000000000 : ℝ)|=(2251985127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s7_3 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (874095813/2000000000 : ℝ)*x 0 + (2122621053/5000000000 : ℝ)*x 1 + (2249714707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874095813/2000000000 : ℝ)^4147 ≤ (16658357228189/50000000000000 : ℝ)^3123 := by
    have hnat : (874095813 : ℕ)^4147*50000000000000^3123 ≤ 16658357228189^3123*2000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874095813 2000000000 16658357228189 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122621053/5000000000 : ℝ)^4147 ≤ (32054976121557/100000000000000 : ℝ)^3123 := by
    have hnat : (2122621053 : ℕ)^4147*100000000000000^3123 ≤ 32054976121557^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122621053 5000000000 32054976121557 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249714707/5000000000 : ℝ)^4147 ≤ (17314154703/50000000000 : ℝ)^3123 := by
    have hnat : (2249714707 : ℕ)^4147*50000000000^3123 ≤ 17314154703^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249714707 5000000000 17314154703 50000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874095813/2000000000 : ℝ), (2122621053/5000000000 : ℝ), (2249714707/5000000000 : ℝ)] ![(16658357228189/50000000000000 : ℝ), (32054976121557/100000000000000 : ℝ), (17314154703/50000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874095813/2000000000 : ℝ)|^4147 ≤ (16658357228189/50000000000000 : ℝ)^3123
        have hw : |(874095813/2000000000 : ℝ)|=(874095813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2122621053/5000000000 : ℝ)|^4147 ≤ (32054976121557/100000000000000 : ℝ)^3123
        have hw : |(2122621053/5000000000 : ℝ)|=(2122621053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249714707/5000000000 : ℝ)|^4147 ≤ (17314154703/50000000000 : ℝ)^3123
        have hw : |(2249714707/5000000000 : ℝ)|=(2249714707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s7_4 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-437329753/2000000000 : ℝ)*x 0 + (5265334437/10000000000 : ℝ)*x 1 + (5393487639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437329753/2000000000 : ℝ)^4147 ≤ (6641547434537/50000000000000 : ℝ)^3123 := by
    have hnat : (437329753 : ℕ)^4147*50000000000000^3123 ≤ 6641547434537^3123*2000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437329753 2000000000 6641547434537 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265334437/10000000000 : ℝ)^4147 ≤ (42666238999499/100000000000000 : ℝ)^3123 := by
    have hnat : (5265334437 : ℕ)^4147*100000000000000^3123 ≤ 42666238999499^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265334437 10000000000 42666238999499 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393487639/10000000000 : ℝ)^4147 ≤ (22025333057103/50000000000000 : ℝ)^3123 := by
    have hnat : (5393487639 : ℕ)^4147*50000000000000^3123 ≤ 22025333057103^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393487639 10000000000 22025333057103 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-437329753/2000000000 : ℝ), (5265334437/10000000000 : ℝ), (5393487639/10000000000 : ℝ)] ![(6641547434537/50000000000000 : ℝ), (42666238999499/100000000000000 : ℝ), (22025333057103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-437329753/2000000000 : ℝ)|^4147 ≤ (6641547434537/50000000000000 : ℝ)^3123
        have hw : |(-437329753/2000000000 : ℝ)|=(437329753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265334437/10000000000 : ℝ)|^4147 ≤ (42666238999499/100000000000000 : ℝ)^3123
        have hw : |(5265334437/10000000000 : ℝ)|=(5265334437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393487639/10000000000 : ℝ)|^4147 ≤ (22025333057103/50000000000000 : ℝ)^3123
        have hw : |(5393487639/10000000000 : ℝ)|=(5393487639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s7_5 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265618677/500000000 : ℝ)*x 0 + (-2123508579/10000000000 : ℝ)*x 1 + (5393487637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265618677/500000000 : ℝ)^4147 ≤ (21586564565657/50000000000000 : ℝ)^3123 := by
    have hnat : (265618677 : ℕ)^4147*50000000000000^3123 ≤ 21586564565657^3123*500000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265618677 500000000 21586564565657 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123508579/10000000000 : ℝ)^4147 ≤ (2555240953537/20000000000000 : ℝ)^3123 := by
    have hnat : (2123508579 : ℕ)^4147*20000000000000^3123 ≤ 2555240953537^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123508579 10000000000 2555240953537 20000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393487637/10000000000 : ℝ)^4147 ≤ (8810133218503/20000000000000 : ℝ)^3123 := by
    have hnat : (5393487637 : ℕ)^4147*20000000000000^3123 ≤ 8810133218503^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393487637 10000000000 8810133218503 20000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265618677/500000000 : ℝ), (-2123508579/10000000000 : ℝ), (5393487637/10000000000 : ℝ)] ![(21586564565657/50000000000000 : ℝ), (2555240953537/20000000000000 : ℝ), (8810133218503/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265618677/500000000 : ℝ)|^4147 ≤ (21586564565657/50000000000000 : ℝ)^3123
        have hw : |(265618677/500000000 : ℝ)|=(265618677/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2123508579/10000000000 : ℝ)|^4147 ≤ (2555240953537/20000000000000 : ℝ)^3123
        have hw : |(-2123508579/10000000000 : ℝ)|=(2123508579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393487637/10000000000 : ℝ)|^4147 ≤ (8810133218503/20000000000000 : ℝ)^3123
        have hw : |(5393487637/10000000000 : ℝ)|=(5393487637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s7_6 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312373541/10000000000 : ℝ)*x 0 + (5393487637/10000000000 : ℝ)*x 1 + (-1061754289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312373541/10000000000 : ℝ)^4147 ≤ (21586564571053/50000000000000 : ℝ)^3123 := by
    have hnat : (5312373541 : ℕ)^4147*50000000000000^3123 ≤ 21586564571053^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312373541 10000000000 21586564571053 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393487637/10000000000 : ℝ)^4147 ≤ (8810133218503/20000000000000 : ℝ)^3123 := by
    have hnat : (5393487637 : ℕ)^4147*20000000000000^3123 ≤ 8810133218503^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393487637 10000000000 8810133218503 20000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1061754289/5000000000 : ℝ)^4147 ≤ (798512797481/6250000000000 : ℝ)^3123 := by
    have hnat : (1061754289 : ℕ)^4147*6250000000000^3123 ≤ 798512797481^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061754289 5000000000 798512797481 6250000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312373541/10000000000 : ℝ), (5393487637/10000000000 : ℝ), (-1061754289/5000000000 : ℝ)] ![(21586564571053/50000000000000 : ℝ), (8810133218503/20000000000000 : ℝ), (798512797481/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312373541/10000000000 : ℝ)|^4147 ≤ (21586564571053/50000000000000 : ℝ)^3123
        have hw : |(5312373541/10000000000 : ℝ)|=(5312373541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393487637/10000000000 : ℝ)|^4147 ≤ (8810133218503/20000000000000 : ℝ)^3123
        have hw : |(5393487637/10000000000 : ℝ)|=(5393487637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1061754289/5000000000 : ℝ)|^4147 ≤ (798512797481/6250000000000 : ℝ)^3123
        have hw : |(-1061754289/5000000000 : ℝ)|=(1061754289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s7_7 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4370488917/10000000000 : ℝ)*x 0 + (4498791291/10000000000 : ℝ)*x 1 + (530735317/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370488917/10000000000 : ℝ)^4147 ≤ (16658407092491/50000000000000 : ℝ)^3123 := by
    have hnat : (4370488917 : ℕ)^4147*50000000000000^3123 ≤ 16658407092491^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370488917 10000000000 16658407092491 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498791291/10000000000 : ℝ)^4147 ≤ (34621788165797/100000000000000 : ℝ)^3123 := by
    have hnat : (4498791291 : ℕ)^4147*100000000000000^3123 ≤ 34621788165797^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498791291 10000000000 34621788165797 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530735317/1250000000 : ℝ)^4147 ≤ (32061397635857/100000000000000 : ℝ)^3123 := by
    have hnat : (530735317 : ℕ)^4147*100000000000000^3123 ≤ 32061397635857^3123*1250000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530735317 1250000000 32061397635857 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370488917/10000000000 : ℝ), (4498791291/10000000000 : ℝ), (530735317/1250000000 : ℝ)] ![(16658407092491/50000000000000 : ℝ), (34621788165797/100000000000000 : ℝ), (32061397635857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370488917/10000000000 : ℝ)|^4147 ≤ (16658407092491/50000000000000 : ℝ)^3123
        have hw : |(4370488917/10000000000 : ℝ)|=(4370488917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498791291/10000000000 : ℝ)|^4147 ≤ (34621788165797/100000000000000 : ℝ)^3123
        have hw : |(4498791291/10000000000 : ℝ)|=(4498791291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(530735317/1250000000 : ℝ)|^4147 ≤ (32061397635857/100000000000000 : ℝ)^3123
        have hw : |(530735317/1250000000 : ℝ)|=(530735317/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1101_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7433719/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (5649/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7013/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7017/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1129/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7017/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1129/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7017/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1129/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7017/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1129/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7017/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1129/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7017/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1129/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1129/10000 : ℝ) ^ (8293/2048 : ℝ) ≤ (2918018446267453/20000000000000000000 : ℝ) := by
    have hpowers : (1129/10000 : ℝ)^8293 ≤ (2918018446267453/20000000000000000000 : ℝ)^2048 := by
      have hnat : (1129 : ℕ)^8293*20000000000000000000^2048 ≤ 2918018446267453^2048*10000^8293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1129 10000 2918018446267453 20000000000000000000 8293 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1129/10000 : ℝ)) (X := (2918018446267453/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7017/50000 : ℝ) ^ (8293/2048 : ℝ) ≤ (8802538889796719/25000000000000000000 : ℝ) := by
    have hpowers : (7017/50000 : ℝ)^8293 ≤ (8802538889796719/25000000000000000000 : ℝ)^2048 := by
      have hnat : (7017 : ℕ)^8293*25000000000000000000^2048 ≤ 8802538889796719^2048*50000^8293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7017 50000 8802538889796719 25000000000000000000 8293 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7017/50000 : ℝ)) (X := (8802538889796719/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002918018446267453/10000000000000000000 : ℝ) ≤ (10000720540853257/10000000000000000 : ℝ) ^ (8293/2048 : ℝ) := by
    have hpowers : (10002918018446267453/10000000000000000000 : ℝ)^2048 ≤ (10000720540853257/10000000000000000 : ℝ)^8293 := by
      have hnat : (10002918018446267453 : ℕ)^2048*10000000000000000^8293 ≤ 10000720540853257^8293*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002918018446267453 10000000000000000000 10000720540853257 10000000000000000 2048 8293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000720540853257/10000000000000000 : ℝ)) (X := (10002918018446267453/10000000000000000000 : ℝ)) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049800247790524141/100000000000000000000 : ℝ) ≤ (10001229612791727/10000000000000000 : ℝ) ^ (8293/2048 : ℝ) := by
    have hpowers : (100049800247790524141/100000000000000000000 : ℝ)^2048 ≤ (10001229612791727/10000000000000000 : ℝ)^8293 := by
      have hnat : (100049800247790524141 : ℕ)^2048*10000000000000000^8293 ≤ 10001229612791727^8293*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049800247790524141 100000000000000000000 10001229612791727 10000000000000000 2048 8293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001229612791727/10000000000000000 : ℝ)) (X := (100049800247790524141/100000000000000000000 : ℝ)) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508802538889796719/12500000000000000000 : ℝ) ≤ (10001738684730197/10000000000000000 : ℝ) ^ (8293/2048 : ℝ) := by
    have hpowers : (12508802538889796719/12500000000000000000 : ℝ)^2048 ≤ (10001738684730197/10000000000000000 : ℝ)^8293 := by
      have hnat : (12508802538889796719 : ℕ)^2048*10000000000000000^8293 ≤ 10001738684730197^8293*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508802538889796719 12500000000000000000 10001738684730197 10000000000000000 2048 8293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001738684730197/10000000000000000 : ℝ)) (X := (12508802538889796719/12500000000000000000 : ℝ)) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2918018446267453/20000000000000000000 : ℝ) ≤ ((428601286245791947/428750000000000000 : ℝ)+2*(50907193847/27440000000000 : ℝ)*(1129/10000 : ℝ))^(8293/2048 : ℝ) := by
    rw [show (428601286245791947/428750000000000000 : ℝ)+2*(50907193847/27440000000000 : ℝ)*(1129/10000 : ℝ)=(10000720540853257/10000000000000000 : ℝ) by norm_num, show 1+2*(2918018446267453/20000000000000000000 : ℝ)=(10002918018446267453/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8802538889796719/25000000000000000000 : ℝ)+(2918018446267453/20000000000000000000 : ℝ) ≤ ((428601286245791947/428750000000000000 : ℝ)+(50907193847/27440000000000 : ℝ)*((7017/50000 : ℝ)+(1129/10000 : ℝ)))^(8293/2048 : ℝ) := by
    rw [show (428601286245791947/428750000000000000 : ℝ)+(50907193847/27440000000000 : ℝ)*((7017/50000 : ℝ)+(1129/10000 : ℝ))=(10001229612791727/10000000000000000 : ℝ) by norm_num, show 1+(8802538889796719/25000000000000000000 : ℝ)+(2918018446267453/20000000000000000000 : ℝ)=(100049800247790524141/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8802538889796719/25000000000000000000 : ℝ) ≤ ((428601286245791947/428750000000000000 : ℝ)+2*(50907193847/27440000000000 : ℝ)*(7017/50000 : ℝ))^(8293/2048 : ℝ) := by
    rw [show (428601286245791947/428750000000000000 : ℝ)+2*(50907193847/27440000000000 : ℝ)*(7017/50000 : ℝ)=(10001738684730197/10000000000000000 : ℝ) by norm_num, show 1+2*(8802538889796719/25000000000000000000 : ℝ)=(12508802538889796719/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (428601286245791947/428750000000000000 : ℝ)*(X 1 0+X 2 0)+(50907193847/27440000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8293/2048 : ℝ)) (lo := (1129/10000 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (428601286245791947/428750000000000000 : ℝ)) (alpha := (50907193847/27440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (428601286245791947/428750000000000000 : ℝ)*(X 0 1+X 2 1)+(50907193847/27440000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8293/2048 : ℝ)) (lo := (1129/10000 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (428601286245791947/428750000000000000 : ℝ)) (alpha := (50907193847/27440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (428601286245791947/428750000000000000 : ℝ)*(X 0 2+X 1 2)+(50907193847/27440000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8293/2048 : ℝ)) (lo := (1129/10000 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (428601286245791947/428750000000000000 : ℝ)) (alpha := (50907193847/27440000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-87465751/400000000 : ℝ)*X 0 0+(1078762431/2000000000 : ℝ)*X 0 1+(5265011087/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344904989/10000000000 : ℝ)*X 1 0+(-281498141/1250000000 : ℝ)*X 1 1+(5265011087/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534490499/1000000000 : ℝ)*X 2 0+(5265011087/10000000000 : ℝ)*X 2 1+(-2251985127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((874095813/2000000000 : ℝ)*X 0 0+(2122621053/5000000000 : ℝ)*X 0 1+(2249714707/5000000000 : ℝ)*X 0 2+(874095813/2000000000 : ℝ)*X 1 0+(2122621053/5000000000 : ℝ)*X 1 1+(2249714707/5000000000 : ℝ)*X 1 2+(874095813/2000000000 : ℝ)*X 2 0+(2122621053/5000000000 : ℝ)*X 2 1+(2249714707/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-437329753/2000000000 : ℝ)*X 0 0+(5265334437/10000000000 : ℝ)*X 0 1+(5393487639/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265618677/500000000 : ℝ)*X 1 0+(-2123508579/10000000000 : ℝ)*X 1 1+(5393487637/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312373541/10000000000 : ℝ)*X 2 0+(5393487637/10000000000 : ℝ)*X 2 1+(-1061754289/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4370488917/10000000000 : ℝ)*X 0 0+(4498791291/10000000000 : ℝ)*X 0 1+(530735317/1250000000 : ℝ)*X 0 2+(4370488917/10000000000 : ℝ)*X 1 0+(4498791291/10000000000 : ℝ)*X 1 1+(530735317/1250000000 : ℝ)*X 1 2+(4370488917/10000000000 : ℝ)*X 2 0+(4498791291/10000000000 : ℝ)*X 2 1+(530735317/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (92317880896952871479019249/21437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (431529059/50000000000000 : ℝ)*(base19) + (806289123/100000000000000 : ℝ)*(base23) + (7779721/25000000000000 : ℝ)*(lower2) + (108367041/100000000000000 : ℝ)*(upper3) + (1680437/2500000000000 : ℝ)*(upper5) + (5849044806614913/100000000000000 : ℝ)*(major0) + (5849044806614913/100000000000000 : ℝ)*(major1) + (5849044806614913/100000000000000 : ℝ)*(major2) + (970491892619193/12500000000000 : ℝ)*(sp0) + (1940989412758407/25000000000000 : ℝ)*(sp1) + (3790994974513/48828125000 : ℝ)*(sp2) + (1967059119693039/50000000000000 : ℝ)*(sp3) + (23373138203/100000000000000 : ℝ)*(sp4) + (3179051553/25000000000000 : ℝ)*(sp7) + (393413095559229/10000000000000 : ℝ)*(f.failure) + (3881979257045873/50000000000000 : ℝ)*(f.sum) + (2150857526077/1372000000000000000000000000 : ℝ)*base66 + (297945454477143/437500000000000000000000000000 : ℝ)*base68 + (1920240507352143/437500000000000000000000000000 : ℝ)*base70 + (663763518539643/437500000000000000000000000000 : ℝ)*base72 + (4613563470039/1372000000000000000000000000 : ℝ)*base73 + (1482179890914643/437500000000000000000000000000 : ℝ)*base76 + (4010080123289643/437500000000000000000000000000 : ℝ)*base78 + (3287806566914643/437500000000000000000000000000 : ℝ)*base80 + (6913552576839/1372000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (257349/50000000000000000000 : ℝ)*base90 + (257349/50000000000000000000 : ℝ)*base92 + (257349/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (135557125053516666840229971/21437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1158410609/100000000000000 : ℝ)*(base19) + (1264818017/100000000000000 : ℝ)*(base23) + (125864563/100000000000000 : ℝ)*(upper3) + (11879303/25000000000000 : ℝ)*(lower4) + (16027083/12500000000000 : ℝ)*(upper5) + (5878577154576153/100000000000000 : ℝ)*(major0) + (5878577154576153/100000000000000 : ℝ)*(major1) + (5878577154576153/100000000000000 : ℝ)*(major2) + (31616515427/100000000000000 : ℝ)*(sp1) + (6829278883/20000000000000 : ℝ)*(sp2) + (1560631873067197/20000000000000 : ℝ)*(sp4) + (1950781647602487/25000000000000 : ℝ)*(sp5) + (243847623566361/3125000000000 : ℝ)*(sp6) + (494249341629687/12500000000000 : ℝ)*(sp7) + (494249341629687/12500000000000 : ℝ)*(f.failure) + (1560631873067197/20000000000000 : ℝ)*(f.sum) + (131590646613/1372000000000000000000000000 : ℝ)*base66 + (354962866436217/437500000000000000000000000000 : ℝ)*base67 + (2972879347938783/437500000000000000000000000000 : ℝ)*base70 + (50297878438783/437500000000000000000000000000 : ℝ)*base72 + (553595954691/274400000000000000000000000 : ℝ)*base73 + (8477487989813783/437500000000000000000000000000 : ℝ)*base76 + (3837134804251283/437500000000000000000000000000 : ℝ)*base78 + (5348545382813783/437500000000000000000000000000 : ℝ)*base80 + (3302865900251/1372000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (409047/62500000000000000000 : ℝ)*base90 + (409047/62500000000000000000 : ℝ)*base92 + (409047/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1101_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7433719/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7013/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1101_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1101_s8_0 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1093324981/5000000000 : ℝ)*x 0 + (5393730073/10000000000 : ℝ)*x 1 + (164534037/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093324981/5000000000 : ℝ)^4147 ≤ (3320776131153/25000000000000 : ℝ)^3123 := by
    have hnat : (1093324981 : ℕ)^4147*25000000000000^3123 ≤ 3320776131153^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093324981 5000000000 3320776131153 25000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393730073/10000000000 : ℝ)^4147 ≤ (2202664771143/5000000000000 : ℝ)^3123 := by
    have hnat : (5393730073 : ℕ)^4147*5000000000000^3123 ≤ 2202664771143^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393730073 10000000000 2202664771143 5000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164534037/312500000 : ℝ)^4147 ≤ (8532720009533/20000000000000 : ℝ)^3123 := by
    have hnat : (164534037 : ℕ)^4147*20000000000000^3123 ≤ 8532720009533^3123*312500000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164534037 312500000 8532720009533 20000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1093324981/5000000000 : ℝ), (5393730073/10000000000 : ℝ), (164534037/312500000 : ℝ)] ![(3320776131153/25000000000000 : ℝ), (2202664771143/5000000000000 : ℝ), (8532720009533/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1093324981/5000000000 : ℝ)|^4147 ≤ (3320776131153/25000000000000 : ℝ)^3123
        have hw : |(-1093324981/5000000000 : ℝ)|=(1093324981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393730073/10000000000 : ℝ)|^4147 ≤ (2202664771143/5000000000000 : ℝ)^3123
        have hw : |(5393730073/10000000000 : ℝ)|=(5393730073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164534037/312500000 : ℝ)|^4147 ≤ (8532720009533/20000000000000 : ℝ)^3123
        have hw : |(164534037/312500000 : ℝ)|=(164534037/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s8_1 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068976933/2000000000 : ℝ)*x 0 + (-1125954011/5000000000 : ℝ)*x 1 + (1316272469/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068976933/2000000000 : ℝ)^4147 ≤ (43524328636627/100000000000000 : ℝ)^3123 := by
    have hnat : (1068976933 : ℕ)^4147*100000000000000^3123 ≤ 43524328636627^3123*2000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068976933 2000000000 43524328636627 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1125954011/5000000000 : ℝ)^4147 ≤ (6906031926609/50000000000000 : ℝ)^3123 := by
    have hnat : (1125954011 : ℕ)^4147*50000000000000^3123 ≤ 6906031926609^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125954011 5000000000 6906031926609 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316272469/2500000000 : ℝ)^4147 ≤ (10665901873403/25000000000000 : ℝ)^3123 := by
    have hnat : (1316272469 : ℕ)^4147*25000000000000^3123 ≤ 10665901873403^3123*2500000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316272469 2500000000 10665901873403 25000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068976933/2000000000 : ℝ), (-1125954011/5000000000 : ℝ), (1316272469/2500000000 : ℝ)] ![(43524328636627/100000000000000 : ℝ), (6906031926609/50000000000000 : ℝ), (10665901873403/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068976933/2000000000 : ℝ)|^4147 ≤ (43524328636627/100000000000000 : ℝ)^3123
        have hw : |(1068976933/2000000000 : ℝ)|=(1068976933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1125954011/5000000000 : ℝ)|^4147 ≤ (6906031926609/50000000000000 : ℝ)^3123
        have hw : |(-1125954011/5000000000 : ℝ)|=(1125954011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316272469/2500000000 : ℝ)|^4147 ≤ (10665901873403/25000000000000 : ℝ)^3123
        have hw : |(1316272469/2500000000 : ℝ)|=(1316272469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s8_2 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344883009/10000000000 : ℝ)*x 0 + (2632546313/5000000000 : ℝ)*x 1 + (-562976647/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344883009/10000000000 : ℝ)^4147 ≤ (8704862145981/20000000000000 : ℝ)^3123 := by
    have hnat : (5344883009 : ℕ)^4147*20000000000000^3123 ≤ 8704862145981^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344883009 10000000000 8704862145981 20000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632546313/5000000000 : ℝ)^4147 ≤ (42663637083721/100000000000000 : ℝ)^3123 := by
    have hnat : (2632546313 : ℕ)^4147*100000000000000^3123 ≤ 42663637083721^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632546313 5000000000 42663637083721 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562976647/2500000000 : ℝ)^4147 ≤ (13812052173857/100000000000000 : ℝ)^3123 := by
    have hnat : (562976647 : ℕ)^4147*100000000000000^3123 ≤ 13812052173857^3123*2500000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562976647 2500000000 13812052173857 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344883009/10000000000 : ℝ), (2632546313/5000000000 : ℝ), (-562976647/2500000000 : ℝ)] ![(8704862145981/20000000000000 : ℝ), (42663637083721/100000000000000 : ℝ), (13812052173857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344883009/10000000000 : ℝ)|^4147 ≤ (8704862145981/20000000000000 : ℝ)^3123
        have hw : |(5344883009/10000000000 : ℝ)|=(5344883009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632546313/5000000000 : ℝ)|^4147 ≤ (42663637083721/100000000000000 : ℝ)^3123
        have hw : |(2632546313/5000000000 : ℝ)|=(2632546313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-562976647/2500000000 : ℝ)|^4147 ≤ (13812052173857/100000000000000 : ℝ)^3123
        have hw : |(-562976647/2500000000 : ℝ)|=(562976647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s8_3 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2185241867/5000000000 : ℝ)*x 0 + (2122699737/5000000000 : ℝ)*x 1 + (562408799/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185241867/5000000000 : ℝ)^4147 ≤ (33316761719143/100000000000000 : ℝ)^3123 := by
    have hnat : (2185241867 : ℕ)^4147*100000000000000^3123 ≤ 33316761719143^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185241867 5000000000 33316761719143 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122699737/5000000000 : ℝ)^4147 ≤ (16028277001031/50000000000000 : ℝ)^3123 := by
    have hnat : (2122699737 : ℕ)^4147*50000000000000^3123 ≤ 16028277001031^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122699737 5000000000 16028277001031 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562408799/1250000000 : ℝ)^4147 ≤ (34626684266703/100000000000000 : ℝ)^3123 := by
    have hnat : (562408799 : ℕ)^4147*100000000000000^3123 ≤ 34626684266703^3123*1250000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562408799 1250000000 34626684266703 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185241867/5000000000 : ℝ), (2122699737/5000000000 : ℝ), (562408799/1250000000 : ℝ)] ![(33316761719143/100000000000000 : ℝ), (16028277001031/50000000000000 : ℝ), (34626684266703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185241867/5000000000 : ℝ)|^4147 ≤ (33316761719143/100000000000000 : ℝ)^3123
        have hw : |(2185241867/5000000000 : ℝ)|=(2185241867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2122699737/5000000000 : ℝ)|^4147 ≤ (16028277001031/50000000000000 : ℝ)^3123
        have hw : |(2122699737/5000000000 : ℝ)|=(2122699737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562408799/1250000000 : ℝ)|^4147 ≤ (34626684266703/100000000000000 : ℝ)^3123
        have hw : |(562408799/1250000000 : ℝ)|=(562408799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s8_4 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2186654727/10000000000 : ℝ)*x 0 + (5265412399/10000000000 : ℝ)*x 1 + (2696702927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186654727/10000000000 : ℝ)^4147 ≤ (6641571480627/50000000000000 : ℝ)^3123 := by
    have hnat : (2186654727 : ℕ)^4147*50000000000000^3123 ≤ 6641571480627^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186654727 10000000000 6641571480627 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265412399/10000000000 : ℝ)^4147 ≤ (5333384736057/12500000000000 : ℝ)^3123 := by
    have hnat : (5265412399 : ℕ)^4147*12500000000000^3123 ≤ 5333384736057^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265412399 10000000000 5333384736057 12500000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696702927/5000000000 : ℝ)^4147 ≤ (8809955825373/20000000000000 : ℝ)^3123 := by
    have hnat : (2696702927 : ℕ)^4147*20000000000000^3123 ≤ 8809955825373^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696702927 5000000000 8809955825373 20000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2186654727/10000000000 : ℝ), (5265412399/10000000000 : ℝ), (2696702927/5000000000 : ℝ)] ![(6641571480627/50000000000000 : ℝ), (5333384736057/12500000000000 : ℝ), (8809955825373/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2186654727/10000000000 : ℝ)|^4147 ≤ (6641571480627/50000000000000 : ℝ)^3123
        have hw : |(-2186654727/10000000000 : ℝ)|=(2186654727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265412399/10000000000 : ℝ)|^4147 ≤ (5333384736057/12500000000000 : ℝ)^3123
        have hw : |(5265412399/10000000000 : ℝ)|=(5265412399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696702927/5000000000 : ℝ)|^4147 ≤ (8809955825373/20000000000000 : ℝ)^3123
        have hw : |(2696702927/5000000000 : ℝ)|=(2696702927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s8_5 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656197161/5000000000 : ℝ)*x 0 + (-2123591323/10000000000 : ℝ)*x 1 + (5393406003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656197161/5000000000 : ℝ)^4147 ≤ (1726934136123/4000000000000 : ℝ)^3123 := by
    have hnat : (2656197161 : ℕ)^4147*4000000000000^3123 ≤ 1726934136123^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656197161 5000000000 1726934136123 4000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123591323/10000000000 : ℝ)^4147 ≤ (12776865840321/100000000000000 : ℝ)^3123 := by
    have hnat : (2123591323 : ℕ)^4147*100000000000000^3123 ≤ 12776865840321^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123591323 10000000000 12776865840321 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393406003/10000000000 : ℝ)^4147 ≤ (44049780742819/100000000000000 : ℝ)^3123 := by
    have hnat : (5393406003 : ℕ)^4147*100000000000000^3123 ≤ 44049780742819^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393406003 10000000000 44049780742819 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656197161/5000000000 : ℝ), (-2123591323/10000000000 : ℝ), (5393406003/10000000000 : ℝ)] ![(1726934136123/4000000000000 : ℝ), (12776865840321/100000000000000 : ℝ), (44049780742819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656197161/5000000000 : ℝ)|^4147 ≤ (1726934136123/4000000000000 : ℝ)^3123
        have hw : |(2656197161/5000000000 : ℝ)|=(2656197161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2123591323/10000000000 : ℝ)|^4147 ≤ (12776865840321/100000000000000 : ℝ)^3123
        have hw : |(-2123591323/10000000000 : ℝ)|=(2123591323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393406003/10000000000 : ℝ)|^4147 ≤ (44049780742819/100000000000000 : ℝ)^3123
        have hw : |(5393406003/10000000000 : ℝ)|=(5393406003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s8_6 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312393191/10000000000 : ℝ)*x 0 + (5393405929/10000000000 : ℝ)*x 1 + (-42471859/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312393191/10000000000 : ℝ)^4147 ≤ (1349166912429/3125000000000 : ℝ)^3123 := by
    have hnat : (5312393191 : ℕ)^4147*3125000000000^3123 ≤ 1349166912429^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312393191 10000000000 1349166912429 3125000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393405929/10000000000 : ℝ)^4147 ≤ (8809955988053/20000000000000 : ℝ)^3123 := by
    have hnat : (5393405929 : ℕ)^4147*20000000000000^3123 ≤ 8809955988053^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393405929 10000000000 8809955988053 20000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42471859/200000000 : ℝ)^4147 ≤ (2555375767823/20000000000000 : ℝ)^3123 := by
    have hnat : (42471859 : ℕ)^4147*20000000000000^3123 ≤ 2555375767823^3123*200000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42471859 200000000 2555375767823 20000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312393191/10000000000 : ℝ), (5393405929/10000000000 : ℝ), (-42471859/200000000 : ℝ)] ![(1349166912429/3125000000000 : ℝ), (8809955988053/20000000000000 : ℝ), (2555375767823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312393191/10000000000 : ℝ)|^4147 ≤ (1349166912429/3125000000000 : ℝ)^3123
        have hw : |(5312393191/10000000000 : ℝ)|=(5312393191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393405929/10000000000 : ℝ)|^4147 ≤ (8809955988053/20000000000000 : ℝ)^3123
        have hw : |(5393405929/10000000000 : ℝ)|=(5393405929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-42471859/200000000 : ℝ)|^4147 ≤ (2555375767823/20000000000000 : ℝ)^3123
        have hw : |(-42471859/200000000 : ℝ)|=(42471859/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s8_7 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (136577877/312500000 : ℝ)*x 0 + (4498632979/10000000000 : ℝ)*x 1 + (42460407/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136577877/312500000 : ℝ)^4147 ≤ (33316846041059/100000000000000 : ℝ)^3123 := by
    have hnat : (136577877 : ℕ)^4147*100000000000000^3123 ≤ 33316846041059^3123*312500000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136577877 312500000 33316846041059 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498632979/10000000000 : ℝ)^4147 ≤ (6924034071521/20000000000000 : ℝ)^3123 := by
    have hnat : (4498632979 : ℕ)^4147*20000000000000^3123 ≤ 6924034071521^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498632979 10000000000 6924034071521 20000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42460407/100000000 : ℝ)^4147 ≤ (32062983576097/100000000000000 : ℝ)^3123 := by
    have hnat : (42460407 : ℕ)^4147*100000000000000^3123 ≤ 32062983576097^3123*100000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42460407 100000000 32062983576097 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136577877/312500000 : ℝ), (4498632979/10000000000 : ℝ), (42460407/100000000 : ℝ)] ![(33316846041059/100000000000000 : ℝ), (6924034071521/20000000000000 : ℝ), (32062983576097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136577877/312500000 : ℝ)|^4147 ≤ (33316846041059/100000000000000 : ℝ)^3123
        have hw : |(136577877/312500000 : ℝ)|=(136577877/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498632979/10000000000 : ℝ)|^4147 ≤ (6924034071521/20000000000000 : ℝ)^3123
        have hw : |(4498632979/10000000000 : ℝ)|=(4498632979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42460407/100000000 : ℝ)|^4147 ≤ (32062983576097/100000000000000 : ℝ)^3123
        have hw : |(42460407/100000000 : ℝ)|=(42460407/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1101_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7433719/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7013/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11299/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1753/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7013/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5649/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7013/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5649/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7013/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5649/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7013/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5649/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7013/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5649/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7013/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5649/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
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
  have hpowlo : (5649/50000 : ℝ) ^ (8293/2048 : ℝ) ≤ (585280040241879/4000000000000000000 : ℝ) := by
    have hpowers : (5649/50000 : ℝ)^8293 ≤ (585280040241879/4000000000000000000 : ℝ)^2048 := by
      have hnat : (5649 : ℕ)^8293*4000000000000000000^2048 ≤ 585280040241879^2048*50000^8293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5649 50000 585280040241879 4000000000000000000 8293 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5649/50000 : ℝ)) (X := (585280040241879/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7013/50000 : ℝ) ^ (8293/2048 : ℝ) ≤ (17564475473228181/50000000000000000000 : ℝ) := by
    have hpowers : (7013/50000 : ℝ)^8293 ≤ (17564475473228181/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7013 : ℕ)^8293*50000000000000000000^2048 ≤ 17564475473228181^2048*50000^8293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7013 50000 17564475473228181 50000000000000000000 8293 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7013/50000 : ℝ)) (X := (17564475473228181/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000585280040241879/2000000000000000000 : ℝ) ≤ (10000722610316377/10000000000000000 : ℝ) ^ (8293/2048 : ℝ) := by
    have hpowers : (2000585280040241879/2000000000000000000 : ℝ)^2048 ≤ (10000722610316377/10000000000000000 : ℝ)^8293 := by
      have hnat : (2000585280040241879 : ℕ)^2048*10000000000000000^8293 ≤ 10000722610316377^8293*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000585280040241879 2000000000000000000 10000722610316377 10000000000000000 2048 8293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000722610316377/10000000000000000 : ℝ)) (X := (2000585280040241879/2000000000000000000 : ℝ)) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049760951952503337/100000000000000000000 : ℝ) ≤ (10001228642723951/10000000000000000 : ℝ) ^ (8293/2048 : ℝ) := by
    have hpowers : (100049760951952503337/100000000000000000000 : ℝ)^2048 ≤ (10001228642723951/10000000000000000 : ℝ)^8293 := by
      have hnat : (100049760951952503337 : ℕ)^2048*10000000000000000^8293 ≤ 10001228642723951^8293*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049760951952503337 100000000000000000000 10001228642723951 10000000000000000 2048 8293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001228642723951/10000000000000000 : ℝ)) (X := (100049760951952503337/100000000000000000000 : ℝ)) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017564475473228181/25000000000000000000 : ℝ) ≤ (400069387005261/400000000000000 : ℝ) ^ (8293/2048 : ℝ) := by
    have hpowers : (25017564475473228181/25000000000000000000 : ℝ)^2048 ≤ (400069387005261/400000000000000 : ℝ)^8293 := by
      have hnat : (25017564475473228181 : ℕ)^2048*400000000000000^8293 ≤ 400069387005261^8293*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017564475473228181 25000000000000000000 400069387005261 400000000000000 2048 8293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400069387005261/400000000000000 : ℝ)) (X := (25017564475473228181/25000000000000000000 : ℝ)) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(585280040241879/4000000000000000000 : ℝ) ≤ ((1704408560791345897/1705000000000000000 : ℝ)+2*(253016203787/136400000000000 : ℝ)*(5649/50000 : ℝ))^(8293/2048 : ℝ) := by
    rw [show (1704408560791345897/1705000000000000000 : ℝ)+2*(253016203787/136400000000000 : ℝ)*(5649/50000 : ℝ)=(10000722610316377/10000000000000000 : ℝ) by norm_num, show 1+2*(585280040241879/4000000000000000000 : ℝ)=(2000585280040241879/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17564475473228181/50000000000000000000 : ℝ)+(585280040241879/4000000000000000000 : ℝ) ≤ ((1704408560791345897/1705000000000000000 : ℝ)+(253016203787/136400000000000 : ℝ)*((7013/50000 : ℝ)+(5649/50000 : ℝ)))^(8293/2048 : ℝ) := by
    rw [show (1704408560791345897/1705000000000000000 : ℝ)+(253016203787/136400000000000 : ℝ)*((7013/50000 : ℝ)+(5649/50000 : ℝ))=(10001228642723951/10000000000000000 : ℝ) by norm_num, show 1+(17564475473228181/50000000000000000000 : ℝ)+(585280040241879/4000000000000000000 : ℝ)=(100049760951952503337/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17564475473228181/50000000000000000000 : ℝ) ≤ ((1704408560791345897/1705000000000000000 : ℝ)+2*(253016203787/136400000000000 : ℝ)*(7013/50000 : ℝ))^(8293/2048 : ℝ) := by
    rw [show (1704408560791345897/1705000000000000000 : ℝ)+2*(253016203787/136400000000000 : ℝ)*(7013/50000 : ℝ)=(400069387005261/400000000000000 : ℝ) by norm_num, show 1+2*(17564475473228181/50000000000000000000 : ℝ)=(25017564475473228181/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1704408560791345897/1705000000000000000 : ℝ)*(X 1 0+X 2 0)+(253016203787/136400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8293/2048 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (7013/50000 : ℝ)) (c := (1704408560791345897/1705000000000000000 : ℝ)) (alpha := (253016203787/136400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1704408560791345897/1705000000000000000 : ℝ)*(X 0 1+X 2 1)+(253016203787/136400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8293/2048 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (7013/50000 : ℝ)) (c := (1704408560791345897/1705000000000000000 : ℝ)) (alpha := (253016203787/136400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1704408560791345897/1705000000000000000 : ℝ)*(X 0 2+X 1 2)+(253016203787/136400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8293/2048 : ℝ)) (lo := (5649/50000 : ℝ)) (hi := (7013/50000 : ℝ)) (c := (1704408560791345897/1705000000000000000 : ℝ)) (alpha := (253016203787/136400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1093324981/5000000000 : ℝ)*X 0 0+(5393730073/10000000000 : ℝ)*X 0 1+(164534037/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068976933/2000000000 : ℝ)*X 1 0+(-1125954011/5000000000 : ℝ)*X 1 1+(1316272469/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344883009/10000000000 : ℝ)*X 2 0+(2632546313/5000000000 : ℝ)*X 2 1+(-562976647/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2185241867/5000000000 : ℝ)*X 0 0+(2122699737/5000000000 : ℝ)*X 0 1+(562408799/1250000000 : ℝ)*X 0 2+(2185241867/5000000000 : ℝ)*X 1 0+(2122699737/5000000000 : ℝ)*X 1 1+(562408799/1250000000 : ℝ)*X 1 2+(2185241867/5000000000 : ℝ)*X 2 0+(2122699737/5000000000 : ℝ)*X 2 1+(562408799/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2186654727/10000000000 : ℝ)*X 0 0+(5265412399/10000000000 : ℝ)*X 0 1+(2696702927/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656197161/5000000000 : ℝ)*X 1 0+(-2123591323/10000000000 : ℝ)*X 1 1+(5393406003/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312393191/10000000000 : ℝ)*X 2 0+(5393405929/10000000000 : ℝ)*X 2 1+(-42471859/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((136577877/312500000 : ℝ)*X 0 0+(4498632979/10000000000 : ℝ)*X 0 1+(42460407/100000000 : ℝ)*X 0 2+(136577877/312500000 : ℝ)*X 1 0+(4498632979/10000000000 : ℝ)*X 1 1+(42460407/100000000 : ℝ)*X 1 2+(136577877/312500000 : ℝ)*X 2 0+(4498632979/10000000000 : ℝ)*X 2 1+(42460407/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (540025549100443307014791681/42625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (265830929/10000000000000 : ℝ)*(base19) + (42981113/50000000000000 : ℝ)*(base23) + (177808921/100000000000000 : ℝ)*(lower2) + (177349753/20000000000000 : ℝ)*(upper5) + (2928262639791703/50000000000000 : ℝ)*(major0) + (2928262639791703/50000000000000 : ℝ)*(major1) + (2928262639791703/50000000000000 : ℝ)*(major2) + (7773719933024469/100000000000000 : ℝ)*(sp0) + (1943464322647489/25000000000000 : ℝ)*(sp1) + (485867978004923/6250000000000 : ℝ)*(sp2) + (1969549908281339/50000000000000 : ℝ)*(sp3) + (6712040661/4000000000000 : ℝ)*(sp4) + (6946285437/25000000000000 : ℝ)*(sp5) + (62586255753/100000000000000 : ℝ)*(sp7) + (30774706272019/781250000000 : ℝ)*(f.failure) + (3886943867020497/50000000000000 : ℝ)*(f.sum) + (38255233409951/3410000000000000000000000000 : ℝ)*base65 + (2094968602491705091/85250000000000000000000000000000 : ℝ)*base67 + (1532114151593955091/85250000000000000000000000000000 : ℝ)*base69 + (2640505162084455091/85250000000000000000000000000000 : ℝ)*base71 + (16548571741831/3410000000000000000000000000 : ℝ)*base73 + (1869105862490455091/85250000000000000000000000000000 : ℝ)*base75 + (2136756661895455091/85250000000000000000000000000000 : ℝ)*base77 + (847342093967705091/85250000000000000000000000000000 : ℝ)*base79 + (9230632053541/3410000000000000000000000000 : ℝ)*base81 + (5893/1953125000000000000 : ℝ)*base89 + (5893/1953125000000000000 : ℝ)*base91 + (5893/1953125000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (531194428243318987689552873/85250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2003447/12500000000000 : ℝ)*(base8) + (93882279/50000000000000 : ℝ)*(upper1) + (340749461/50000000000000 : ℝ)*(upper2) + (75054041/20000000000000 : ℝ)*(lower4) + (112133353/100000000000000 : ℝ)*(lower5) + (5885926249617197/100000000000000 : ℝ)*(major0) + (5885926249617197/100000000000000 : ℝ)*(major1) + (5885926249617197/100000000000000 : ℝ)*(major2) + (14453531921/50000000000000 : ℝ)*(sp0) + (53286140869/100000000000000 : ℝ)*(sp1) + (3906442777198577/50000000000000 : ℝ)*(sp4) + (7812861191347703/100000000000000 : ℝ)*(sp5) + (1953228619372143/25000000000000 : ℝ)*(sp6) + (1979468907022581/50000000000000 : ℝ)*(sp7) + (1979468907022581/50000000000000 : ℝ)*(f.failure) + (1953228619372143/25000000000000 : ℝ)*(f.sum) + (22982867096119/6820000000000000000000000000 : ℝ)*base65 + (689014631274578209/170500000000000000000000000000000 : ℝ)*base67 + (123792240827578209/170500000000000000000000000000000 : ℝ)*base69 + (286467522690078209/170500000000000000000000000000000 : ℝ)*base71 + (10090393622019/6820000000000000000000000000 : ℝ)*base73 + (1916407163156921791/170500000000000000000000000000000 : ℝ)*base76 + (51173115980421791/170500000000000000000000000000000 : ℝ)*base78 + (537898695116578209/170500000000000000000000000000000 : ℝ)*base79 + (45879031594961/6820000000000000000000000000 : ℝ)*base82 + (1308739/250000000000000000000 : ℝ)*base89 + (1308739/250000000000000000000 : ℝ)*base91 + (1308739/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1101_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7433719/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7013/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1101_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1101_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7433719/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5627/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1101_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1101_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1101_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7433719/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1759/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5627/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1101_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

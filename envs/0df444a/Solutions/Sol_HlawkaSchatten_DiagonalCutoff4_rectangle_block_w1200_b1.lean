-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1200_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:03:03.210995+00:00
-- url     : https://prove2.me/submissions/498b9be3-4730-465e-8132-2e6764c3507e

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
theorem support_rectangle_w1200_s3_0 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2136239177/10000000000 : ℝ)*x 0 + (5423468009/10000000000 : ℝ)*x 1 + (1309310861/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136239177/10000000000 : ℝ)^8393 ≤ (12980110604801/100000000000000 : ℝ)^6345 := by
    have hnat : (2136239177 : ℕ)^8393*100000000000000^6345 ≤ 12980110604801^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136239177 10000000000 12980110604801 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423468009/10000000000 : ℝ)^8393 ≤ (11128808919337/25000000000000 : ℝ)^6345 := by
    have hnat : (5423468009 : ℕ)^8393*25000000000000^6345 ≤ 11128808919337^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423468009 10000000000 11128808919337 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309310861/2500000000 : ℝ)^8393 ≤ (21252326851469/50000000000000 : ℝ)^6345 := by
    have hnat : (1309310861 : ℕ)^8393*50000000000000^6345 ≤ 21252326851469^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309310861 2500000000 21252326851469 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2136239177/10000000000 : ℝ), (5423468009/10000000000 : ℝ), (1309310861/2500000000 : ℝ)] ![(12980110604801/100000000000000 : ℝ), (11128808919337/25000000000000 : ℝ), (21252326851469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2136239177/10000000000 : ℝ)|^8393 ≤ (12980110604801/100000000000000 : ℝ)^6345
        have hw : |(-2136239177/10000000000 : ℝ)|=(2136239177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423468009/10000000000 : ℝ)|^8393 ≤ (11128808919337/25000000000000 : ℝ)^6345
        have hw : |(5423468009/10000000000 : ℝ)|=(5423468009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1309310861/2500000000 : ℝ)|^8393 ≤ (21252326851469/50000000000000 : ℝ)^6345
        have hw : |(1309310861/2500000000 : ℝ)|=(1309310861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s3_1 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2676216737/5000000000 : ℝ)*x 0 + (-17432153/78125000 : ℝ)*x 1 + (5237243513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676216737/5000000000 : ℝ)^8393 ≤ (43745635744693/100000000000000 : ℝ)^6345 := by
    have hnat : (2676216737 : ℕ)^8393*100000000000000^6345 ≤ 43745635744693^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676216737 5000000000 43745635744693 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17432153/78125000 : ℝ)^8393 ≤ (13749709803107/100000000000000 : ℝ)^6345 := by
    have hnat : (17432153 : ℕ)^8393*100000000000000^6345 ≤ 13749709803107^6345*78125000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17432153 78125000 13749709803107 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237243513/10000000000 : ℝ)^8393 ≤ (42504654443683/100000000000000 : ℝ)^6345 := by
    have hnat : (5237243513 : ℕ)^8393*100000000000000^6345 ≤ 42504654443683^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237243513 10000000000 42504654443683 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676216737/5000000000 : ℝ), (-17432153/78125000 : ℝ), (5237243513/10000000000 : ℝ)] ![(43745635744693/100000000000000 : ℝ), (13749709803107/100000000000000 : ℝ), (42504654443683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676216737/5000000000 : ℝ)|^8393 ≤ (43745635744693/100000000000000 : ℝ)^6345
        have hw : |(2676216737/5000000000 : ℝ)|=(2676216737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17432153/78125000 : ℝ)|^8393 ≤ (13749709803107/100000000000000 : ℝ)^6345
        have hw : |(-17432153/78125000 : ℝ)|=(17432153/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237243513/10000000000 : ℝ)|^8393 ≤ (42504654443683/100000000000000 : ℝ)^6345
        have hw : |(5237243513/10000000000 : ℝ)|=(5237243513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s3_2 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (214097337/400000000 : ℝ)*x 0 + (5237243659/10000000000 : ℝ)*x 1 + (-2179019/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214097337/400000000 : ℝ)^8393 ≤ (874912704299/2000000000000 : ℝ)^6345 := by
    have hnat : (214097337 : ℕ)^8393*2000000000000^6345 ≤ 874912704299^6345*400000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214097337 400000000 874912704299 2000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237243659/10000000000 : ℝ)^8393 ≤ (8500931202211/20000000000000 : ℝ)^6345 := by
    have hnat : (5237243659 : ℕ)^8393*20000000000000^6345 ≤ 8500931202211^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237243659 10000000000 8500931202211 20000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2179019/9765625 : ℝ)^8393 ≤ (6874854379881/50000000000000 : ℝ)^6345 := by
    have hnat : (2179019 : ℕ)^8393*50000000000000^6345 ≤ 6874854379881^6345*9765625^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179019 9765625 6874854379881 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214097337/400000000 : ℝ), (5237243659/10000000000 : ℝ), (-2179019/9765625 : ℝ)] ![(874912704299/2000000000000 : ℝ), (8500931202211/20000000000000 : ℝ), (6874854379881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214097337/400000000 : ℝ)|^8393 ≤ (874912704299/2000000000000 : ℝ)^6345
        have hw : |(214097337/400000000 : ℝ)|=(214097337/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237243659/10000000000 : ℝ)|^8393 ≤ (8500931202211/20000000000000 : ℝ)^6345
        have hw : |(5237243659/10000000000 : ℝ)|=(5237243659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2179019/9765625 : ℝ)|^8393 ≤ (6874854379881/50000000000000 : ℝ)^6345
        have hw : |(-2179019/9765625 : ℝ)|=(2179019/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s3_3 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272165713/625000000 : ℝ)*x 0 + (4171249513/10000000000 : ℝ)*x 1 + (4545957587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272165713/625000000 : ℝ)^8393 ≤ (8324477920247/25000000000000 : ℝ)^6345 := by
    have hnat : (272165713 : ℕ)^8393*25000000000000^6345 ≤ 8324477920247^6345*625000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272165713 625000000 8324477920247 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171249513/10000000000 : ℝ)^8393 ≤ (31455603582963/100000000000000 : ℝ)^6345 := by
    have hnat : (4171249513 : ℕ)^8393*100000000000000^6345 ≤ 31455603582963^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171249513 10000000000 31455603582963 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4545957587/10000000000 : ℝ)^8393 ≤ (35246484709247/100000000000000 : ℝ)^6345 := by
    have hnat : (4545957587 : ℕ)^8393*100000000000000^6345 ≤ 35246484709247^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4545957587 10000000000 35246484709247 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272165713/625000000 : ℝ), (4171249513/10000000000 : ℝ), (4545957587/10000000000 : ℝ)] ![(8324477920247/25000000000000 : ℝ), (31455603582963/100000000000000 : ℝ), (35246484709247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272165713/625000000 : ℝ)|^8393 ≤ (8324477920247/25000000000000 : ℝ)^6345
        have hw : |(272165713/625000000 : ℝ)|=(272165713/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171249513/10000000000 : ℝ)|^8393 ≤ (31455603582963/100000000000000 : ℝ)^6345
        have hw : |(4171249513/10000000000 : ℝ)|=(4171249513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4545957587/10000000000 : ℝ)|^8393 ≤ (35246484709247/100000000000000 : ℝ)^6345
        have hw : |(4545957587/10000000000 : ℝ)|=(4545957587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s3_4 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-534063709/2500000000 : ℝ)*x 0 + (1309484627/2500000000 : ℝ)*x 1 + (2711384559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534063709/2500000000 : ℝ)^8393 ≤ (12980236462171/100000000000000 : ℝ)^6345 := by
    have hnat : (534063709 : ℕ)^8393*100000000000000^6345 ≤ 12980236462171^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534063709 2500000000 12980236462171 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309484627/2500000000 : ℝ)^8393 ≤ (10628028917871/25000000000000 : ℝ)^6345 := by
    have hnat : (1309484627 : ℕ)^8393*25000000000000^6345 ≤ 10628028917871^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309484627 2500000000 10628028917871 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711384559/5000000000 : ℝ)^8393 ≤ (445076478471/1000000000000 : ℝ)^6345 := by
    have hnat : (2711384559 : ℕ)^8393*1000000000000^6345 ≤ 445076478471^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711384559 5000000000 445076478471 1000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-534063709/2500000000 : ℝ), (1309484627/2500000000 : ℝ), (2711384559/5000000000 : ℝ)] ![(12980236462171/100000000000000 : ℝ), (10628028917871/25000000000000 : ℝ), (445076478471/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-534063709/2500000000 : ℝ)|^8393 ≤ (12980236462171/100000000000000 : ℝ)^6345
        have hw : |(-534063709/2500000000 : ℝ)|=(534063709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309484627/2500000000 : ℝ)|^8393 ≤ (10628028917871/25000000000000 : ℝ)^6345
        have hw : |(1309484627/2500000000 : ℝ)|=(1309484627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711384559/5000000000 : ℝ)|^8393 ≤ (445076478471/1000000000000 : ℝ)^6345
        have hw : |(2711384559/5000000000 : ℝ)|=(2711384559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s3_5 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (331566209/625000000 : ℝ)*x 0 + (-2045789611/10000000000 : ℝ)*x 1 + (5422769041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331566209/625000000 : ℝ)^8393 ≤ (21617101664701/50000000000000 : ℝ)^6345 := by
    have hnat : (331566209 : ℕ)^8393*50000000000000^6345 ≤ 21617101664701^6345*625000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331566209 625000000 21617101664701 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2045789611/10000000000 : ℝ)^8393 ≤ (12258149651323/100000000000000 : ℝ)^6345 := by
    have hnat : (2045789611 : ℕ)^8393*100000000000000^6345 ≤ 12258149651323^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045789611 10000000000 12258149651323 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422769041/10000000000 : ℝ)^8393 ≤ (11126911752783/25000000000000 : ℝ)^6345 := by
    have hnat : (5422769041 : ℕ)^8393*25000000000000^6345 ≤ 11126911752783^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422769041 10000000000 11126911752783 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331566209/625000000 : ℝ), (-2045789611/10000000000 : ℝ), (5422769041/10000000000 : ℝ)] ![(21617101664701/50000000000000 : ℝ), (12258149651323/100000000000000 : ℝ), (11126911752783/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331566209/625000000 : ℝ)|^8393 ≤ (21617101664701/50000000000000 : ℝ)^6345
        have hw : |(331566209/625000000 : ℝ)|=(331566209/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2045789611/10000000000 : ℝ)|^8393 ≤ (12258149651323/100000000000000 : ℝ)^6345
        have hw : |(-2045789611/10000000000 : ℝ)|=(2045789611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422769041/10000000000 : ℝ)|^8393 ≤ (11126911752783/25000000000000 : ℝ)^6345
        have hw : |(5422769041/10000000000 : ℝ)|=(5422769041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s3_6 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652529467/5000000000 : ℝ)*x 0 + (1355692369/2500000000 : ℝ)*x 1 + (-2045789571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652529467/5000000000 : ℝ)^8393 ≤ (43234198909561/100000000000000 : ℝ)^6345 := by
    have hnat : (2652529467 : ℕ)^8393*100000000000000^6345 ≤ 43234198909561^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652529467 5000000000 43234198909561 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355692369/2500000000 : ℝ)^8393 ≤ (44507651733811/100000000000000 : ℝ)^6345 := by
    have hnat : (1355692369 : ℕ)^8393*100000000000000^6345 ≤ 44507651733811^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355692369 2500000000 44507651733811 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2045789571/10000000000 : ℝ)^8393 ≤ (6129074667143/50000000000000 : ℝ)^6345 := by
    have hnat : (2045789571 : ℕ)^8393*50000000000000^6345 ≤ 6129074667143^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045789571 10000000000 6129074667143 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652529467/5000000000 : ℝ), (1355692369/2500000000 : ℝ), (-2045789571/10000000000 : ℝ)] ![(43234198909561/100000000000000 : ℝ), (44507651733811/100000000000000 : ℝ), (6129074667143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652529467/5000000000 : ℝ)|^8393 ≤ (43234198909561/100000000000000 : ℝ)^6345
        have hw : |(2652529467/5000000000 : ℝ)|=(2652529467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355692369/2500000000 : ℝ)|^8393 ≤ (44507651733811/100000000000000 : ℝ)^6345
        have hw : |(1355692369/2500000000 : ℝ)|=(1355692369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2045789571/10000000000 : ℝ)|^8393 ≤ (6129074667143/50000000000000 : ℝ)^6345
        have hw : |(-2045789571/10000000000 : ℝ)|=(2045789571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s3_7 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088670779/2500000000 : ℝ)*x 0 + (4544558597/10000000000 : ℝ)*x 1 + (2086327797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088670779/2500000000 : ℝ)^8393 ≤ (33298232395461/100000000000000 : ℝ)^6345 := by
    have hnat : (1088670779 : ℕ)^8393*100000000000000^6345 ≤ 33298232395461^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088670779 2500000000 33298232395461 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4544558597/10000000000 : ℝ)^8393 ≤ (17616068723031/50000000000000 : ℝ)^6345 := by
    have hnat : (4544558597 : ℕ)^8393*50000000000000^6345 ≤ 17616068723031^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4544558597 10000000000 17616068723031 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086327797/5000000000 : ℝ)^8393 ≤ (6293926030147/20000000000000 : ℝ)^6345 := by
    have hnat : (2086327797 : ℕ)^8393*20000000000000^6345 ≤ 6293926030147^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086327797 5000000000 6293926030147 20000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088670779/2500000000 : ℝ), (4544558597/10000000000 : ℝ), (2086327797/5000000000 : ℝ)] ![(33298232395461/100000000000000 : ℝ), (17616068723031/50000000000000 : ℝ), (6293926030147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088670779/2500000000 : ℝ)|^8393 ≤ (33298232395461/100000000000000 : ℝ)^6345
        have hw : |(1088670779/2500000000 : ℝ)|=(1088670779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4544558597/10000000000 : ℝ)|^8393 ≤ (17616068723031/50000000000000 : ℝ)^6345
        have hw : |(4544558597/10000000000 : ℝ)|=(4544558597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086327797/5000000000 : ℝ)|^8393 ≤ (6293926030147/20000000000000 : ℝ)^6345
        have hw : |(2086327797/5000000000 : ℝ)|=(2086327797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1200_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (373/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (27/250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14741/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1021/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (373/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1021/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (373/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1021/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (373/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1021/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (373/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1021/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (373/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1021/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (373/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (373/4000 : ℝ) ^ (1049/256 : ℝ) ≤ (1199513464202529/20000000000000000000 : ℝ) := by
    have hpowers : (373/4000 : ℝ)^1049 ≤ (1199513464202529/20000000000000000000 : ℝ)^256 := by
      have hnat : (373 : ℕ)^1049*20000000000000000000^256 ≤ 1199513464202529^256*4000^1049 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        373 4000 1199513464202529 20000000000000000000 1049 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (373/4000 : ℝ)) (X := (1199513464202529/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1021/6250 : ℝ) ^ (1049/256 : ℝ) ≤ (29834012371813033/50000000000000000000 : ℝ) := by
    have hpowers : (1021/6250 : ℝ)^1049 ≤ (29834012371813033/50000000000000000000 : ℝ)^256 := by
      have hnat : (1021 : ℕ)^1049*50000000000000000000^256 ≤ 29834012371813033^256*6250^1049 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1021 6250 29834012371813033 50000000000000000000 1049 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1021/6250 : ℝ)) (X := (29834012371813033/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001199513464202529/10000000000000000000 : ℝ) ≤ (1250036589790907/1250000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (10001199513464202529/10000000000000000000 : ℝ)^256 ≤ (1250036589790907/1250000000000000 : ℝ)^1049 := by
      have hnat : (10001199513464202529 : ℕ)^256*1250000000000000^1049 ≤ 1250036589790907^1049*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001199513464202529 10000000000000000000 1250036589790907 1250000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250036589790907/1250000000000000 : ℝ)) (X := (10001199513464202529/10000000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100065665592064638711/100000000000000000000 : ℝ) ≤ (1250200264785461/1250000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (100065665592064638711/100000000000000000000 : ℝ)^256 ≤ (1250200264785461/1250000000000000 : ℝ)^1049 := by
      have hnat : (100065665592064638711 : ℕ)^256*1250000000000000^1049 ≤ 1250200264785461^1049*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100065665592064638711 100000000000000000000 1250200264785461 1250000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250200264785461/1250000000000000 : ℝ)) (X := (100065665592064638711/100000000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25029834012371813033/25000000000000000000 : ℝ) ≤ (250072787956003/250000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (25029834012371813033/25000000000000000000 : ℝ)^256 ≤ (250072787956003/250000000000000 : ℝ)^1049 := by
      have hnat : (25029834012371813033 : ℕ)^256*250000000000000^1049 ≤ 250072787956003^1049*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25029834012371813033 25000000000000000000 250072787956003 250000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250072787956003/250000000000000 : ℝ)) (X := (25029834012371813033/25000000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1199513464202529/20000000000000000000 : ℝ) ≤ ((973439332486179653/973750000000000000 : ℝ)+2*(9093055253/4868750000000 : ℝ)*(373/4000 : ℝ))^(1049/256 : ℝ) := by
    rw [show (973439332486179653/973750000000000000 : ℝ)+2*(9093055253/4868750000000 : ℝ)*(373/4000 : ℝ)=(1250036589790907/1250000000000000 : ℝ) by norm_num, show 1+2*(1199513464202529/20000000000000000000 : ℝ)=(10001199513464202529/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29834012371813033/50000000000000000000 : ℝ)+(1199513464202529/20000000000000000000 : ℝ) ≤ ((973439332486179653/973750000000000000 : ℝ)+(9093055253/4868750000000 : ℝ)*((1021/6250 : ℝ)+(373/4000 : ℝ)))^(1049/256 : ℝ) := by
    rw [show (973439332486179653/973750000000000000 : ℝ)+(9093055253/4868750000000 : ℝ)*((1021/6250 : ℝ)+(373/4000 : ℝ))=(1250200264785461/1250000000000000 : ℝ) by norm_num, show 1+(29834012371813033/50000000000000000000 : ℝ)+(1199513464202529/20000000000000000000 : ℝ)=(100065665592064638711/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29834012371813033/50000000000000000000 : ℝ) ≤ ((973439332486179653/973750000000000000 : ℝ)+2*(9093055253/4868750000000 : ℝ)*(1021/6250 : ℝ))^(1049/256 : ℝ) := by
    rw [show (973439332486179653/973750000000000000 : ℝ)+2*(9093055253/4868750000000 : ℝ)*(1021/6250 : ℝ)=(250072787956003/250000000000000 : ℝ) by norm_num, show 1+2*(29834012371813033/50000000000000000000 : ℝ)=(25029834012371813033/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (973439332486179653/973750000000000000 : ℝ)*(X 1 0+X 2 0)+(9093055253/4868750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (373/4000 : ℝ)) (hi := (1021/6250 : ℝ)) (c := (973439332486179653/973750000000000000 : ℝ)) (alpha := (9093055253/4868750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (973439332486179653/973750000000000000 : ℝ)*(X 0 1+X 2 1)+(9093055253/4868750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (373/4000 : ℝ)) (hi := (1021/6250 : ℝ)) (c := (973439332486179653/973750000000000000 : ℝ)) (alpha := (9093055253/4868750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (973439332486179653/973750000000000000 : ℝ)*(X 0 2+X 1 2)+(9093055253/4868750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (373/4000 : ℝ)) (hi := (1021/6250 : ℝ)) (c := (973439332486179653/973750000000000000 : ℝ)) (alpha := (9093055253/4868750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2136239177/10000000000 : ℝ)*X 0 0+(5423468009/10000000000 : ℝ)*X 0 1+(1309310861/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676216737/5000000000 : ℝ)*X 1 0+(-17432153/78125000 : ℝ)*X 1 1+(5237243513/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214097337/400000000 : ℝ)*X 2 0+(5237243659/10000000000 : ℝ)*X 2 1+(-2179019/9765625 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((272165713/625000000 : ℝ)*X 0 0+(4171249513/10000000000 : ℝ)*X 0 1+(4545957587/10000000000 : ℝ)*X 0 2+(272165713/625000000 : ℝ)*X 1 0+(4171249513/10000000000 : ℝ)*X 1 1+(4545957587/10000000000 : ℝ)*X 1 2+(272165713/625000000 : ℝ)*X 2 0+(4171249513/10000000000 : ℝ)*X 2 1+(4545957587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-534063709/2500000000 : ℝ)*X 0 0+(1309484627/2500000000 : ℝ)*X 0 1+(2711384559/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331566209/625000000 : ℝ)*X 1 0+(-2045789611/10000000000 : ℝ)*X 1 1+(5422769041/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652529467/5000000000 : ℝ)*X 2 0+(1355692369/2500000000 : ℝ)*X 2 1+(-2045789571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1088670779/2500000000 : ℝ)*X 0 0+(4544558597/10000000000 : ℝ)*X 0 1+(2086327797/5000000000 : ℝ)*X 0 2+(1088670779/2500000000 : ℝ)*X 1 0+(4544558597/10000000000 : ℝ)*X 1 1+(2086327797/5000000000 : ℝ)*X 1 2+(1088670779/2500000000 : ℝ)*X 2 0+(4544558597/10000000000 : ℝ)*X 2 1+(2086327797/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (189093405445084548217761009/24343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (168717639/12500000000000 : ℝ)*(base19) + (575591793/50000000000000 : ℝ)*(base23) + (39981999/50000000000000 : ℝ)*(lower2) + (30323097/25000000000000 : ℝ)*(upper3) + (1120653/800000000000 : ℝ)*(upper5) + (1004836225213149/25000000000000 : ℝ)*(major0) + (1004836225213149/25000000000000 : ℝ)*(major1) + (2009672450426299/50000000000000 : ℝ)*(major2) + (5369888852178099/100000000000000 : ℝ)*(sp0) + (2684958805977867/50000000000000 : ℝ)*(sp1) + (5369917810513261/100000000000000 : ℝ)*(sp2) + (1334378633262457/50000000000000 : ℝ)*(sp3) + (7527379687/25000000000000 : ℝ)*(sp4) + (2662912439/20000000000000 : ℝ)*(sp7) + (266877058108711/10000000000000 : ℝ)*(f.failure) + (5369918961696847/100000000000000 : ℝ)*(f.sum) + (13008644460161/3895000000000000000000000000 : ℝ)*base65 + (92032158246932297/24343750000000000000000000000000 : ℝ)*base67 + (69129416172326013/2562500000000000000000000000000 : ℝ)*base69 + (175452786346942703/24343750000000000000000000000000 : ℝ)*base72 + (14145127715961/3895000000000000000000000000 : ℝ)*base73 + (67771044347201013/2562500000000000000000000000000 : ℝ)*base75 + (208357301810086453/24343750000000000000000000000000 : ℝ)*base78 + (278239160921757297/24343750000000000000000000000000 : ℝ)*base79 + (6735407635117/973750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1517971/100000000000000000000 : ℝ)*base89 + (1517971/100000000000000000000 : ℝ)*base91 + (482029/100000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39561278404291833237793731/24343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1168747043/100000000000000 : ℝ)*(base19) + (181792971/20000000000000 : ℝ)*(base23) + (5665583/25000000000000 : ℝ)*(upper3) + (90198283/100000000000000 : ℝ)*(lower4) + (172083851/100000000000000 : ℝ)*(upper5) + (2024807178353447/50000000000000 : ℝ)*(major0) + (2024807178353447/50000000000000 : ℝ)*(major1) + (2024807178353447/50000000000000 : ℝ)*(major2) + (3170994969/12500000000000 : ℝ)*(sp1) + (24061248247/100000000000000 : ℝ)*(sp2) + (5410359720020313/100000000000000 : ℝ)*(sp4) + (5410333183313517/100000000000000 : ℝ)*(sp5) + (5410334749807211/100000000000000 : ℝ)*(sp6) + (1344434469611557/50000000000000 : ℝ)*(sp7) + (1344434469611557/50000000000000 : ℝ)*(f.failure) + (5410359720020313/100000000000000 : ℝ)*(f.sum) + (8569304314073/973750000000000000000000000 : ℝ)*base65 + (356746165623388891/48687500000000000000000000000000 : ℝ)*base67 + (427846002557638891/48687500000000000000000000000000 : ℝ)*base69 + (1187106100199513891/48687500000000000000000000000000 : ℝ)*base71 + (4501093435227/3895000000000000000000000000 : ℝ)*base73 + (558210579533826391/48687500000000000000000000000000 : ℝ)*base75 + (601554305850326391/48687500000000000000000000000000 : ℝ)*base77 + (652951460267451391/48687500000000000000000000000000 : ℝ)*base79 + (7364566563227/3895000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8340823/500000000000000000000 : ℝ)*base90 + (8340823/500000000000000000000 : ℝ)*base92 + (8340823/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1200_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (373/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (27/250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1200_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1200_s4_0 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2138809991/10000000000 : ℝ)*x 0 + (269962339/500000000 : ℝ)*x 1 + (1051956197/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138809991/10000000000 : ℝ)^8393 ≤ (13000777207347/100000000000000 : ℝ)^6345 := by
    have hnat : (2138809991 : ℕ)^8393*100000000000000^6345 ≤ 13000777207347^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138809991 10000000000 13000777207347 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269962339/500000000 : ℝ)^8393 ≤ (8850490214617/20000000000000 : ℝ)^6345 := by
    have hnat : (269962339 : ℕ)^8393*20000000000000^6345 ≤ 8850490214617^6345*500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269962339 500000000 8850490214617 20000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051956197/2000000000 : ℝ)^8393 ≤ (267167323107/625000000000 : ℝ)^6345 := by
    have hnat : (1051956197 : ℕ)^8393*625000000000^6345 ≤ 267167323107^6345*2000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051956197 2000000000 267167323107 625000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2138809991/10000000000 : ℝ), (269962339/500000000 : ℝ), (1051956197/2000000000 : ℝ)] ![(13000777207347/100000000000000 : ℝ), (8850490214617/20000000000000 : ℝ), (267167323107/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2138809991/10000000000 : ℝ)|^8393 ≤ (13000777207347/100000000000000 : ℝ)^6345
        have hw : |(-2138809991/10000000000 : ℝ)|=(2138809991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269962339/500000000 : ℝ)|^8393 ≤ (8850490214617/20000000000000 : ℝ)^6345
        have hw : |(269962339/500000000 : ℝ)|=(269962339/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051956197/2000000000 : ℝ)|^8393 ≤ (267167323107/625000000000 : ℝ)^6345
        have hw : |(1051956197/2000000000 : ℝ)|=(1051956197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s4_1 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346350237/10000000000 : ℝ)*x 0 + (-2209644823/10000000000 : ℝ)*x 1 + (1051956213/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346350237/10000000000 : ℝ)^8393 ≤ (10919970363371/25000000000000 : ℝ)^6345 := by
    have hnat : (5346350237 : ℕ)^8393*25000000000000^6345 ≤ 10919970363371^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346350237 10000000000 10919970363371 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2209644823/10000000000 : ℝ)^8393 ≤ (6786672982413/50000000000000 : ℝ)^6345 := by
    have hnat : (2209644823 : ℕ)^8393*50000000000000^6345 ≤ 6786672982413^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209644823 10000000000 6786672982413 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051956213/2000000000 : ℝ)^8393 ≤ (8549354511429/20000000000000 : ℝ)^6345 := by
    have hnat : (1051956213 : ℕ)^8393*20000000000000^6345 ≤ 8549354511429^6345*2000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051956213 2000000000 8549354511429 20000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346350237/10000000000 : ℝ), (-2209644823/10000000000 : ℝ), (1051956213/2000000000 : ℝ)] ![(10919970363371/25000000000000 : ℝ), (6786672982413/50000000000000 : ℝ), (8549354511429/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346350237/10000000000 : ℝ)|^8393 ≤ (10919970363371/25000000000000 : ℝ)^6345
        have hw : |(5346350237/10000000000 : ℝ)|=(5346350237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2209644823/10000000000 : ℝ)|^8393 ≤ (6786672982413/50000000000000 : ℝ)^6345
        have hw : |(-2209644823/10000000000 : ℝ)|=(2209644823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051956213/2000000000 : ℝ)|^8393 ≤ (8549354511429/20000000000000 : ℝ)^6345
        have hw : |(1051956213/2000000000 : ℝ)|=(1051956213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s4_2 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668293777/1250000000 : ℝ)*x 0 + (5259780971/10000000000 : ℝ)*x 1 + (-2209644977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668293777/1250000000 : ℝ)^8393 ≤ (8735976245307/20000000000000 : ℝ)^6345 := by
    have hnat : (668293777 : ℕ)^8393*20000000000000^6345 ≤ 8735976245307^6345*1250000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668293777 1250000000 8735976245307 20000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259780971/10000000000 : ℝ)^8393 ≤ (5343346443327/12500000000000 : ℝ)^6345 := by
    have hnat : (5259780971 : ℕ)^8393*12500000000000^6345 ≤ 5343346443327^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259780971 10000000000 5343346443327 12500000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2209644977/10000000000 : ℝ)^8393 ≤ (1696668402019/12500000000000 : ℝ)^6345 := by
    have hnat : (2209644977 : ℕ)^8393*12500000000000^6345 ≤ 1696668402019^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209644977 10000000000 1696668402019 12500000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668293777/1250000000 : ℝ), (5259780971/10000000000 : ℝ), (-2209644977/10000000000 : ℝ)] ![(8735976245307/20000000000000 : ℝ), (5343346443327/12500000000000 : ℝ), (1696668402019/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668293777/1250000000 : ℝ)|^8393 ≤ (8735976245307/20000000000000 : ℝ)^6345
        have hw : |(668293777/1250000000 : ℝ)|=(668293777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259780971/10000000000 : ℝ)|^8393 ≤ (5343346443327/12500000000000 : ℝ)^6345
        have hw : |(5259780971/10000000000 : ℝ)|=(5259780971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2209644977/10000000000 : ℝ)|^8393 ≤ (1696668402019/12500000000000 : ℝ)^6345
        have hw : |(-2209644977/10000000000 : ℝ)|=(2209644977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s4_3 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4356188283/10000000000 : ℝ)*x 0 + (2109047129/5000000000 : ℝ)*x 1 + (4498718077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356188283/10000000000 : ℝ)^8393 ≤ (33313457459591/100000000000000 : ℝ)^6345 := by
    have hnat : (4356188283 : ℕ)^8393*100000000000000^6345 ≤ 33313457459591^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356188283 10000000000 33313457459591 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109047129/5000000000 : ℝ)^8393 ≤ (31923729587/100000000000 : ℝ)^6345 := by
    have hnat : (2109047129 : ℕ)^8393*100000000000^6345 ≤ 31923729587^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109047129 5000000000 31923729587 100000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498718077/10000000000 : ℝ)^8393 ≤ (869070323403/2500000000000 : ℝ)^6345 := by
    have hnat : (4498718077 : ℕ)^8393*2500000000000^6345 ≤ 869070323403^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498718077 10000000000 869070323403 2500000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356188283/10000000000 : ℝ), (2109047129/5000000000 : ℝ), (4498718077/10000000000 : ℝ)] ![(33313457459591/100000000000000 : ℝ), (31923729587/100000000000 : ℝ), (869070323403/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356188283/10000000000 : ℝ)|^8393 ≤ (33313457459591/100000000000000 : ℝ)^6345
        have hw : |(4356188283/10000000000 : ℝ)|=(4356188283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2109047129/5000000000 : ℝ)|^8393 ≤ (31923729587/100000000000 : ℝ)^6345
        have hw : |(2109047129/5000000000 : ℝ)|=(2109047129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498718077/10000000000 : ℝ)|^8393 ≤ (869070323403/2500000000000 : ℝ)^6345
        have hw : |(4498718077/10000000000 : ℝ)|=(4498718077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s4_4 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2138816083/10000000000 : ℝ)*x 0 + (5260171331/10000000000 : ℝ)*x 1 + (539885519/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138816083/10000000000 : ℝ)^8393 ≤ (13000826190057/100000000000000 : ℝ)^6345 := by
    have hnat : (2138816083 : ℕ)^8393*100000000000000^6345 ≤ 13000826190057^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138816083 10000000000 13000826190057 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260171331/10000000000 : ℝ)^8393 ≤ (42750968090493/100000000000000 : ℝ)^6345 := by
    have hnat : (5260171331 : ℕ)^8393*100000000000000^6345 ≤ 42750968090493^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260171331 10000000000 42750968090493 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539885519/1000000000 : ℝ)^8393 ≤ (22124102848063/50000000000000 : ℝ)^6345 := by
    have hnat : (539885519 : ℕ)^8393*50000000000000^6345 ≤ 22124102848063^6345*1000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539885519 1000000000 22124102848063 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2138816083/10000000000 : ℝ), (5260171331/10000000000 : ℝ), (539885519/1000000000 : ℝ)] ![(13000826190057/100000000000000 : ℝ), (42750968090493/100000000000000 : ℝ), (22124102848063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2138816083/10000000000 : ℝ)|^8393 ≤ (13000826190057/100000000000000 : ℝ)^6345
        have hw : |(-2138816083/10000000000 : ℝ)|=(2138816083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260171331/10000000000 : ℝ)|^8393 ≤ (42750968090493/100000000000000 : ℝ)^6345
        have hw : |(5260171331/10000000000 : ℝ)|=(5260171331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539885519/1000000000 : ℝ)|^8393 ≤ (22124102848063/50000000000000 : ℝ)^6345
        have hw : |(539885519/1000000000 : ℝ)|=(539885519/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s4_5 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062173889/2000000000 : ℝ)*x 0 + (-2070571589/10000000000 : ℝ)*x 1 + (1349713657/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062173889/2000000000 : ℝ)^8393 ≤ (43296847870073/100000000000000 : ℝ)^6345 := by
    have hnat : (1062173889 : ℕ)^8393*100000000000000^6345 ≤ 43296847870073^6345*2000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062173889 2000000000 43296847870073 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070571589/10000000000 : ℝ)^8393 ≤ (12454952517297/100000000000000 : ℝ)^6345 := by
    have hnat : (2070571589 : ℕ)^8393*100000000000000^6345 ≤ 12454952517297^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070571589 10000000000 12454952517297 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349713657/2500000000 : ℝ)^8393 ≤ (2212409980167/5000000000000 : ℝ)^6345 := by
    have hnat : (1349713657 : ℕ)^8393*5000000000000^6345 ≤ 2212409980167^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349713657 2500000000 2212409980167 5000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062173889/2000000000 : ℝ), (-2070571589/10000000000 : ℝ), (1349713657/2500000000 : ℝ)] ![(43296847870073/100000000000000 : ℝ), (12454952517297/100000000000000 : ℝ), (2212409980167/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062173889/2000000000 : ℝ)|^8393 ≤ (43296847870073/100000000000000 : ℝ)^6345
        have hw : |(1062173889/2000000000 : ℝ)|=(1062173889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2070571589/10000000000 : ℝ)|^8393 ≤ (12454952517297/100000000000000 : ℝ)^6345
        have hw : |(-2070571589/10000000000 : ℝ)|=(2070571589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349713657/2500000000 : ℝ)|^8393 ≤ (2212409980167/5000000000000 : ℝ)^6345
        have hw : |(1349713657/2500000000 : ℝ)|=(1349713657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s4_6 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663858721/1250000000 : ℝ)*x 0 + (2699427317/5000000000 : ℝ)*x 1 + (-1035285571/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663858721/1250000000 : ℝ)^8393 ≤ (10824212838319/25000000000000 : ℝ)^6345 := by
    have hnat : (663858721 : ℕ)^8393*25000000000000^6345 ≤ 10824212838319^6345*1250000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663858721 1250000000 10824212838319 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699427317/5000000000 : ℝ)^8393 ≤ (11062049917097/25000000000000 : ℝ)^6345 := by
    have hnat : (2699427317 : ℕ)^8393*25000000000000^6345 ≤ 11062049917097^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699427317 5000000000 11062049917097 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035285571/5000000000 : ℝ)^8393 ≤ (1556868620077/12500000000000 : ℝ)^6345 := by
    have hnat : (1035285571 : ℕ)^8393*12500000000000^6345 ≤ 1556868620077^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035285571 5000000000 1556868620077 12500000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663858721/1250000000 : ℝ), (2699427317/5000000000 : ℝ), (-1035285571/5000000000 : ℝ)] ![(10824212838319/25000000000000 : ℝ), (11062049917097/25000000000000 : ℝ), (1556868620077/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663858721/1250000000 : ℝ)|^8393 ≤ (10824212838319/25000000000000 : ℝ)^6345
        have hw : |(663858721/1250000000 : ℝ)|=(663858721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699427317/5000000000 : ℝ)|^8393 ≤ (11062049917097/25000000000000 : ℝ)^6345
        have hw : |(2699427317/5000000000 : ℝ)|=(2699427317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1035285571/5000000000 : ℝ)|^8393 ≤ (1556868620077/12500000000000 : ℝ)^6345
        have hw : |(-1035285571/5000000000 : ℝ)|=(1035285571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s4_7 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4356201837/10000000000 : ℝ)*x 0 + (44979323/100000000 : ℝ)*x 1 + (10547207/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356201837/10000000000 : ℝ)^8393 ≤ (33313594568717/100000000000000 : ℝ)^6345 := by
    have hnat : (4356201837 : ℕ)^8393*100000000000000^6345 ≤ 33313594568717^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356201837 10000000000 33313594568717 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44979323/100000000 : ℝ)^8393 ≤ (17377390698307/50000000000000 : ℝ)^6345 := by
    have hnat : (44979323 : ℕ)^8393*50000000000000^6345 ≤ 17377390698307^6345*100000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44979323 100000000 17377390698307 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10547207/25000000 : ℝ)^8393 ≤ (15965812009351/50000000000000 : ℝ)^6345 := by
    have hnat : (10547207 : ℕ)^8393*50000000000000^6345 ≤ 15965812009351^6345*25000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10547207 25000000 15965812009351 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356201837/10000000000 : ℝ), (44979323/100000000 : ℝ), (10547207/25000000 : ℝ)] ![(33313594568717/100000000000000 : ℝ), (17377390698307/50000000000000 : ℝ), (15965812009351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356201837/10000000000 : ℝ)|^8393 ≤ (33313594568717/100000000000000 : ℝ)^6345
        have hw : |(4356201837/10000000000 : ℝ)|=(4356201837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(44979323/100000000 : ℝ)|^8393 ≤ (17377390698307/50000000000000 : ℝ)^6345
        have hw : |(44979323/100000000 : ℝ)|=(44979323/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10547207/25000000 : ℝ)|^8393 ≤ (15965812009351/50000000000000 : ℝ)^6345
        have hw : |(10547207/25000000 : ℝ)|=(10547207/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1200_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (27/250 : ℝ)*pair X i i ≤ pair X i h) :
    (11281/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14741/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (27/250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14741/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (27/250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14741/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (27/250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14741/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (27/250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14741/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (27/250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14741/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (27/250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (27/250 : ℝ) ^ (1049/256 : ℝ) ≤ (87577551212561/800000000000000000 : ℝ) := by
    have hpowers : (27/250 : ℝ)^1049 ≤ (87577551212561/800000000000000000 : ℝ)^256 := by
      have hnat : (27 : ℕ)^1049*800000000000000000^256 ≤ 87577551212561^256*250^1049 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27 250 87577551212561 800000000000000000 1049 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27/250 : ℝ)) (X := (87577551212561/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14741/100000 : ℝ) ^ (1049/256 : ℝ) ≤ (39166002234844863/100000000000000000000 : ℝ) := by
    have hpowers : (14741/100000 : ℝ)^1049 ≤ (39166002234844863/100000000000000000000 : ℝ)^256 := by
      have hnat : (14741 : ℕ)^1049*100000000000000000000^256 ≤ 39166002234844863^256*100000^1049 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14741 100000 39166002234844863 100000000000000000000 1049 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14741/100000 : ℝ)) (X := (39166002234844863/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (400087577551212561/400000000000000000 : ℝ) ≤ (10000534270685569/10000000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (400087577551212561/400000000000000000 : ℝ)^256 ≤ (10000534270685569/10000000000000000 : ℝ)^1049 := by
      have hnat : (400087577551212561 : ℕ)^256*10000000000000000^1049 ≤ 10000534270685569^1049*400000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400087577551212561 400000000000000000 10000534270685569 10000000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000534270685569/10000000000000000 : ℝ)) (X := (400087577551212561/400000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012528299034103747/25000000000000000000 : ℝ) ≤ (5000611370299911/5000000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (25012528299034103747/25000000000000000000 : ℝ)^256 ≤ (5000611370299911/5000000000000000 : ℝ)^1049 := by
      have hnat : (25012528299034103747 : ℕ)^256*5000000000000000^1049 ≤ 5000611370299911^1049*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012528299034103747 25000000000000000000 5000611370299911 5000000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000611370299911/5000000000000000 : ℝ)) (X := (25012528299034103747/25000000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039166002234844863/50000000000000000000 : ℝ) ≤ (400076448420563/400000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (50039166002234844863/50000000000000000000 : ℝ)^256 ≤ (400076448420563/400000000000000 : ℝ)^1049 := by
      have hnat : (50039166002234844863 : ℕ)^256*400000000000000^1049 ≤ 400076448420563^1049*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039166002234844863 50000000000000000000 400076448420563 400000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400076448420563/400000000000000 : ℝ)) (X := (50039166002234844863/50000000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(87577551212561/800000000000000000 : ℝ) ≤ ((39397234610623962629/39410000000000000000 : ℝ)+2*(688469914253/394100000000000 : ℝ)*(27/250 : ℝ))^(1049/256 : ℝ) := by
    rw [show (39397234610623962629/39410000000000000000 : ℝ)+2*(688469914253/394100000000000 : ℝ)*(27/250 : ℝ)=(10000534270685569/10000000000000000 : ℝ) by norm_num, show 1+2*(87577551212561/800000000000000000 : ℝ)=(400087577551212561/400000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39166002234844863/100000000000000000000 : ℝ)+(87577551212561/800000000000000000 : ℝ) ≤ ((39397234610623962629/39410000000000000000 : ℝ)+(688469914253/394100000000000 : ℝ)*((14741/100000 : ℝ)+(27/250 : ℝ)))^(1049/256 : ℝ) := by
    rw [show (39397234610623962629/39410000000000000000 : ℝ)+(688469914253/394100000000000 : ℝ)*((14741/100000 : ℝ)+(27/250 : ℝ))=(5000611370299911/5000000000000000 : ℝ) by norm_num, show 1+(39166002234844863/100000000000000000000 : ℝ)+(87577551212561/800000000000000000 : ℝ)=(25012528299034103747/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39166002234844863/100000000000000000000 : ℝ) ≤ ((39397234610623962629/39410000000000000000 : ℝ)+2*(688469914253/394100000000000 : ℝ)*(14741/100000 : ℝ))^(1049/256 : ℝ) := by
    rw [show (39397234610623962629/39410000000000000000 : ℝ)+2*(688469914253/394100000000000 : ℝ)*(14741/100000 : ℝ)=(400076448420563/400000000000000 : ℝ) by norm_num, show 1+2*(39166002234844863/100000000000000000000 : ℝ)=(50039166002234844863/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39397234610623962629/39410000000000000000 : ℝ)*(X 1 0+X 2 0)+(688469914253/394100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (27/250 : ℝ)) (hi := (14741/100000 : ℝ)) (c := (39397234610623962629/39410000000000000000 : ℝ)) (alpha := (688469914253/394100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39397234610623962629/39410000000000000000 : ℝ)*(X 0 1+X 2 1)+(688469914253/394100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (27/250 : ℝ)) (hi := (14741/100000 : ℝ)) (c := (39397234610623962629/39410000000000000000 : ℝ)) (alpha := (688469914253/394100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39397234610623962629/39410000000000000000 : ℝ)*(X 0 2+X 1 2)+(688469914253/394100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (27/250 : ℝ)) (hi := (14741/100000 : ℝ)) (c := (39397234610623962629/39410000000000000000 : ℝ)) (alpha := (688469914253/394100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2138809991/10000000000 : ℝ)*X 0 0+(269962339/500000000 : ℝ)*X 0 1+(1051956197/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346350237/10000000000 : ℝ)*X 1 0+(-2209644823/10000000000 : ℝ)*X 1 1+(1051956213/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668293777/1250000000 : ℝ)*X 2 0+(5259780971/10000000000 : ℝ)*X 2 1+(-2209644977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4356188283/10000000000 : ℝ)*X 0 0+(2109047129/5000000000 : ℝ)*X 0 1+(4498718077/10000000000 : ℝ)*X 0 2+(4356188283/10000000000 : ℝ)*X 1 0+(2109047129/5000000000 : ℝ)*X 1 1+(4498718077/10000000000 : ℝ)*X 1 2+(4356188283/10000000000 : ℝ)*X 2 0+(2109047129/5000000000 : ℝ)*X 2 1+(4498718077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2138816083/10000000000 : ℝ)*X 0 0+(5260171331/10000000000 : ℝ)*X 0 1+(539885519/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062173889/2000000000 : ℝ)*X 1 0+(-2070571589/10000000000 : ℝ)*X 1 1+(1349713657/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663858721/1250000000 : ℝ)*X 2 0+(2699427317/5000000000 : ℝ)*X 2 1+(-1035285571/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356201837/10000000000 : ℝ)*X 0 0+(44979323/100000000 : ℝ)*X 0 1+(10547207/25000000 : ℝ)*X 0 2+(4356201837/10000000000 : ℝ)*X 1 0+(44979323/100000000 : ℝ)*X 1 1+(10547207/25000000 : ℝ)*X 1 2+(4356201837/10000000000 : ℝ)*X 2 0+(44979323/100000000 : ℝ)*X 2 1+(10547207/25000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4484191416580870314630144309/985250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1430019179/100000000000000 : ℝ)*(base19) + (655402257/50000000000000 : ℝ)*(base23) + (13353013/50000000000000 : ℝ)*(upper2) + (74332343/25000000000000 : ℝ)*(upper3) + (301539/400000000000 : ℝ)*(upper4) + (5366910847298613/100000000000000 : ℝ)*(major0) + (5366910847298613/100000000000000 : ℝ)*(major1) + (2683455423649307/50000000000000 : ℝ)*(major2) + (89628258027877/1250000000000 : ℝ)*(sp0) + (1434058139704351/20000000000000 : ℝ)*(sp1) + (7170290817736421/100000000000000 : ℝ)*(sp2) + (35635064741429/1000000000000 : ℝ)*(sp3) + (1259452431/4000000000000 : ℝ)*(sp4) + (22940202601/100000000000000 : ℝ)*(sp7) + (1781764707172751/50000000000000 : ℝ)*(f.failure) + (1434058425708187/20000000000000 : ℝ)*(f.sum) + (75954002049111/39410000000000000000000000000 : ℝ)*base65 + (2260133817324733577/3941000000000000000000000000000000 : ℝ)*base67 + (26441952702550801897/1970500000000000000000000000000000 : ℝ)*base70 + (21539238432297733577/3941000000000000000000000000000000 : ℝ)*base71 + (177850122296081/39410000000000000000000000000 : ℝ)*base73 + (17212897670413301897/1970500000000000000000000000000000 : ℝ)*base76 + (5202555801590603/1000000000000000000000000000000 : ℝ)*base78 + (14903145419590603/1000000000000000000000000000000 : ℝ)*base80 + (5903538199/17500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (6248411/500000000000000000000 : ℝ)*base89 + (6248411/500000000000000000000 : ℝ)*base91 + (1248411/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2639046785571128826671315859/246312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1092185857/100000000000000 : ℝ)*(base19) + (1269312969/50000000000000 : ℝ)*(base23) + (26216901/50000000000000 : ℝ)*(upper3) + (202771603/50000000000000 : ℝ)*(lower4) + (161562701/50000000000000 : ℝ)*(upper5) + (674640041084957/12500000000000 : ℝ)*(major0) + (674640041084957/12500000000000 : ℝ)*(major1) + (674640041084957/12500000000000 : ℝ)*(major2) + (50398381/1562500000000 : ℝ)*(sp1) + (19895826091/50000000000000 : ℝ)*(sp2) + (360532617483833/5000000000000 : ℝ)*(sp4) + (3605324015997209/50000000000000 : ℝ)*(sp5) + (360530500969927/5000000000000 : ℝ)*(sp6) + (895896987635479/25000000000000 : ℝ)*(sp7) + (895896987635479/25000000000000 : ℝ)*(f.failure) + (360532617483833/5000000000000 : ℝ)*(f.sum) + (15397906814249/2463125000000000000000000000 : ℝ)*base66 + (126406154816189721/70375000000000000000000000000000 : ℝ)*base68 + (488287701468689721/70375000000000000000000000000000 : ℝ)*base70 + (170642433609939721/70375000000000000000000000000000 : ℝ)*base72 + (19079071598031/9852500000000000000000000000 : ℝ)*base74 + (861802480277310279/70375000000000000000000000000000 : ℝ)*base75 + (441875355470189721/70375000000000000000000000000000 : ℝ)*base78 + (221652505910560279/70375000000000000000000000000000 : ℝ)*base79 + (6231550248619/9852500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (791619/250000000000000000000 : ℝ)*base89 + (791619/250000000000000000000 : ℝ)*base91 + (791619/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1200_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14741/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (27/250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1200_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1200_s5_0 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-534831749/2500000000 : ℝ)*x 0 + (2696718177/5000000000 : ℝ)*x 1 + (1053050413/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534831749/2500000000 : ℝ)^8393 ≤ (13004934344881/100000000000000 : ℝ)^6345 := by
    have hnat : (534831749 : ℕ)^8393*100000000000000^6345 ≤ 13004934344881^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534831749 2500000000 13004934344881 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696718177/5000000000 : ℝ)^8393 ≤ (44189468228441/100000000000000 : ℝ)^6345 := by
    have hnat : (2696718177 : ℕ)^8393*100000000000000^6345 ≤ 44189468228441^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696718177 5000000000 44189468228441 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053050413/2000000000 : ℝ)^8393 ≤ (10701399352701/25000000000000 : ℝ)^6345 := by
    have hnat : (1053050413 : ℕ)^8393*25000000000000^6345 ≤ 10701399352701^6345*2000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053050413 2000000000 10701399352701 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-534831749/2500000000 : ℝ), (2696718177/5000000000 : ℝ), (1053050413/2000000000 : ℝ)] ![(13004934344881/100000000000000 : ℝ), (44189468228441/100000000000000 : ℝ), (10701399352701/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-534831749/2500000000 : ℝ)|^8393 ≤ (13004934344881/100000000000000 : ℝ)^6345
        have hw : |(-534831749/2500000000 : ℝ)|=(534831749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696718177/5000000000 : ℝ)|^8393 ≤ (44189468228441/100000000000000 : ℝ)^6345
        have hw : |(2696718177/5000000000 : ℝ)|=(2696718177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053050413/2000000000 : ℝ)|^8393 ≤ (10701399352701/25000000000000 : ℝ)^6345
        have hw : |(1053050413/2000000000 : ℝ)|=(1053050413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s5_1 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534488633/1000000000 : ℝ)*x 0 + (-110217507/500000000 : ℝ)*x 1 + (2632626049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534488633/1000000000 : ℝ)^8393 ≤ (43664061546113/100000000000000 : ℝ)^6345 := by
    have hnat : (534488633 : ℕ)^8393*100000000000000^6345 ≤ 43664061546113^6345*1000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534488633 1000000000 43664061546113 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110217507/500000000 : ℝ)^8393 ≤ (6765170334563/50000000000000 : ℝ)^6345 := by
    have hnat : (110217507 : ℕ)^8393*50000000000000^6345 ≤ 6765170334563^6345*500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110217507 500000000 6765170334563 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632626049/5000000000 : ℝ)^8393 ≤ (42805597765683/100000000000000 : ℝ)^6345 := by
    have hnat : (2632626049 : ℕ)^8393*100000000000000^6345 ≤ 42805597765683^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632626049 5000000000 42805597765683 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534488633/1000000000 : ℝ), (-110217507/500000000 : ℝ), (2632626049/5000000000 : ℝ)] ![(43664061546113/100000000000000 : ℝ), (6765170334563/50000000000000 : ℝ), (42805597765683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534488633/1000000000 : ℝ)|^8393 ≤ (43664061546113/100000000000000 : ℝ)^6345
        have hw : |(534488633/1000000000 : ℝ)|=(534488633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-110217507/500000000 : ℝ)|^8393 ≤ (6765170334563/50000000000000 : ℝ)^6345
        have hw : |(-110217507/500000000 : ℝ)|=(110217507/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632626049/5000000000 : ℝ)|^8393 ≤ (42805597765683/100000000000000 : ℝ)^6345
        have hw : |(2632626049/5000000000 : ℝ)|=(2632626049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s5_2 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344886021/10000000000 : ℝ)*x 0 + (5265252157/10000000000 : ℝ)*x 1 + (-1102175237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344886021/10000000000 : ℝ)^8393 ≤ (43664058207011/100000000000000 : ℝ)^6345 := by
    have hnat : (5344886021 : ℕ)^8393*100000000000000^6345 ≤ 43664058207011^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344886021 10000000000 43664058207011 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265252157/10000000000 : ℝ)^8393 ≤ (8561119680033/20000000000000 : ℝ)^6345 := by
    have hnat : (5265252157 : ℕ)^8393*20000000000000^6345 ≤ 8561119680033^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265252157 10000000000 8561119680033 20000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1102175237/5000000000 : ℝ)^8393 ≤ (6765171690471/50000000000000 : ℝ)^6345 := by
    have hnat : (1102175237 : ℕ)^8393*50000000000000^6345 ≤ 6765171690471^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102175237 5000000000 6765171690471 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344886021/10000000000 : ℝ), (5265252157/10000000000 : ℝ), (-1102175237/5000000000 : ℝ)] ![(43664058207011/100000000000000 : ℝ), (8561119680033/20000000000000 : ℝ), (6765171690471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344886021/10000000000 : ℝ)|^8393 ≤ (43664058207011/100000000000000 : ℝ)^6345
        have hw : |(5344886021/10000000000 : ℝ)|=(5344886021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265252157/10000000000 : ℝ)|^8393 ≤ (8561119680033/20000000000000 : ℝ)^6345
        have hw : |(5265252157/10000000000 : ℝ)|=(5265252157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1102175237/5000000000 : ℝ)|^8393 ≤ (6765171690471/50000000000000 : ℝ)^6345
        have hw : |(-1102175237/5000000000 : ℝ)|=(1102175237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s5_3 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272280827/625000000 : ℝ)*x 0 + (2114702391/5000000000 : ℝ)*x 1 + (224366451/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272280827/625000000 : ℝ)^8393 ≤ (33316542286373/100000000000000 : ℝ)^6345 := by
    have hnat : (272280827 : ℕ)^8393*100000000000000^6345 ≤ 33316542286373^6345*625000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272280827 625000000 33316542286373 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114702391/5000000000 : ℝ)^8393 ≤ (16018504820989/50000000000000 : ℝ)^6345 := by
    have hnat : (2114702391 : ℕ)^8393*50000000000000^6345 ≤ 16018504820989^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114702391 5000000000 16018504820989 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224366451/500000000 : ℝ)^8393 ≤ (3464644805803/10000000000000 : ℝ)^6345 := by
    have hnat : (224366451 : ℕ)^8393*10000000000000^6345 ≤ 3464644805803^6345*500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224366451 500000000 3464644805803 10000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272280827/625000000 : ℝ), (2114702391/5000000000 : ℝ), (224366451/500000000 : ℝ)] ![(33316542286373/100000000000000 : ℝ), (16018504820989/50000000000000 : ℝ), (3464644805803/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272280827/625000000 : ℝ)|^8393 ≤ (33316542286373/100000000000000 : ℝ)^6345
        have hw : |(272280827/625000000 : ℝ)|=(272280827/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114702391/5000000000 : ℝ)|^8393 ≤ (16018504820989/50000000000000 : ℝ)^6345
        have hw : |(2114702391/5000000000 : ℝ)|=(2114702391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224366451/500000000 : ℝ)|^8393 ≤ (3464644805803/10000000000000 : ℝ)^6345
        have hw : |(224366451/500000000 : ℝ)|=(224366451/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s5_4 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1069666019/5000000000 : ℝ)*x 0 + (1053116477/2000000000 : ℝ)*x 1 + (5393104841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069666019/5000000000 : ℝ)^8393 ≤ (3251243722057/25000000000000 : ℝ)^6345 := by
    have hnat : (1069666019 : ℕ)^8393*25000000000000^6345 ≤ 3251243722057^6345*5000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069666019 5000000000 3251243722057 25000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053116477/2000000000 : ℝ)^8393 ≤ (42809149683183/100000000000000 : ℝ)^6345 := by
    have hnat : (1053116477 : ℕ)^8393*100000000000000^6345 ≤ 42809149683183^6345*2000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053116477 2000000000 42809149683183 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393104841/10000000000 : ℝ)^8393 ≤ (4418587541167/10000000000000 : ℝ)^6345 := by
    have hnat : (5393104841 : ℕ)^8393*10000000000000^6345 ≤ 4418587541167^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393104841 10000000000 4418587541167 10000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1069666019/5000000000 : ℝ), (1053116477/2000000000 : ℝ), (5393104841/10000000000 : ℝ)] ![(3251243722057/25000000000000 : ℝ), (42809149683183/100000000000000 : ℝ), (4418587541167/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1069666019/5000000000 : ℝ)|^8393 ≤ (3251243722057/25000000000000 : ℝ)^6345
        have hw : |(-1069666019/5000000000 : ℝ)|=(1069666019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053116477/2000000000 : ℝ)|^8393 ≤ (42809149683183/100000000000000 : ℝ)^6345
        have hw : |(1053116477/2000000000 : ℝ)|=(1053116477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393104841/10000000000 : ℝ)|^8393 ≤ (4418587541167/10000000000000 : ℝ)^6345
        have hw : |(5393104841/10000000000 : ℝ)|=(5393104841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s5_5 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312274743/10000000000 : ℝ)*x 0 + (-83059891/400000000 : ℝ)*x 1 + (1348276159/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312274743/10000000000 : ℝ)^8393 ≤ (42296878051/97656250000 : ℝ)^6345 := by
    have hnat : (5312274743 : ℕ)^8393*97656250000^6345 ≤ 42296878051^6345*10000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312274743 10000000000 42296878051 97656250000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83059891/400000000 : ℝ)^8393 ≤ (195345682307/1562500000000 : ℝ)^6345 := by
    have hnat : (83059891 : ℕ)^8393*1562500000000^6345 ≤ 195345682307^6345*400000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83059891 400000000 195345682307 1562500000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348276159/2500000000 : ℝ)^8393 ≤ (44185873189977/100000000000000 : ℝ)^6345 := by
    have hnat : (1348276159 : ℕ)^8393*100000000000000^6345 ≤ 44185873189977^6345*2500000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348276159 2500000000 44185873189977 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312274743/10000000000 : ℝ), (-83059891/400000000 : ℝ), (1348276159/2500000000 : ℝ)] ![(42296878051/97656250000 : ℝ), (195345682307/1562500000000 : ℝ), (44185873189977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312274743/10000000000 : ℝ)|^8393 ≤ (42296878051/97656250000 : ℝ)^6345
        have hw : |(5312274743/10000000000 : ℝ)|=(5312274743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-83059891/400000000 : ℝ)|^8393 ≤ (195345682307/1562500000000 : ℝ)^6345
        have hw : |(-83059891/400000000 : ℝ)|=(83059891/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348276159/2500000000 : ℝ)|^8393 ≤ (44185873189977/100000000000000 : ℝ)^6345
        have hw : |(1348276159/2500000000 : ℝ)|=(1348276159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s5_6 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (83004287/156250000 : ℝ)*x 0 + (84267267/156250000 : ℝ)*x 1 + (-129781073/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83004287/156250000 : ℝ)^8393 ≤ (5413999884989/12500000000000 : ℝ)^6345 := by
    have hnat : (83004287 : ℕ)^8393*12500000000000^6345 ≤ 5413999884989^6345*156250000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83004287 156250000 5413999884989 12500000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84267267/156250000 : ℝ)^8393 ≤ (44185878088539/100000000000000 : ℝ)^6345 := by
    have hnat : (84267267 : ℕ)^8393*100000000000000^6345 ≤ 44185878088539^6345*156250000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84267267 156250000 44185878088539 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129781073/625000000 : ℝ)^8393 ≤ (12502122815487/100000000000000 : ℝ)^6345 := by
    have hnat : (129781073 : ℕ)^8393*100000000000000^6345 ≤ 12502122815487^6345*625000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129781073 625000000 12502122815487 100000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83004287/156250000 : ℝ), (84267267/156250000 : ℝ), (-129781073/625000000 : ℝ)] ![(5413999884989/12500000000000 : ℝ), (44185878088539/100000000000000 : ℝ), (12502122815487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83004287/156250000 : ℝ)|^8393 ≤ (5413999884989/12500000000000 : ℝ)^6345
        have hw : |(83004287/156250000 : ℝ)|=(83004287/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84267267/156250000 : ℝ)|^8393 ≤ (44185878088539/100000000000000 : ℝ)^6345
        have hw : |(84267267/156250000 : ℝ)|=(84267267/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-129781073/625000000 : ℝ)|^8393 ≤ (12502122815487/100000000000000 : ℝ)^6345
        have hw : |(-129781073/625000000 : ℝ)|=(129781073/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1200_s5_7 (p : ℝ) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4254398/9765625 : ℝ)*x 0 + (560833091/1250000000 : ℝ)*x 1 + (846014287/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4254398/9765625 : ℝ)^8393 ≤ (666332933669/2000000000000 : ℝ)^6345 := by
    have hnat : (4254398 : ℕ)^8393*2000000000000^6345 ≤ 666332933669^6345*9765625^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254398 9765625 666332933669 2000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560833091/1250000000 : ℝ)^8393 ≤ (17319831878999/50000000000000 : ℝ)^6345 := by
    have hnat : (560833091 : ℕ)^8393*50000000000000^6345 ≤ 17319831878999^6345*1250000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560833091 1250000000 17319831878999 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846014287/2000000000 : ℝ)^8393 ≤ (16021844765149/50000000000000 : ℝ)^6345 := by
    have hnat : (846014287 : ℕ)^8393*50000000000000^6345 ≤ 16021844765149^6345*2000000000^8393 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846014287 2000000000 16021844765149 50000000000000 8393 6345 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8393/2048 : ℝ)) 8393 6345 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4254398/9765625 : ℝ), (560833091/1250000000 : ℝ), (846014287/2000000000 : ℝ)] ![(666332933669/2000000000000 : ℝ), (17319831878999/50000000000000 : ℝ), (16021844765149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4254398/9765625 : ℝ)|^8393 ≤ (666332933669/2000000000000 : ℝ)^6345
        have hw : |(4254398/9765625 : ℝ)|=(4254398/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560833091/1250000000 : ℝ)|^8393 ≤ (17319831878999/50000000000000 : ℝ)^6345
        have hw : |(560833091/1250000000 : ℝ)|=(560833091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(846014287/2000000000 : ℝ)|^8393 ≤ (16021844765149/50000000000000 : ℝ)^6345
        have hw : |(846014287/2000000000 : ℝ)|=(846014287/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1200_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11397/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14113/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11281/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11281/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11281/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11281/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11281/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11281/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11281/100000 : ℝ) ^ (1049/256 : ℝ) ≤ (3271796065483009/25000000000000000000 : ℝ) := by
    have hpowers : (11281/100000 : ℝ)^1049 ≤ (3271796065483009/25000000000000000000 : ℝ)^256 := by
      have hnat : (11281 : ℕ)^1049*25000000000000000000^256 ≤ 3271796065483009^256*100000^1049 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11281 100000 3271796065483009 25000000000000000000 1049 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11281/100000 : ℝ)) (X := (3271796065483009/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (1049/256 : ℝ) ≤ (1697148934633901/5000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^1049 ≤ (1697148934633901/5000000000000000000 : ℝ)^256 := by
      have hnat : (2847 : ℕ)^1049*5000000000000000000^256 ≤ 1697148934633901^256*20000^1049 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 1697148934633901 5000000000000000000 1049 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (1697148934633901/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503271796065483009/12500000000000000000 : ℝ) ≤ (312519959412313/312500000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (12503271796065483009/12500000000000000000 : ℝ)^256 ≤ (312519959412313/312500000000000 : ℝ)^1049 := by
      have hnat : (12503271796065483009 : ℕ)^256*312500000000000^1049 ≤ 312519959412313^1049*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503271796065483009 12500000000000000000 312519959412313 312500000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312519959412313/312500000000000 : ℝ)) (X := (12503271796065483009/12500000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505878770369326257/12500000000000000000 : ℝ) ≤ (5000573764636531/5000000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (12505878770369326257/12500000000000000000 : ℝ)^256 ≤ (5000573764636531/5000000000000000 : ℝ)^1049 := by
      have hnat : (12505878770369326257 : ℕ)^256*5000000000000000^1049 ≤ 5000573764636531^1049*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505878770369326257 12500000000000000000 5000573764636531 5000000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000573764636531/5000000000000000 : ℝ)) (X := (12505878770369326257/12500000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501697148934633901/2500000000000000000 : ℝ) ≤ (2500414089338027/2500000000000000 : ℝ) ^ (1049/256 : ℝ) := by
    have hpowers : (2501697148934633901/2500000000000000000 : ℝ)^256 ≤ (2500414089338027/2500000000000000 : ℝ)^1049 := by
      have hnat : (2501697148934633901 : ℕ)^256*2500000000000000^1049 ≤ 2500414089338027^1049*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501697148934633901 2500000000000000000 2500414089338027 2500000000000000 256 1049 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500414089338027/2500000000000000 : ℝ)) (X := (2501697148934633901/2500000000000000000 : ℝ)) (by norm_num) 1049 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3271796065483009/25000000000000000000 : ℝ) ≤ ((1054657376578845979/1055000000000000000 : ℝ)+2*(36344862789/21100000000000 : ℝ)*(11281/100000 : ℝ))^(1049/256 : ℝ) := by
    rw [show (1054657376578845979/1055000000000000000 : ℝ)+2*(36344862789/21100000000000 : ℝ)*(11281/100000 : ℝ)=(312519959412313/312500000000000 : ℝ) by norm_num, show 1+2*(3271796065483009/25000000000000000000 : ℝ)=(12503271796065483009/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1697148934633901/5000000000000000000 : ℝ)+(3271796065483009/25000000000000000000 : ℝ) ≤ ((1054657376578845979/1055000000000000000 : ℝ)+(36344862789/21100000000000 : ℝ)*((2847/20000 : ℝ)+(11281/100000 : ℝ)))^(1049/256 : ℝ) := by
    rw [show (1054657376578845979/1055000000000000000 : ℝ)+(36344862789/21100000000000 : ℝ)*((2847/20000 : ℝ)+(11281/100000 : ℝ))=(5000573764636531/5000000000000000 : ℝ) by norm_num, show 1+(1697148934633901/5000000000000000000 : ℝ)+(3271796065483009/25000000000000000000 : ℝ)=(12505878770369326257/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1697148934633901/5000000000000000000 : ℝ) ≤ ((1054657376578845979/1055000000000000000 : ℝ)+2*(36344862789/21100000000000 : ℝ)*(2847/20000 : ℝ))^(1049/256 : ℝ) := by
    rw [show (1054657376578845979/1055000000000000000 : ℝ)+2*(36344862789/21100000000000 : ℝ)*(2847/20000 : ℝ)=(2500414089338027/2500000000000000 : ℝ) by norm_num, show 1+2*(1697148934633901/5000000000000000000 : ℝ)=(2501697148934633901/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1054657376578845979/1055000000000000000 : ℝ)*(X 1 0+X 2 0)+(36344862789/21100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (11281/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1054657376578845979/1055000000000000000 : ℝ)) (alpha := (36344862789/21100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1054657376578845979/1055000000000000000 : ℝ)*(X 0 1+X 2 1)+(36344862789/21100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (11281/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1054657376578845979/1055000000000000000 : ℝ)) (alpha := (36344862789/21100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1054657376578845979/1055000000000000000 : ℝ)*(X 0 2+X 1 2)+(36344862789/21100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1049/256 : ℝ)) (lo := (11281/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1054657376578845979/1055000000000000000 : ℝ)) (alpha := (36344862789/21100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-534831749/2500000000 : ℝ)*X 0 0+(2696718177/5000000000 : ℝ)*X 0 1+(1053050413/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534488633/1000000000 : ℝ)*X 1 0+(-110217507/500000000 : ℝ)*X 1 1+(2632626049/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344886021/10000000000 : ℝ)*X 2 0+(5265252157/10000000000 : ℝ)*X 2 1+(-1102175237/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((272280827/625000000 : ℝ)*X 0 0+(2114702391/5000000000 : ℝ)*X 0 1+(224366451/500000000 : ℝ)*X 0 2+(272280827/625000000 : ℝ)*X 1 0+(2114702391/5000000000 : ℝ)*X 1 1+(224366451/500000000 : ℝ)*X 1 2+(272280827/625000000 : ℝ)*X 2 0+(2114702391/5000000000 : ℝ)*X 2 1+(224366451/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1069666019/5000000000 : ℝ)*X 0 0+(1053116477/2000000000 : ℝ)*X 0 1+(5393104841/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312274743/10000000000 : ℝ)*X 1 0+(-83059891/400000000 : ℝ)*X 1 1+(1348276159/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((83004287/156250000 : ℝ)*X 2 0+(84267267/156250000 : ℝ)*X 2 1+(-129781073/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4254398/9765625 : ℝ)*X 0 0+(560833091/1250000000 : ℝ)*X 0 1+(846014287/2000000000 : ℝ)*X 0 2+(4254398/9765625 : ℝ)*X 1 0+(560833091/1250000000 : ℝ)*X 1 1+(846014287/2000000000 : ℝ)*X 1 2+(4254398/9765625 : ℝ)*X 2 0+(560833091/1250000000 : ℝ)*X 2 1+(846014287/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1200_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2278281537729803840349/211000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1142250089/50000000000000 : ℝ)*(base19) + (430615637/20000000000000 : ℝ)*(base23) + (22664689/100000000000000 : ℝ)*(lower2) + (47368379/12500000000000 : ℝ)*(upper3) + (193484631/100000000000000 : ℝ)*(lower4) + (1167859617287323/20000000000000 : ℝ)*(major0) + (1167859617287323/20000000000000 : ℝ)*(major1) + (729912260804577/12500000000000 : ℝ)*(major2) + (7801353044067531/100000000000000 : ℝ)*(sp0) + (1950351933830921/25000000000000 : ℝ)*(sp1) + (7801407866745677/100000000000000 : ℝ)*(sp2) + (3877144812257839/100000000000000 : ℝ)*(sp3) + (56975756331/100000000000000 : ℝ)*(sp4) + (40980873429/100000000000000 : ℝ)*(sp7) + (969296448282817/25000000000000 : ℝ)*(f.failure) + (3900705009911931/50000000000000 : ℝ)*(f.sum) + (1344366162961/2110000000000000000000000000 : ℝ)*base66 + (109979242554435783/21100000000000000000000000000000 : ℝ)*base68 + (230350051615777133/13187500000000000000000000000000 : ℝ)*base69 + (152320019412864217/21100000000000000000000000000000 : ℝ)*base71 + (2029066709759/2110000000000000000000000000 : ℝ)*base73 + (85363830247097867/13187500000000000000000000000000 : ℝ)*base76 + (88178835198274217/21100000000000000000000000000000 : ℝ)*base77 + (112503835050325783/21100000000000000000000000000000 : ℝ)*base80 + (43105328099/10550000000000000000000000 : ℝ)*base81 + (1462037/250000000000000000000 : ℝ)*base89 + (1462037/250000000000000000000 : ℝ)*base91 + (1037963/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1212862417293345048987/211000000000000000000000000 : ℝ) := by norm_num
    linear_combination (582929653/25000000000000 : ℝ)*(base19) + (23928703/1000000000000 : ℝ)*(base23) + (9159461/5000000000000 : ℝ)*(upper3) + (248977391/100000000000000 : ℝ)*(lower4) + (1173896272084253/20000000000000 : ℝ)*(major0) + (1173896272084253/20000000000000 : ℝ)*(major1) + (1173896272084253/20000000000000 : ℝ)*(major2) + (57116861183/100000000000000 : ℝ)*(sp1) + (80903660413/100000000000000 : ℝ)*(sp2) + (4925696219/100000000000000 : ℝ)*(sp3) + (7841735601135279/100000000000000 : ℝ)*(sp4) + (1568335230511097/20000000000000 : ℝ)*(sp5) + (1568330460920913/20000000000000 : ℝ)*(sp6) + (1948611001202793/50000000000000 : ℝ)*(sp7) + (974306732025451/25000000000000 : ℝ)*(f.failure) + (7841735601135279/100000000000000 : ℝ)*(f.sum) + (890501963441/211000000000000000000000000 : ℝ)*base66 + (22931184950018687/21100000000000000000000000000000 : ℝ)*base67 + (80003590677218687/21100000000000000000000000000000 : ℝ)*base69 + (245087867148381313/21100000000000000000000000000000 : ℝ)*base72 + (1102298041/52750000000000000000000000 : ℝ)*base74 + (48610504653281313/21100000000000000000000000000000 : ℝ)*base76 + (51055070241181313/21100000000000000000000000000000 : ℝ)*base78 + (171288932169418687/21100000000000000000000000000000 : ℝ)*base79 + (500930749671/211000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (1616889/250000000000000000000 : ℝ)*base90 + (1616889/250000000000000000000 : ℝ)*base92 + (1616889/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1200_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1200_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1200_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (373/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1200_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1200_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1200_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1049/256 : ℝ) ≤ p) (hpb : p ≤ (8393/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15060661/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (373/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1200_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

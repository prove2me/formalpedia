-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1394_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:43:53.171998+00:00
-- url     : https://prove2.me/submissions/33d2cde6-b92c-46cd-8a09-8fbd0f7fb186

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
theorem support_rectangle_w1394_s0_0 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1778801423/10000000000 : ℝ)*x 0 + (597475871/1000000000 : ℝ)*x 1 + (4823163187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1778801423/10000000000 : ℝ)^2177 ≤ (1307513097721/12500000000000 : ℝ)^1665 := by
    have hnat : (1778801423 : ℕ)^2177*12500000000000^1665 ≤ 1307513097721^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1778801423 10000000000 1307513097721 12500000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597475871/1000000000 : ℝ)^2177 ≤ (25498064195341/50000000000000 : ℝ)^1665 := by
    have hnat : (597475871 : ℕ)^2177*50000000000000^1665 ≤ 25498064195341^1665*1000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597475871 1000000000 25498064195341 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4823163187/10000000000 : ℝ)^2177 ≤ (4817970851617/12500000000000 : ℝ)^1665 := by
    have hnat : (4823163187 : ℕ)^2177*12500000000000^1665 ≤ 4817970851617^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4823163187 10000000000 4817970851617 12500000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1778801423/10000000000 : ℝ), (597475871/1000000000 : ℝ), (4823163187/10000000000 : ℝ)] ![(1307513097721/12500000000000 : ℝ), (25498064195341/50000000000000 : ℝ), (4817970851617/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1778801423/10000000000 : ℝ)|^2177 ≤ (1307513097721/12500000000000 : ℝ)^1665
        have hw : |(-1778801423/10000000000 : ℝ)|=(1778801423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(597475871/1000000000 : ℝ)|^2177 ≤ (25498064195341/50000000000000 : ℝ)^1665
        have hw : |(597475871/1000000000 : ℝ)|=(597475871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4823163187/10000000000 : ℝ)|^2177 ≤ (4817970851617/12500000000000 : ℝ)^1665
        have hw : |(4823163187/10000000000 : ℝ)|=(4823163187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s0_1 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5495998739/10000000000 : ℝ)*x 0 + (-151933061/625000000 : ℝ)*x 1 + (2411581679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5495998739/10000000000 : ℝ)^2177 ≤ (22860146757281/50000000000000 : ℝ)^1665 := by
    have hnat : (5495998739 : ℕ)^2177*50000000000000^1665 ≤ 22860146757281^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495998739 10000000000 22860146757281 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (151933061/625000000 : ℝ)^2177 ≤ (1920890853/12207031250 : ℝ)^1665 := by
    have hnat : (151933061 : ℕ)^2177*12207031250^1665 ≤ 1920890853^1665*625000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151933061 625000000 1920890853 12207031250 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2411581679/5000000000 : ℝ)^2177 ≤ (38543768599681/100000000000000 : ℝ)^1665 := by
    have hnat : (2411581679 : ℕ)^2177*100000000000000^1665 ≤ 38543768599681^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2411581679 5000000000 38543768599681 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5495998739/10000000000 : ℝ), (-151933061/625000000 : ℝ), (2411581679/5000000000 : ℝ)] ![(22860146757281/50000000000000 : ℝ), (1920890853/12207031250 : ℝ), (38543768599681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5495998739/10000000000 : ℝ)|^2177 ≤ (22860146757281/50000000000000 : ℝ)^1665
        have hw : |(5495998739/10000000000 : ℝ)|=(5495998739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-151933061/625000000 : ℝ)|^2177 ≤ (1920890853/12207031250 : ℝ)^1665
        have hw : |(-151933061/625000000 : ℝ)|=(151933061/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2411581679/5000000000 : ℝ)|^2177 ≤ (38543768599681/100000000000000 : ℝ)^1665
        have hw : |(2411581679/5000000000 : ℝ)|=(2411581679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s0_2 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5495998747/10000000000 : ℝ)*x 0 + (964632667/2000000000 : ℝ)*x 1 + (-1215464497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5495998747/10000000000 : ℝ)^2177 ≤ (45720293601577/100000000000000 : ℝ)^1665 := by
    have hnat : (5495998747 : ℕ)^2177*100000000000000^1665 ≤ 45720293601577^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495998747 10000000000 45720293601577 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (964632667/2000000000 : ℝ)^2177 ≤ (19271884179679/50000000000000 : ℝ)^1665 := by
    have hnat : (964632667 : ℕ)^2177*50000000000000^1665 ≤ 19271884179679^1665*2000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964632667 2000000000 19271884179679 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1215464497/5000000000 : ℝ)^2177 ≤ (3933984505031/25000000000000 : ℝ)^1665 := by
    have hnat : (1215464497 : ℕ)^2177*25000000000000^1665 ≤ 3933984505031^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1215464497 5000000000 3933984505031 25000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5495998747/10000000000 : ℝ), (964632667/2000000000 : ℝ), (-1215464497/5000000000 : ℝ)] ![(45720293601577/100000000000000 : ℝ), (19271884179679/50000000000000 : ℝ), (3933984505031/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5495998747/10000000000 : ℝ)|^2177 ≤ (45720293601577/100000000000000 : ℝ)^1665
        have hw : |(5495998747/10000000000 : ℝ)|=(5495998747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(964632667/2000000000 : ℝ)|^2177 ≤ (19271884179679/50000000000000 : ℝ)^1665
        have hw : |(964632667/2000000000 : ℝ)|=(964632667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1215464497/5000000000 : ℝ)|^2177 ≤ (3933984505031/25000000000000 : ℝ)^1665
        have hw : |(-1215464497/5000000000 : ℝ)|=(1215464497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s0_3 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1042765827/2500000000 : ℝ)*x 0 + (3104388007/10000000000 : ℝ)*x 1 + (2781881477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042765827/2500000000 : ℝ)^2177 ≤ (15938220110821/50000000000000 : ℝ)^1665 := by
    have hnat : (1042765827 : ℕ)^2177*50000000000000^1665 ≤ 15938220110821^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042765827 2500000000 15938220110821 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3104388007/10000000000 : ℝ)^2177 ≤ (10832402940473/50000000000000 : ℝ)^1665 := by
    have hnat : (3104388007 : ℕ)^2177*50000000000000^1665 ≤ 10832402940473^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104388007 10000000000 10832402940473 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2781881477/5000000000 : ℝ)^2177 ≤ (46458753883723/100000000000000 : ℝ)^1665 := by
    have hnat : (2781881477 : ℕ)^2177*100000000000000^1665 ≤ 46458753883723^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2781881477 5000000000 46458753883723 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042765827/2500000000 : ℝ), (3104388007/10000000000 : ℝ), (2781881477/5000000000 : ℝ)] ![(15938220110821/50000000000000 : ℝ), (10832402940473/50000000000000 : ℝ), (46458753883723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042765827/2500000000 : ℝ)|^2177 ≤ (15938220110821/50000000000000 : ℝ)^1665
        have hw : |(1042765827/2500000000 : ℝ)|=(1042765827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3104388007/10000000000 : ℝ)|^2177 ≤ (10832402940473/50000000000000 : ℝ)^1665
        have hw : |(3104388007/10000000000 : ℝ)|=(3104388007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2781881477/5000000000 : ℝ)|^2177 ≤ (46458753883723/100000000000000 : ℝ)^1665
        have hw : |(2781881477/5000000000 : ℝ)|=(2781881477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s0_4 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-891495891/5000000000 : ℝ)*x 0 + (970540593/2000000000 : ℝ)*x 1 + (2972081543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (891495891/5000000000 : ℝ)^2177 ≤ (10492334846499/100000000000000 : ℝ)^1665 := by
    have hnat : (891495891 : ℕ)^2177*100000000000000^1665 ≤ 10492334846499^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891495891 5000000000 10492334846499 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (970540593/2000000000 : ℝ)^2177 ≤ (4856589033719/12500000000000 : ℝ)^1665 := by
    have hnat : (970540593 : ℕ)^2177*12500000000000^1665 ≤ 4856589033719^1665*2000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970540593 2000000000 4856589033719 12500000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2972081543/5000000000 : ℝ)^2177 ≤ (50654952870981/100000000000000 : ℝ)^1665 := by
    have hnat : (2972081543 : ℕ)^2177*100000000000000^1665 ≤ 50654952870981^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2972081543 5000000000 50654952870981 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-891495891/5000000000 : ℝ), (970540593/2000000000 : ℝ), (2972081543/5000000000 : ℝ)] ![(10492334846499/100000000000000 : ℝ), (4856589033719/12500000000000 : ℝ), (50654952870981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-891495891/5000000000 : ℝ)|^2177 ≤ (10492334846499/100000000000000 : ℝ)^1665
        have hw : |(-891495891/5000000000 : ℝ)|=(891495891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(970540593/2000000000 : ℝ)|^2177 ≤ (4856589033719/12500000000000 : ℝ)^1665
        have hw : |(970540593/2000000000 : ℝ)|=(970540593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2972081543/5000000000 : ℝ)|^2177 ≤ (50654952870981/100000000000000 : ℝ)^1665
        have hw : |(2972081543/5000000000 : ℝ)|=(2972081543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s0_5 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (518185733/1000000000 : ℝ)*x 0 + (-327482213/2500000000 : ℝ)*x 1 + (5944160951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518185733/1000000000 : ℝ)^2177 ≤ (529172902949/1250000000000 : ℝ)^1665 := by
    have hnat : (518185733 : ℕ)^2177*1250000000000^1665 ≤ 529172902949^1665*1000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518185733 1000000000 529172902949 1250000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327482213/2500000000 : ℝ)^2177 ≤ (3505619331277/50000000000000 : ℝ)^1665 := by
    have hnat : (327482213 : ℕ)^2177*50000000000000^1665 ≤ 3505619331277^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327482213 2500000000 3505619331277 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5944160951/10000000000 : ℝ)^2177 ≤ (25327464541071/50000000000000 : ℝ)^1665 := by
    have hnat : (5944160951 : ℕ)^2177*50000000000000^1665 ≤ 25327464541071^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5944160951 10000000000 25327464541071 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518185733/1000000000 : ℝ), (-327482213/2500000000 : ℝ), (5944160951/10000000000 : ℝ)] ![(529172902949/1250000000000 : ℝ), (3505619331277/50000000000000 : ℝ), (25327464541071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518185733/1000000000 : ℝ)|^2177 ≤ (529172902949/1250000000000 : ℝ)^1665
        have hw : |(518185733/1000000000 : ℝ)|=(518185733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-327482213/2500000000 : ℝ)|^2177 ≤ (3505619331277/50000000000000 : ℝ)^1665
        have hw : |(-327482213/2500000000 : ℝ)|=(327482213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5944160951/10000000000 : ℝ)|^2177 ≤ (25327464541071/50000000000000 : ℝ)^1665
        have hw : |(5944160951/10000000000 : ℝ)|=(5944160951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s0_6 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (518185259/1000000000 : ℝ)*x 0 + (5944166177/10000000000 : ℝ)*x 1 + (-654963883/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (518185259/1000000000 : ℝ)^2177 ≤ (5291722700497/12500000000000 : ℝ)^1665 := by
    have hnat : (518185259 : ℕ)^2177*12500000000000^1665 ≤ 5291722700497^1665*1000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518185259 1000000000 5291722700497 12500000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5944166177/10000000000 : ℝ)^2177 ≤ (12663746827969/25000000000000 : ℝ)^1665 := by
    have hnat : (5944166177 : ℕ)^2177*25000000000000^1665 ≤ 12663746827969^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5944166177 10000000000 12663746827969 25000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654963883/5000000000 : ℝ)^2177 ≤ (280449242497/4000000000000 : ℝ)^1665 := by
    have hnat : (654963883 : ℕ)^2177*4000000000000^1665 ≤ 280449242497^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654963883 5000000000 280449242497 4000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(518185259/1000000000 : ℝ), (5944166177/10000000000 : ℝ), (-654963883/5000000000 : ℝ)] ![(5291722700497/12500000000000 : ℝ), (12663746827969/25000000000000 : ℝ), (280449242497/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(518185259/1000000000 : ℝ)|^2177 ≤ (5291722700497/12500000000000 : ℝ)^1665
        have hw : |(518185259/1000000000 : ℝ)|=(518185259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5944166177/10000000000 : ℝ)|^2177 ≤ (12663746827969/25000000000000 : ℝ)^1665
        have hw : |(5944166177/10000000000 : ℝ)|=(5944166177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-654963883/5000000000 : ℝ)|^2177 ≤ (280449242497/4000000000000 : ℝ)^1665
        have hw : |(-654963883/5000000000 : ℝ)|=(654963883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s0_7 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4180005279/10000000000 : ℝ)*x 0 + (2750339167/5000000000 : ℝ)*x 1 + (3169732287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180005279/10000000000 : ℝ)^2177 ≤ (15982910439043/50000000000000 : ℝ)^1665 := by
    have hnat : (4180005279 : ℕ)^2177*50000000000000^1665 ≤ 15982910439043^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180005279 10000000000 15982910439043 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2750339167/5000000000 : ℝ)^2177 ≤ (11442799958119/25000000000000 : ℝ)^1665 := by
    have hnat : (2750339167 : ℕ)^2177*25000000000000^1665 ≤ 11442799958119^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750339167 5000000000 11442799958119 25000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3169732287/10000000000 : ℝ)^2177 ≤ (22262979273783/100000000000000 : ℝ)^1665 := by
    have hnat : (3169732287 : ℕ)^2177*100000000000000^1665 ≤ 22262979273783^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3169732287 10000000000 22262979273783 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180005279/10000000000 : ℝ), (2750339167/5000000000 : ℝ), (3169732287/10000000000 : ℝ)] ![(15982910439043/50000000000000 : ℝ), (11442799958119/25000000000000 : ℝ), (22262979273783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180005279/10000000000 : ℝ)|^2177 ≤ (15982910439043/50000000000000 : ℝ)^1665
        have hw : |(4180005279/10000000000 : ℝ)|=(4180005279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2750339167/5000000000 : ℝ)|^2177 ≤ (11442799958119/25000000000000 : ℝ)^1665
        have hw : |(2750339167/5000000000 : ℝ)|=(2750339167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3169732287/10000000000 : ℝ)|^2177 ≤ (22262979273783/100000000000000 : ℝ)^1665
        have hw : |(3169732287/10000000000 : ℝ)|=(3169732287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1394_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156781207/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1797/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13251/50000 : ℝ)*pair X 0 0 := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4353/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4353 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4353*1^1024 ≤ 0^1024*1^4353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4353 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4353/1024 : ℝ) ≤ (63564754139662891/3125000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4353 ≤ (63564754139662891/3125000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4353*3125000000000000000^1024 ≤ 63564754139662891^1024*5^4353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 63564754139662891 3125000000000000000 4353 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (63564754139662891/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4353/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4353 := by
      have hnat : (1 : ℕ)^1024*1^4353 ≤ 1^4353*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3188564754139662891/3125000000000000000 : ℝ) ≤ (5023740874679727/5000000000000000 : ℝ) ^ (4353/1024 : ℝ) := by
    have hpowers : (3188564754139662891/3125000000000000000 : ℝ)^1024 ≤ (5023740874679727/5000000000000000 : ℝ)^4353 := by
      have hnat : (3188564754139662891 : ℕ)^1024*5000000000000000^4353 ≤ 5023740874679727^4353*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3188564754139662891 3125000000000000000 5023740874679727 5000000000000000 1024 4353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5023740874679727/5000000000000000 : ℝ)) (X := (3188564754139662891/3125000000000000000 : ℝ)) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1626064754139662891/1562500000000000000 : ℝ) ≤ (2523740874679727/2500000000000000 : ℝ) ^ (4353/1024 : ℝ) := by
    have hpowers : (1626064754139662891/1562500000000000000 : ℝ)^1024 ≤ (2523740874679727/2500000000000000 : ℝ)^4353 := by
      have hnat : (1626064754139662891 : ℕ)^1024*2500000000000000^4353 ≤ 2523740874679727^4353*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1626064754139662891 1562500000000000000 2523740874679727 2500000000000000 1024 4353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2523740874679727/2500000000000000 : ℝ)) (X := (1626064754139662891/1562500000000000000 : ℝ)) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(23740874679727/2000000000000000 : ℝ)*(0 : ℝ))^(4353/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(23740874679727/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(63564754139662891/3125000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(23740874679727/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4353/1024 : ℝ) := by
    rw [show (1 : ℝ)+(23740874679727/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5023740874679727/5000000000000000 : ℝ) by norm_num, show 1+(63564754139662891/3125000000000000000 : ℝ)+(0 : ℝ)=(3188564754139662891/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(63564754139662891/3125000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(23740874679727/2000000000000000 : ℝ)*(2/5 : ℝ))^(4353/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(23740874679727/2000000000000000 : ℝ)*(2/5 : ℝ)=(2523740874679727/2500000000000000 : ℝ) by norm_num, show 1+2*(63564754139662891/3125000000000000000 : ℝ)=(1626064754139662891/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(23740874679727/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4353/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (23740874679727/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(23740874679727/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4353/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (23740874679727/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(23740874679727/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4353/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (23740874679727/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1778801423/10000000000 : ℝ)*X 0 0+(597475871/1000000000 : ℝ)*X 0 1+(4823163187/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5495998739/10000000000 : ℝ)*X 1 0+(-151933061/625000000 : ℝ)*X 1 1+(2411581679/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5495998747/10000000000 : ℝ)*X 2 0+(964632667/2000000000 : ℝ)*X 2 1+(-1215464497/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1042765827/2500000000 : ℝ)*X 0 0+(3104388007/10000000000 : ℝ)*X 0 1+(2781881477/5000000000 : ℝ)*X 0 2+(1042765827/2500000000 : ℝ)*X 1 0+(3104388007/10000000000 : ℝ)*X 1 1+(2781881477/5000000000 : ℝ)*X 1 2+(1042765827/2500000000 : ℝ)*X 2 0+(3104388007/10000000000 : ℝ)*X 2 1+(2781881477/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-891495891/5000000000 : ℝ)*X 0 0+(970540593/2000000000 : ℝ)*X 0 1+(2972081543/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((518185733/1000000000 : ℝ)*X 1 0+(-327482213/2500000000 : ℝ)*X 1 1+(5944160951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((518185259/1000000000 : ℝ)*X 2 0+(5944166177/10000000000 : ℝ)*X 2 1+(-654963883/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4180005279/10000000000 : ℝ)*X 0 0+(2750339167/5000000000 : ℝ)*X 0 1+(3169732287/10000000000 : ℝ)*X 0 2+(4180005279/10000000000 : ℝ)*X 1 0+(2750339167/5000000000 : ℝ)*X 1 1+(3169732287/10000000000 : ℝ)*X 1 2+(4180005279/10000000000 : ℝ)*X 2 0+(2750339167/5000000000 : ℝ)*X 2 1+(3169732287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50640625799316048287643/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1591771/2500000000000 : ℝ)*(base1) + (471302433/25000000000000 : ℝ)*(base19) + (1886473737/100000000000000 : ℝ)*(base23) + (236353579/100000000000000 : ℝ)*(upper3) + (232022419/100000000000000 : ℝ)*(upper5) + (79686661606799/12500000000000 : ℝ)*(major0) + (79686661606799/12500000000000 : ℝ)*(major1) + (79686661606799/12500000000000 : ℝ)*(major2) + (217091647302041/25000000000000 : ℝ)*(sp0) + (868371096424477/100000000000000 : ℝ)*(sp1) + (108546386895059/12500000000000 : ℝ)*(sp2) + (406610239020953/100000000000000 : ℝ)*(sp3) + (3228048443/50000000000000 : ℝ)*(sp4) + (3031299437/100000000000000 : ℝ)*(sp7) + (40661333399123/10000000000000 : ℝ)*(f.failure) + (86837298163421/10000000000000 : ℝ)*(f.sum) + (6898677876373/12500000000000000000000000000 : ℝ)*base65 + (33816729188873/25000000000000000000000000000 : ℝ)*base67 + (27026169538873/25000000000000000000000000000 : ℝ)*base69 + (108237456913873/25000000000000000000000000000 : ℝ)*base71 + (6133042201373/12500000000000000000000000000 : ℝ)*base73 + (157143546988873/25000000000000000000000000000 : ℝ)*base75 + (136357604888873/25000000000000000000000000000 : ℝ)*base77 + (193563761938873/25000000000000000000000000000 : ℝ)*base79 + (1942925501373/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3318539/1000000000000000000000 : ℝ)*base90 + (3318539/1000000000000000000000 : ℝ)*base92 + (3318539/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45541804262839809414399/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (925379597/50000000000000 : ℝ)*(base19) + (1780004237/100000000000000 : ℝ)*(base23) + (108696181/25000000000000 : ℝ)*(base39) + (88411867/50000000000000 : ℝ)*(upper2) + (4718971/1250000000000 : ℝ)*(upper5) + (134521050598821/20000000000000 : ℝ)*(major0) + (134521050598821/20000000000000 : ℝ)*(major1) + (672604818209381/100000000000000 : ℝ)*(major2) + (247560409/5000000000000 : ℝ)*(sp1) + (994380771/20000000000000 : ℝ)*(sp2) + (57262557356351/6250000000000 : ℝ)*(sp4) + (458097057867121/50000000000000 : ℝ)*(sp5) + (114524325072281/12500000000000 : ℝ)*(sp6) + (429008849889837/100000000000000 : ℝ)*(sp7) + (429008849889837/100000000000000 : ℝ)*(f.failure) + (45810067624317/5000000000000 : ℝ)*(f.sum) + (540544866864161/100000000000000000000000000000 : ℝ)*base65 + (849030597681013/200000000000000000000000000000 : ℝ)*base68 + (123197371001867/40000000000000000000000000000 : ℝ)*base69 + (779719678681013/200000000000000000000000000000 : ℝ)*base72 + (3546078564161/100000000000000000000000000000 : ℝ)*base73 + (210953146761867/40000000000000000000000000000 : ℝ)*base75 + (47694677681867/40000000000000000000000000000 : ℝ)*base77 + (77775303641867/40000000000000000000000000000 : ℝ)*base79 + (33642711181867/20000000000000000000000000000 : ℝ)*base81 + (38106741/10000000000000000000000 : ℝ)*base90 + (38106741/10000000000000000000000 : ℝ)*base92 + (38106741/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1394_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156781207/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1797/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13251/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1394_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1394_s1_0 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-244517509/1250000000 : ℝ)*x 0 + (1123916871/2000000000 : ℝ)*x 1 + (1266176279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (244517509/1250000000 : ℝ)^2177 ≤ (11844046793663/100000000000000 : ℝ)^1665 := by
    have hnat : (244517509 : ℕ)^2177*100000000000000^1665 ≤ 11844046793663^1665*1250000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244517509 1250000000 11844046793663 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123916871/2000000000 : ℝ)^2177 ≤ (23534574993667/50000000000000 : ℝ)^1665 := by
    have hnat : (1123916871 : ℕ)^2177*50000000000000^1665 ≤ 23534574993667^1665*2000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123916871 2000000000 23534574993667 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1266176279/2500000000 : ℝ)^2177 ≤ (2567925199897/6250000000000 : ℝ)^1665 := by
    have hnat : (1266176279 : ℕ)^2177*6250000000000^1665 ≤ 2567925199897^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1266176279 2500000000 2567925199897 6250000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-244517509/1250000000 : ℝ), (1123916871/2000000000 : ℝ), (1266176279/2500000000 : ℝ)] ![(11844046793663/100000000000000 : ℝ), (23534574993667/50000000000000 : ℝ), (2567925199897/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-244517509/1250000000 : ℝ)|^2177 ≤ (11844046793663/100000000000000 : ℝ)^1665
        have hw : |(-244517509/1250000000 : ℝ)|=(244517509/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123916871/2000000000 : ℝ)|^2177 ≤ (23534574993667/50000000000000 : ℝ)^1665
        have hw : |(1123916871/2000000000 : ℝ)|=(1123916871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1266176279/2500000000 : ℝ)|^2177 ≤ (2567925199897/6250000000000 : ℝ)^1665
        have hw : |(1266176279/2500000000 : ℝ)|=(1266176279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s1_1 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5400353521/10000000000 : ℝ)*x 0 + (-45019337/200000000 : ℝ)*x 1 + (2532353253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400353521/10000000000 : ℝ)^2177 ≤ (44682761491043/100000000000000 : ℝ)^1665 := by
    have hnat : (5400353521 : ℕ)^2177*100000000000000^1665 ≤ 44682761491043^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400353521 10000000000 44682761491043 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45019337/200000000 : ℝ)^2177 ≤ (7115210277761/50000000000000 : ℝ)^1665 := by
    have hnat : (45019337 : ℕ)^2177*50000000000000^1665 ≤ 7115210277761^1665*200000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45019337 200000000 7115210277761 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2532353253/5000000000 : ℝ)^2177 ≤ (10271704485519/25000000000000 : ℝ)^1665 := by
    have hnat : (2532353253 : ℕ)^2177*25000000000000^1665 ≤ 10271704485519^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2532353253 5000000000 10271704485519 25000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400353521/10000000000 : ℝ), (-45019337/200000000 : ℝ), (2532353253/5000000000 : ℝ)] ![(44682761491043/100000000000000 : ℝ), (7115210277761/50000000000000 : ℝ), (10271704485519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400353521/10000000000 : ℝ)|^2177 ≤ (44682761491043/100000000000000 : ℝ)^1665
        have hw : |(5400353521/10000000000 : ℝ)|=(5400353521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-45019337/200000000 : ℝ)|^2177 ≤ (7115210277761/50000000000000 : ℝ)^1665
        have hw : |(-45019337/200000000 : ℝ)|=(45019337/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2532353253/5000000000 : ℝ)|^2177 ≤ (10271704485519/25000000000000 : ℝ)^1665
        have hw : |(2532353253/5000000000 : ℝ)|=(2532353253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s1_2 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5400354417/10000000000 : ℝ)*x 0 + (5064705299/10000000000 : ℝ)*x 1 + (-1125483613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400354417/10000000000 : ℝ)^2177 ≤ (44682771184307/100000000000000 : ℝ)^1665 := by
    have hnat : (5400354417 : ℕ)^2177*100000000000000^1665 ≤ 44682771184307^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400354417 10000000000 44682771184307 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5064705299/10000000000 : ℝ)^2177 ≤ (5135850642429/12500000000000 : ℝ)^1665 := by
    have hnat : (5064705299 : ℕ)^2177*12500000000000^1665 ≤ 5135850642429^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5064705299 10000000000 5135850642429 12500000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125483613/5000000000 : ℝ)^2177 ≤ (88940147897/625000000000 : ℝ)^1665 := by
    have hnat : (1125483613 : ℕ)^2177*625000000000^1665 ≤ 88940147897^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125483613 5000000000 88940147897 625000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400354417/10000000000 : ℝ), (5064705299/10000000000 : ℝ), (-1125483613/5000000000 : ℝ)] ![(44682771184307/100000000000000 : ℝ), (5135850642429/12500000000000 : ℝ), (88940147897/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400354417/10000000000 : ℝ)|^2177 ≤ (44682771184307/100000000000000 : ℝ)^1665
        have hw : |(5400354417/10000000000 : ℝ)|=(5400354417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5064705299/10000000000 : ℝ)|^2177 ≤ (5135850642429/12500000000000 : ℝ)^1665
        have hw : |(5064705299/10000000000 : ℝ)|=(5064705299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1125483613/5000000000 : ℝ)|^2177 ≤ (88940147897/625000000000 : ℝ)^1665
        have hw : |(-1125483613/5000000000 : ℝ)|=(1125483613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s1_3 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4282976967/10000000000 : ℝ)*x 0 + (3727608039/10000000000 : ℝ)*x 1 + (1228154447/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4282976967/10000000000 : ℝ)^2177 ≤ (4124913083233/12500000000000 : ℝ)^1665 := by
    have hnat : (4282976967 : ℕ)^2177*12500000000000^1665 ≤ 4124913083233^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4282976967 10000000000 4124913083233 12500000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3727608039/10000000000 : ℝ)^2177 ≤ (27519581229393/100000000000000 : ℝ)^1665 := by
    have hnat : (3727608039 : ℕ)^2177*100000000000000^1665 ≤ 27519581229393^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3727608039 10000000000 27519581229393 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1228154447/2500000000 : ℝ)^2177 ≤ (789622281767/2000000000000 : ℝ)^1665 := by
    have hnat : (1228154447 : ℕ)^2177*2000000000000^1665 ≤ 789622281767^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1228154447 2500000000 789622281767 2000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4282976967/10000000000 : ℝ), (3727608039/10000000000 : ℝ), (1228154447/2500000000 : ℝ)] ![(4124913083233/12500000000000 : ℝ), (27519581229393/100000000000000 : ℝ), (789622281767/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4282976967/10000000000 : ℝ)|^2177 ≤ (4124913083233/12500000000000 : ℝ)^1665
        have hw : |(4282976967/10000000000 : ℝ)|=(4282976967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3727608039/10000000000 : ℝ)|^2177 ≤ (27519581229393/100000000000000 : ℝ)^1665
        have hw : |(3727608039/10000000000 : ℝ)|=(3727608039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1228154447/2500000000 : ℝ)|^2177 ≤ (789622281767/2000000000000 : ℝ)^1665
        have hw : |(1228154447/2500000000 : ℝ)|=(1228154447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s1_4 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-489147269/2500000000 : ℝ)*x 0 + (1014278621/2000000000 : ℝ)*x 1 + (2806389811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (489147269/2500000000 : ℝ)^2177 ≤ (11847601550449/100000000000000 : ℝ)^1665 := by
    have hnat : (489147269 : ℕ)^2177*100000000000000^1665 ≤ 11847601550449^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489147269 2500000000 11847601550449 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1014278621/2000000000 : ℝ)^2177 ≤ (41157757065293/100000000000000 : ℝ)^1665 := by
    have hnat : (1014278621 : ℕ)^2177*100000000000000^1665 ≤ 41157757065293^1665*2000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014278621 2000000000 41157757065293 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2806389811/5000000000 : ℝ)^2177 ≤ (23497320680707/50000000000000 : ℝ)^1665 := by
    have hnat : (2806389811 : ℕ)^2177*50000000000000^1665 ≤ 23497320680707^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2806389811 5000000000 23497320680707 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-489147269/2500000000 : ℝ), (1014278621/2000000000 : ℝ), (2806389811/5000000000 : ℝ)] ![(11847601550449/100000000000000 : ℝ), (41157757065293/100000000000000 : ℝ), (23497320680707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-489147269/2500000000 : ℝ)|^2177 ≤ (11847601550449/100000000000000 : ℝ)^1665
        have hw : |(-489147269/2500000000 : ℝ)|=(489147269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1014278621/2000000000 : ℝ)|^2177 ≤ (41157757065293/100000000000000 : ℝ)^1665
        have hw : |(1014278621/2000000000 : ℝ)|=(1014278621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2806389811/5000000000 : ℝ)|^2177 ≤ (23497320680707/50000000000000 : ℝ)^1665
        have hw : |(2806389811/5000000000 : ℝ)|=(2806389811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s1_5 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (656970509/1250000000 : ℝ)*x 0 + (-1702893613/10000000000 : ℝ)*x 1 + (5612779621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656970509/1250000000 : ℝ)^2177 ≤ (43125018257677/100000000000000 : ℝ)^1665 := by
    have hnat : (656970509 : ℕ)^2177*100000000000000^1665 ≤ 43125018257677^1665*1250000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656970509 1250000000 43125018257677 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1702893613/10000000000 : ℝ)^2177 ≤ (9880340372803/100000000000000 : ℝ)^1665 := by
    have hnat : (1702893613 : ℕ)^2177*100000000000000^1665 ≤ 9880340372803^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1702893613 10000000000 9880340372803 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5612779621/10000000000 : ℝ)^2177 ≤ (23497320675233/50000000000000 : ℝ)^1665 := by
    have hnat : (5612779621 : ℕ)^2177*50000000000000^1665 ≤ 23497320675233^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5612779621 10000000000 23497320675233 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656970509/1250000000 : ℝ), (-1702893613/10000000000 : ℝ), (5612779621/10000000000 : ℝ)] ![(43125018257677/100000000000000 : ℝ), (9880340372803/100000000000000 : ℝ), (23497320675233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656970509/1250000000 : ℝ)|^2177 ≤ (43125018257677/100000000000000 : ℝ)^1665
        have hw : |(656970509/1250000000 : ℝ)|=(656970509/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1702893613/10000000000 : ℝ)|^2177 ≤ (9880340372803/100000000000000 : ℝ)^1665
        have hw : |(-1702893613/10000000000 : ℝ)|=(1702893613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5612779621/10000000000 : ℝ)|^2177 ≤ (23497320675233/50000000000000 : ℝ)^1665
        have hw : |(5612779621/10000000000 : ℝ)|=(5612779621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s1_6 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5255764531/10000000000 : ℝ)*x 0 + (1403195003/2500000000 : ℝ)*x 1 + (-1702892399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255764531/10000000000 : ℝ)^2177 ≤ (43125023182043/100000000000000 : ℝ)^1665 := by
    have hnat : (5255764531 : ℕ)^2177*100000000000000^1665 ≤ 43125023182043^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255764531 10000000000 43125023182043 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1403195003/2500000000 : ℝ)^2177 ≤ (9398929126187/20000000000000 : ℝ)^1665 := by
    have hnat : (1403195003 : ℕ)^2177*20000000000000^1665 ≤ 9398929126187^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403195003 2500000000 9398929126187 20000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1702892399/10000000000 : ℝ)^2177 ≤ (4940165581533/50000000000000 : ℝ)^1665 := by
    have hnat : (1702892399 : ℕ)^2177*50000000000000^1665 ≤ 4940165581533^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1702892399 10000000000 4940165581533 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255764531/10000000000 : ℝ), (1403195003/2500000000 : ℝ), (-1702892399/10000000000 : ℝ)] ![(43125023182043/100000000000000 : ℝ), (9398929126187/20000000000000 : ℝ), (4940165581533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255764531/10000000000 : ℝ)|^2177 ≤ (43125023182043/100000000000000 : ℝ)^1665
        have hw : |(5255764531/10000000000 : ℝ)|=(5255764531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1403195003/2500000000 : ℝ)|^2177 ≤ (9398929126187/20000000000000 : ℝ)^1665
        have hw : |(1403195003/2500000000 : ℝ)|=(1403195003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1702892399/10000000000 : ℝ)|^2177 ≤ (4940165581533/50000000000000 : ℝ)^1665
        have hw : |(-1702892399/10000000000 : ℝ)|=(1702892399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s1_7 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4283937417/10000000000 : ℝ)*x 0 + (2449167531/5000000000 : ℝ)*x 1 + (935534511/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4283937417/10000000000 : ℝ)^2177 ≤ (8252245150399/25000000000000 : ℝ)^1665 := by
    have hnat : (4283937417 : ℕ)^2177*25000000000000^1665 ≤ 8252245150399^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283937417 10000000000 8252245150399 25000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2449167531/5000000000 : ℝ)^2177 ≤ (19665549074129/50000000000000 : ℝ)^1665 := by
    have hnat : (2449167531 : ℕ)^2177*50000000000000^1665 ≤ 19665549074129^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2449167531 5000000000 19665549074129 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (935534511/2500000000 : ℝ)^2177 ≤ (13829960620381/50000000000000 : ℝ)^1665 := by
    have hnat : (935534511 : ℕ)^2177*50000000000000^1665 ≤ 13829960620381^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935534511 2500000000 13829960620381 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4283937417/10000000000 : ℝ), (2449167531/5000000000 : ℝ), (935534511/2500000000 : ℝ)] ![(8252245150399/25000000000000 : ℝ), (19665549074129/50000000000000 : ℝ), (13829960620381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4283937417/10000000000 : ℝ)|^2177 ≤ (8252245150399/25000000000000 : ℝ)^1665
        have hw : |(4283937417/10000000000 : ℝ)|=(4283937417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2449167531/5000000000 : ℝ)|^2177 ≤ (19665549074129/50000000000000 : ℝ)^1665
        have hw : |(2449167531/5000000000 : ℝ)|=(2449167531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(935534511/2500000000 : ℝ)|^2177 ≤ (13829960620381/50000000000000 : ℝ)^1665
        have hw : |(935534511/2500000000 : ℝ)|=(935534511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1394_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156781207/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13251/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1797/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1839/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3817/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13251/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1797/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13251/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1797/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13251/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1797/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13251/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1797/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13251/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1797/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13251/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1797/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1797/100000 : ℝ) ^ (4353/1024 : ℝ) ≤ (152119460379/4000000000000000000 : ℝ) := by
    have hpowers : (1797/100000 : ℝ)^4353 ≤ (152119460379/4000000000000000000 : ℝ)^1024 := by
      have hnat : (1797 : ℕ)^4353*4000000000000000000^1024 ≤ 152119460379^1024*100000^4353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1797 100000 152119460379 4000000000000000000 4353 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1797/100000 : ℝ)) (X := (152119460379/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13251/50000 : ℝ) ^ (4353/1024 : ℝ) ≤ (353485054639317681/100000000000000000000 : ℝ) := by
    have hpowers : (13251/50000 : ℝ)^4353 ≤ (353485054639317681/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13251 : ℕ)^4353*100000000000000000000^1024 ≤ 353485054639317681^1024*50000^4353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13251 50000 353485054639317681 100000000000000000000 4353 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13251/50000 : ℝ)) (X := (353485054639317681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000000152119460379/2000000000000000000 : ℝ) ≤ (5000000089461477/5000000000000000 : ℝ) ^ (4353/1024 : ℝ) := by
    have hpowers : (2000000152119460379/2000000000000000000 : ℝ)^1024 ≤ (5000000089461477/5000000000000000 : ℝ)^4353 := by
      have hnat : (2000000152119460379 : ℕ)^1024*5000000000000000^4353 ≤ 5000000089461477^4353*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000000152119460379 2000000000000000000 5000000089461477 5000000000000000 1024 4353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000089461477/5000000000000000 : ℝ)) (X := (2000000152119460379/2000000000000000000 : ℝ)) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25088372214406456789/25000000000000000000 : ℝ) ≤ (10008304257693931/10000000000000000 : ℝ) ^ (4353/1024 : ℝ) := by
    have hpowers : (25088372214406456789/25000000000000000000 : ℝ)^1024 ≤ (10008304257693931/10000000000000000 : ℝ)^4353 := by
      have hnat : (25088372214406456789 : ℕ)^1024*10000000000000000^4353 ≤ 10008304257693931^4353*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25088372214406456789 25000000000000000000 10008304257693931 10000000000000000 1024 4353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008304257693931/10000000000000000 : ℝ)) (X := (25088372214406456789/25000000000000000000 : ℝ)) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50353485054639317681/50000000000000000000 : ℝ) ≤ (2504152084116227/2500000000000000 : ℝ) ^ (4353/1024 : ℝ) := by
    have hpowers : (50353485054639317681/50000000000000000000 : ℝ)^1024 ≤ (2504152084116227/2500000000000000 : ℝ)^4353 := by
      have hnat : (50353485054639317681 : ℕ)^1024*2500000000000000^4353 ≤ 2504152084116227^4353*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50353485054639317681 50000000000000000000 2504152084116227 2500000000000000 1024 4353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504152084116227/2500000000000000 : ℝ)) (X := (50353485054639317681/50000000000000000000 : ℝ)) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(152119460379/4000000000000000000 : ℝ) ≤ ((643281665523928873/643359375000000000 : ℝ)+2*(8304078770977/2470500000000000 : ℝ)*(1797/100000 : ℝ))^(4353/1024 : ℝ) := by
    rw [show (643281665523928873/643359375000000000 : ℝ)+2*(8304078770977/2470500000000000 : ℝ)*(1797/100000 : ℝ)=(5000000089461477/5000000000000000 : ℝ) by norm_num, show 1+2*(152119460379/4000000000000000000 : ℝ)=(2000000152119460379/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(353485054639317681/100000000000000000000 : ℝ)+(152119460379/4000000000000000000 : ℝ) ≤ ((643281665523928873/643359375000000000 : ℝ)+(8304078770977/2470500000000000 : ℝ)*((13251/50000 : ℝ)+(1797/100000 : ℝ)))^(4353/1024 : ℝ) := by
    rw [show (643281665523928873/643359375000000000 : ℝ)+(8304078770977/2470500000000000 : ℝ)*((13251/50000 : ℝ)+(1797/100000 : ℝ))=(10008304257693931/10000000000000000 : ℝ) by norm_num, show 1+(353485054639317681/100000000000000000000 : ℝ)+(152119460379/4000000000000000000 : ℝ)=(25088372214406456789/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(353485054639317681/100000000000000000000 : ℝ) ≤ ((643281665523928873/643359375000000000 : ℝ)+2*(8304078770977/2470500000000000 : ℝ)*(13251/50000 : ℝ))^(4353/1024 : ℝ) := by
    rw [show (643281665523928873/643359375000000000 : ℝ)+2*(8304078770977/2470500000000000 : ℝ)*(13251/50000 : ℝ)=(2504152084116227/2500000000000000 : ℝ) by norm_num, show 1+2*(353485054639317681/100000000000000000000 : ℝ)=(50353485054639317681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (643281665523928873/643359375000000000 : ℝ)*(X 1 0+X 2 0)+(8304078770977/2470500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4353/1024 : ℝ)) (lo := (1797/100000 : ℝ)) (hi := (13251/50000 : ℝ)) (c := (643281665523928873/643359375000000000 : ℝ)) (alpha := (8304078770977/2470500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (643281665523928873/643359375000000000 : ℝ)*(X 0 1+X 2 1)+(8304078770977/2470500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4353/1024 : ℝ)) (lo := (1797/100000 : ℝ)) (hi := (13251/50000 : ℝ)) (c := (643281665523928873/643359375000000000 : ℝ)) (alpha := (8304078770977/2470500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (643281665523928873/643359375000000000 : ℝ)*(X 0 2+X 1 2)+(8304078770977/2470500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4353/1024 : ℝ)) (lo := (1797/100000 : ℝ)) (hi := (13251/50000 : ℝ)) (c := (643281665523928873/643359375000000000 : ℝ)) (alpha := (8304078770977/2470500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-244517509/1250000000 : ℝ)*X 0 0+(1123916871/2000000000 : ℝ)*X 0 1+(1266176279/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5400353521/10000000000 : ℝ)*X 1 0+(-45019337/200000000 : ℝ)*X 1 1+(2532353253/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5400354417/10000000000 : ℝ)*X 2 0+(5064705299/10000000000 : ℝ)*X 2 1+(-1125483613/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4282976967/10000000000 : ℝ)*X 0 0+(3727608039/10000000000 : ℝ)*X 0 1+(1228154447/2500000000 : ℝ)*X 0 2+(4282976967/10000000000 : ℝ)*X 1 0+(3727608039/10000000000 : ℝ)*X 1 1+(1228154447/2500000000 : ℝ)*X 1 2+(4282976967/10000000000 : ℝ)*X 2 0+(3727608039/10000000000 : ℝ)*X 2 1+(1228154447/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-489147269/2500000000 : ℝ)*X 0 0+(1014278621/2000000000 : ℝ)*X 0 1+(2806389811/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((656970509/1250000000 : ℝ)*X 1 0+(-1702893613/10000000000 : ℝ)*X 1 1+(5612779621/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5255764531/10000000000 : ℝ)*X 2 0+(1403195003/2500000000 : ℝ)*X 2 1+(-1702892399/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4283937417/10000000000 : ℝ)*X 0 0+(2449167531/5000000000 : ℝ)*X 0 1+(935534511/2500000000 : ℝ)*X 0 2+(4283937417/10000000000 : ℝ)*X 1 0+(2449167531/5000000000 : ℝ)*X 1 1+(935534511/2500000000 : ℝ)*X 1 2+(4283937417/10000000000 : ℝ)*X 2 0+(2449167531/5000000000 : ℝ)*X 2 1+(935534511/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (796349616207695180286723689/128671875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (66720609/6250000000000 : ℝ)*(base19) + (338301463/25000000000000 : ℝ)*(base23) + (158631359/100000000000000 : ℝ)*(upper3) + (900413/12500000000000 : ℝ)*(upper4) + (52387117/100000000000000 : ℝ)*(upper5) + (41345312775823/3125000000000 : ℝ)*(major0) + (41345312775823/3125000000000 : ℝ)*(major1) + (41345312775823/3125000000000 : ℝ)*(major2) + (360441097311231/20000000000000 : ℝ)*(sp0) + (901107854129269/50000000000000 : ℝ)*(sp1) + (1802215422582429/100000000000000 : ℝ)*(sp2) + (421939242883549/50000000000000 : ℝ)*(sp3) + (11289232127/100000000000000 : ℝ)*(sp4) + (4549797449/100000000000000 : ℝ)*(sp7) + (843883035564547/100000000000000 : ℝ)*(f.failure) + (901108387894141/50000000000000 : ℝ)*(f.sum) + (132774889126097/123525000000000000000000000000 : ℝ)*base65 + (117303094292327117/96503906250000000000000000000000 : ℝ)*base67 + (901043456127857359/193007812500000000000000000000000 : ℝ)*base69 + (627287212742980343/386015625000000000000000000000000 : ℝ)*base71 + (26766069535159/15440625000000000000000000000 : ℝ)*base73 + (133518620518953629/48251953125000000000000000000000 : ℝ)*base76 + (395174234711233367/96503906250000000000000000000000 : ℝ)*base77 + (48570419100300907/386015625000000000000000000000000 : ℝ)*base80 + (221903947206811/61762500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (5068229/10000000000000000000000 : ℝ)*base89 + (5068229/10000000000000000000000 : ℝ)*base91 + (5068229/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (292835870889387859483202933/64335937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (91937333/50000000000000 : ℝ)*(base1) + (3941489/312500000000 : ℝ)*(base19) + (1519236403/100000000000000 : ℝ)*(base23) + (13925611/12500000000000 : ℝ)*(upper3) + (204574047/100000000000000 : ℝ)*(upper5) + (678003879892129/50000000000000 : ℝ)*(major0) + (678003879892129/50000000000000 : ℝ)*(major1) + (678003879892129/50000000000000 : ℝ)*(major2) + (61771939/1000000000000 : ℝ)*(sp1) + (1938047553/20000000000000 : ℝ)*(sp2) + (461777755708861/25000000000000 : ℝ)*(sp4) + (1847103400490399/100000000000000 : ℝ)*(sp5) + (461774907371653/25000000000000 : ℝ)*(sp6) + (108113043126347/12500000000000 : ℝ)*(sp7) + (864904528885441/100000000000000 : ℝ)*(f.failure) + (1847110838960779/100000000000000 : ℝ)*(f.sum) + (88882370122067/61762500000000000000000000000 : ℝ)*base66 + (973051497663971971/386015625000000000000000000000000 : ℝ)*base68 + (2531799534540715529/386015625000000000000000000000000 : ℝ)*base69 + (1614698438383346971/386015625000000000000000000000000 : ℝ)*base72 + (56575071254441/123525000000000000000000000000 : ℝ)*base73 + (726780443837103173/193007812500000000000000000000000 : ℝ)*base76 + (78651590750565631/24125976562500000000000000000000 : ℝ)*base78 + (2487901434375696923/193007812500000000000000000000000 : ℝ)*base80 + (83525852309677/15440625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (4707287/10000000000000000000000 : ℝ)*base89 + (4707287/10000000000000000000000 : ℝ)*base91 + (4707287/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1394_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156781207/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13251/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1797/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1839/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3817/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1394_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1394_s2_0 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1991968141/10000000000 : ℝ)*x 0 + (27331701/50000000 : ℝ)*x 1 + (5194932199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1991968141/10000000000 : ℝ)^2177 ≤ (3032120596837/25000000000000 : ℝ)^1665 := by
    have hnat : (1991968141 : ℕ)^2177*25000000000000^1665 ≤ 3032120596837^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991968141 10000000000 3032120596837 25000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27331701/50000000 : ℝ)^2177 ≤ (45397967476671/100000000000000 : ℝ)^1665 := by
    have hnat : (27331701 : ℕ)^2177*100000000000000^1665 ≤ 45397967476671^1665*50000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27331701 50000000 45397967476671 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5194932199/10000000000 : ℝ)^2177 ≤ (1327298441501/3125000000000 : ℝ)^1665 := by
    have hnat : (5194932199 : ℕ)^2177*3125000000000^1665 ≤ 1327298441501^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194932199 10000000000 1327298441501 3125000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1991968141/10000000000 : ℝ), (27331701/50000000 : ℝ), (5194932199/10000000000 : ℝ)] ![(3032120596837/25000000000000 : ℝ), (45397967476671/100000000000000 : ℝ), (1327298441501/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1991968141/10000000000 : ℝ)|^2177 ≤ (3032120596837/25000000000000 : ℝ)^1665
        have hw : |(-1991968141/10000000000 : ℝ)|=(1991968141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27331701/50000000 : ℝ)|^2177 ≤ (45397967476671/100000000000000 : ℝ)^1665
        have hw : |(27331701/50000000 : ℝ)|=(27331701/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5194932199/10000000000 : ℝ)|^2177 ≤ (1327298441501/3125000000000 : ℝ)^1665
        have hw : |(5194932199/10000000000 : ℝ)|=(5194932199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s2_1 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (670300807/1250000000 : ℝ)*x 0 + (-2131831829/10000000000 : ℝ)*x 1 + (5194932161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670300807/1250000000 : ℝ)^2177 ≤ (8854536037237/20000000000000 : ℝ)^1665 := by
    have hnat : (670300807 : ℕ)^2177*20000000000000^1665 ≤ 8854536037237^1665*1250000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670300807 1250000000 8854536037237 20000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2131831829/10000000000 : ℝ)^2177 ≤ (6626885040031/50000000000000 : ℝ)^1665 := by
    have hnat : (2131831829 : ℕ)^2177*50000000000000^1665 ≤ 6626885040031^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131831829 10000000000 6626885040031 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5194932161/10000000000 : ℝ)^2177 ≤ (42473549721807/100000000000000 : ℝ)^1665 := by
    have hnat : (5194932161 : ℕ)^2177*100000000000000^1665 ≤ 42473549721807^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194932161 10000000000 42473549721807 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670300807/1250000000 : ℝ), (-2131831829/10000000000 : ℝ), (5194932161/10000000000 : ℝ)] ![(8854536037237/20000000000000 : ℝ), (6626885040031/50000000000000 : ℝ), (42473549721807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670300807/1250000000 : ℝ)|^2177 ≤ (8854536037237/20000000000000 : ℝ)^1665
        have hw : |(670300807/1250000000 : ℝ)|=(670300807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2131831829/10000000000 : ℝ)|^2177 ≤ (6626885040031/50000000000000 : ℝ)^1665
        have hw : |(-2131831829/10000000000 : ℝ)|=(2131831829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5194932161/10000000000 : ℝ)|^2177 ≤ (42473549721807/100000000000000 : ℝ)^1665
        have hw : |(5194932161/10000000000 : ℝ)|=(5194932161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s2_2 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1072481257/2000000000 : ℝ)*x 0 + (5194932349/10000000000 : ℝ)*x 1 + (-2081867/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072481257/2000000000 : ℝ)^2177 ≤ (177090713361/400000000000 : ℝ)^1665 := by
    have hnat : (1072481257 : ℕ)^2177*400000000000^1665 ≤ 177090713361^1665*2000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072481257 2000000000 177090713361 400000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5194932349/10000000000 : ℝ)^2177 ≤ (42473551731551/100000000000000 : ℝ)^1665 := by
    have hnat : (5194932349 : ℕ)^2177*100000000000000^1665 ≤ 42473551731551^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194932349 10000000000 42473551731551 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081867/9765625 : ℝ)^2177 ≤ (2650753981871/20000000000000 : ℝ)^1665 := by
    have hnat : (2081867 : ℕ)^2177*20000000000000^1665 ≤ 2650753981871^1665*9765625^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081867 9765625 2650753981871 20000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072481257/2000000000 : ℝ), (5194932349/10000000000 : ℝ), (-2081867/9765625 : ℝ)] ![(177090713361/400000000000 : ℝ), (42473551731551/100000000000000 : ℝ), (2650753981871/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072481257/2000000000 : ℝ)|^2177 ≤ (177090713361/400000000000 : ℝ)^1665
        have hw : |(1072481257/2000000000 : ℝ)|=(1072481257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5194932349/10000000000 : ℝ)|^2177 ≤ (42473551731551/100000000000000 : ℝ)^1665
        have hw : |(5194932349/10000000000 : ℝ)|=(5194932349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2081867/9765625 : ℝ)|^2177 ≤ (2650753981871/20000000000000 : ℝ)^1665
        have hw : |(-2081867/9765625 : ℝ)|=(2081867/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s2_3 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (215408849/500000000 : ℝ)*x 0 + (1006811789/2500000000 : ℝ)*x 1 + (4606872929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215408849/500000000 : ℝ)^2177 ≤ (33253399702183/100000000000000 : ℝ)^1665 := by
    have hnat : (215408849 : ℕ)^2177*100000000000000^1665 ≤ 33253399702183^1665*500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215408849 500000000 33253399702183 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006811789/2500000000 : ℝ)^2177 ≤ (3044706015417/10000000000000 : ℝ)^1665 := by
    have hnat : (1006811789 : ℕ)^2177*10000000000000^1665 ≤ 3044706015417^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006811789 2500000000 3044706015417 10000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4606872929/10000000000 : ℝ)^2177 ≤ (9074885031883/25000000000000 : ℝ)^1665 := by
    have hnat : (4606872929 : ℕ)^2177*25000000000000^1665 ≤ 9074885031883^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4606872929 10000000000 9074885031883 25000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215408849/500000000 : ℝ), (1006811789/2500000000 : ℝ), (4606872929/10000000000 : ℝ)] ![(33253399702183/100000000000000 : ℝ), (3044706015417/10000000000000 : ℝ), (9074885031883/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215408849/500000000 : ℝ)|^2177 ≤ (33253399702183/100000000000000 : ℝ)^1665
        have hw : |(215408849/500000000 : ℝ)|=(215408849/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1006811789/2500000000 : ℝ)|^2177 ≤ (3044706015417/10000000000000 : ℝ)^1665
        have hw : |(1006811789/2500000000 : ℝ)|=(1006811789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4606872929/10000000000 : ℝ)|^2177 ≤ (9074885031883/25000000000000 : ℝ)^1665
        have hw : |(4606872929/10000000000 : ℝ)|=(4606872929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s2_4 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-996010221/5000000000 : ℝ)*x 0 + (5196541851/10000000000 : ℝ)*x 1 + (1092943413/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (996010221/5000000000 : ℝ)^2177 ≤ (758056172369/6250000000000 : ℝ)^1665 := by
    have hnat : (996010221 : ℕ)^2177*6250000000000^1665 ≤ 758056172369^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996010221 5000000000 758056172369 6250000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5196541851/10000000000 : ℝ)^2177 ≤ (42490758332267/100000000000000 : ℝ)^1665 := by
    have hnat : (5196541851 : ℕ)^2177*100000000000000^1665 ≤ 42490758332267^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196541851 10000000000 42490758332267 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092943413/2000000000 : ℝ)^2177 ≤ (907606857949/2000000000000 : ℝ)^1665 := by
    have hnat : (1092943413 : ℕ)^2177*2000000000000^1665 ≤ 907606857949^1665*2000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092943413 2000000000 907606857949 2000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-996010221/5000000000 : ℝ), (5196541851/10000000000 : ℝ), (1092943413/2000000000 : ℝ)] ![(758056172369/6250000000000 : ℝ), (42490758332267/100000000000000 : ℝ), (907606857949/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-996010221/5000000000 : ℝ)|^2177 ≤ (758056172369/6250000000000 : ℝ)^1665
        have hw : |(-996010221/5000000000 : ℝ)|=(996010221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5196541851/10000000000 : ℝ)|^2177 ≤ (42490758332267/100000000000000 : ℝ)^1665
        have hw : |(5196541851/10000000000 : ℝ)|=(5196541851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1092943413/2000000000 : ℝ)|^2177 ≤ (907606857949/2000000000000 : ℝ)^1665
        have hw : |(1092943413/2000000000 : ℝ)|=(1092943413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s2_5 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2646035301/5000000000 : ℝ)*x 0 + (-1862047549/10000000000 : ℝ)*x 1 + (1366179189/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646035301/5000000000 : ℝ)^2177 ≤ (21757472338237/50000000000000 : ℝ)^1665 := by
    have hnat : (2646035301 : ℕ)^2177*50000000000000^1665 ≤ 21757472338237^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646035301 5000000000 21757472338237 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1862047549/10000000000 : ℝ)^2177 ≤ (11104715771673/100000000000000 : ℝ)^1665 := by
    have hnat : (1862047549 : ℕ)^2177*100000000000000^1665 ≤ 11104715771673^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862047549 10000000000 11104715771673 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1366179189/2500000000 : ℝ)^2177 ≤ (45380339542371/100000000000000 : ℝ)^1665 := by
    have hnat : (1366179189 : ℕ)^2177*100000000000000^1665 ≤ 45380339542371^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366179189 2500000000 45380339542371 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646035301/5000000000 : ℝ), (-1862047549/10000000000 : ℝ), (1366179189/2500000000 : ℝ)] ![(21757472338237/50000000000000 : ℝ), (11104715771673/100000000000000 : ℝ), (45380339542371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646035301/5000000000 : ℝ)|^2177 ≤ (21757472338237/50000000000000 : ℝ)^1665
        have hw : |(2646035301/5000000000 : ℝ)|=(2646035301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1862047549/10000000000 : ℝ)|^2177 ≤ (11104715771673/100000000000000 : ℝ)^1665
        have hw : |(-1862047549/10000000000 : ℝ)|=(1862047549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1366179189/2500000000 : ℝ)|^2177 ≤ (45380339542371/100000000000000 : ℝ)^1665
        have hw : |(1366179189/2500000000 : ℝ)|=(1366179189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s2_6 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5292072027/10000000000 : ℝ)*x 0 + (1366179189/2500000000 : ℝ)*x 1 + (-116377849/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292072027/10000000000 : ℝ)^2177 ≤ (43514959996937/100000000000000 : ℝ)^1665 := by
    have hnat : (5292072027 : ℕ)^2177*100000000000000^1665 ≤ 43514959996937^1665*10000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292072027 10000000000 43514959996937 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366179189/2500000000 : ℝ)^2177 ≤ (45380339542371/100000000000000 : ℝ)^1665 := by
    have hnat : (1366179189 : ℕ)^2177*100000000000000^1665 ≤ 45380339542371^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366179189 2500000000 45380339542371 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (116377849/625000000 : ℝ)^2177 ≤ (5552350224697/50000000000000 : ℝ)^1665 := by
    have hnat : (116377849 : ℕ)^2177*50000000000000^1665 ≤ 5552350224697^1665*625000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116377849 625000000 5552350224697 50000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292072027/10000000000 : ℝ), (1366179189/2500000000 : ℝ), (-116377849/625000000 : ℝ)] ![(43514959996937/100000000000000 : ℝ), (45380339542371/100000000000000 : ℝ), (5552350224697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292072027/10000000000 : ℝ)|^2177 ≤ (43514959996937/100000000000000 : ℝ)^1665
        have hw : |(5292072027/10000000000 : ℝ)|=(5292072027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366179189/2500000000 : ℝ)|^2177 ≤ (45380339542371/100000000000000 : ℝ)^1665
        have hw : |(1366179189/2500000000 : ℝ)|=(1366179189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-116377849/625000000 : ℝ)|^2177 ≤ (5552350224697/50000000000000 : ℝ)^1665
        have hw : |(-116377849/625000000 : ℝ)|=(116377849/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1394_s2_7 (p : ℝ) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1077072513/2500000000 : ℝ)*x 0 + (2301717917/5000000000 : ℝ)*x 1 + (50383913/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077072513/2500000000 : ℝ)^2177 ≤ (6650908170857/20000000000000 : ℝ)^1665 := by
    have hnat : (1077072513 : ℕ)^2177*20000000000000^1665 ≤ 6650908170857^1665*2500000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077072513 2500000000 6650908170857 20000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2301717917/5000000000 : ℝ)^2177 ≤ (3626413380783/10000000000000 : ℝ)^1665 := by
    have hnat : (2301717917 : ℕ)^2177*10000000000000^1665 ≤ 3626413380783^1665*5000000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2301717917 5000000000 3626413380783 10000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50383913/125000000 : ℝ)^2177 ≤ (30481325312867/100000000000000 : ℝ)^1665 := by
    have hnat : (50383913 : ℕ)^2177*100000000000000^1665 ≤ 30481325312867^1665*125000000^2177 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50383913 125000000 30481325312867 100000000000000 2177 1665 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2177/512 : ℝ)) 2177 1665 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077072513/2500000000 : ℝ), (2301717917/5000000000 : ℝ), (50383913/125000000 : ℝ)] ![(6650908170857/20000000000000 : ℝ), (3626413380783/10000000000000 : ℝ), (30481325312867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077072513/2500000000 : ℝ)|^2177 ≤ (6650908170857/20000000000000 : ℝ)^1665
        have hw : |(1077072513/2500000000 : ℝ)|=(1077072513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2301717917/5000000000 : ℝ)|^2177 ≤ (3626413380783/10000000000000 : ℝ)^1665
        have hw : |(2301717917/5000000000 : ℝ)|=(2301717917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(50383913/125000000 : ℝ)|^2177 ≤ (30481325312867/100000000000000 : ℝ)^1665
        have hw : |(50383913/125000000 : ℝ)|=(50383913/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1394_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156781207/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1839/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2543/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15913/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3817/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1839/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3817/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1839/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3817/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1839/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3817/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1839/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3817/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1839/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3817/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1839/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1839/25000 : ℝ) ^ (4353/1024 : ℝ) ≤ (23765149092921/1562500000000000000 : ℝ) := by
    have hpowers : (1839/25000 : ℝ)^4353 ≤ (23765149092921/1562500000000000000 : ℝ)^1024 := by
      have hnat : (1839 : ℕ)^4353*1562500000000000000^1024 ≤ 23765149092921^1024*25000^4353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1839 25000 23765149092921 1562500000000000000 4353 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1839/25000 : ℝ)) (X := (23765149092921/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3817/20000 : ℝ) ^ (4353/1024 : ℝ) ≤ (8754659291768501/10000000000000000000 : ℝ) := by
    have hpowers : (3817/20000 : ℝ)^4353 ≤ (8754659291768501/10000000000000000000 : ℝ)^1024 := by
      have hnat : (3817 : ℕ)^4353*10000000000000000000^1024 ≤ 8754659291768501^1024*20000^4353 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3817 20000 8754659291768501 10000000000000000000 4353 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3817/20000 : ℝ)) (X := (8754659291768501/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (781273765149092921/781250000000000000 : ℝ) ≤ (10000071557762239/10000000000000000 : ℝ) ^ (4353/1024 : ℝ) := by
    have hpowers : (781273765149092921/781250000000000000 : ℝ)^1024 ≤ (10000071557762239/10000000000000000 : ℝ)^4353 := by
      have hnat : (781273765149092921 : ℕ)^1024*10000000000000000^4353 ≤ 10000071557762239^4353*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781273765149092921 781250000000000000 10000071557762239 10000000000000000 1024 4353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000071557762239/10000000000000000 : ℝ)) (X := (781273765149092921/781250000000000000 : ℝ)) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50044533781229815977/50000000000000000000 : ℝ) ≤ (10002094512701119/10000000000000000 : ℝ) ^ (4353/1024 : ℝ) := by
    have hpowers : (50044533781229815977/50000000000000000000 : ℝ)^1024 ≤ (10002094512701119/10000000000000000 : ℝ)^4353 := by
      have hnat : (50044533781229815977 : ℕ)^1024*10000000000000000^4353 ≤ 10002094512701119^4353*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50044533781229815977 50000000000000000000 10002094512701119 10000000000000000 1024 4353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002094512701119/10000000000000000 : ℝ)) (X := (50044533781229815977/50000000000000000000 : ℝ)) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5008754659291768501/5000000000000000000 : ℝ) ≤ (10004117467639999/10000000000000000 : ℝ) ^ (4353/1024 : ℝ) := by
    have hpowers : (5008754659291768501/5000000000000000000 : ℝ)^1024 ≤ (10004117467639999/10000000000000000 : ℝ)^4353 := by
      have hnat : (5008754659291768501 : ℕ)^1024*10000000000000000^4353 ≤ 10004117467639999^4353*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5008754659291768501 5000000000000000000 10004117467639999 10000000000000000 1024 4353 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004117467639999/10000000000000000 : ℝ)) (X := (5008754659291768501/5000000000000000000 : ℝ)) (by norm_num) 4353 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(23765149092921/1562500000000000000 : ℝ) ≤ ((117261077587932498671/117290000000000000000 : ℝ)+2*(790216773/458164062500 : ℝ)*(1839/25000 : ℝ))^(4353/1024 : ℝ) := by
    rw [show (117261077587932498671/117290000000000000000 : ℝ)+2*(790216773/458164062500 : ℝ)*(1839/25000 : ℝ)=(10000071557762239/10000000000000000 : ℝ) by norm_num, show 1+2*(23765149092921/1562500000000000000 : ℝ)=(781273765149092921/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8754659291768501/10000000000000000000 : ℝ)+(23765149092921/1562500000000000000 : ℝ) ≤ ((117261077587932498671/117290000000000000000 : ℝ)+(790216773/458164062500 : ℝ)*((3817/20000 : ℝ)+(1839/25000 : ℝ)))^(4353/1024 : ℝ) := by
    rw [show (117261077587932498671/117290000000000000000 : ℝ)+(790216773/458164062500 : ℝ)*((3817/20000 : ℝ)+(1839/25000 : ℝ))=(10002094512701119/10000000000000000 : ℝ) by norm_num, show 1+(8754659291768501/10000000000000000000 : ℝ)+(23765149092921/1562500000000000000 : ℝ)=(50044533781229815977/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8754659291768501/10000000000000000000 : ℝ) ≤ ((117261077587932498671/117290000000000000000 : ℝ)+2*(790216773/458164062500 : ℝ)*(3817/20000 : ℝ))^(4353/1024 : ℝ) := by
    rw [show (117261077587932498671/117290000000000000000 : ℝ)+2*(790216773/458164062500 : ℝ)*(3817/20000 : ℝ)=(10004117467639999/10000000000000000 : ℝ) by norm_num, show 1+2*(8754659291768501/10000000000000000000 : ℝ)=(5008754659291768501/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (117261077587932498671/117290000000000000000 : ℝ)*(X 1 0+X 2 0)+(790216773/458164062500 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4353/1024 : ℝ)) (lo := (1839/25000 : ℝ)) (hi := (3817/20000 : ℝ)) (c := (117261077587932498671/117290000000000000000 : ℝ)) (alpha := (790216773/458164062500 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (117261077587932498671/117290000000000000000 : ℝ)*(X 0 1+X 2 1)+(790216773/458164062500 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4353/1024 : ℝ)) (lo := (1839/25000 : ℝ)) (hi := (3817/20000 : ℝ)) (c := (117261077587932498671/117290000000000000000 : ℝ)) (alpha := (790216773/458164062500 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (117261077587932498671/117290000000000000000 : ℝ)*(X 0 2+X 1 2)+(790216773/458164062500 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4353/1024 : ℝ)) (lo := (1839/25000 : ℝ)) (hi := (3817/20000 : ℝ)) (c := (117261077587932498671/117290000000000000000 : ℝ)) (alpha := (790216773/458164062500 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1991968141/10000000000 : ℝ)*X 0 0+(27331701/50000000 : ℝ)*X 0 1+(5194932199/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((670300807/1250000000 : ℝ)*X 1 0+(-2131831829/10000000000 : ℝ)*X 1 1+(5194932161/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1072481257/2000000000 : ℝ)*X 2 0+(5194932349/10000000000 : ℝ)*X 2 1+(-2081867/9765625 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((215408849/500000000 : ℝ)*X 0 0+(1006811789/2500000000 : ℝ)*X 0 1+(4606872929/10000000000 : ℝ)*X 0 2+(215408849/500000000 : ℝ)*X 1 0+(1006811789/2500000000 : ℝ)*X 1 1+(4606872929/10000000000 : ℝ)*X 1 2+(215408849/500000000 : ℝ)*X 2 0+(1006811789/2500000000 : ℝ)*X 2 1+(4606872929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-996010221/5000000000 : ℝ)*X 0 0+(5196541851/10000000000 : ℝ)*X 0 1+(1092943413/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646035301/5000000000 : ℝ)*X 1 0+(-1862047549/10000000000 : ℝ)*X 1 1+(1366179189/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5292072027/10000000000 : ℝ)*X 2 0+(1366179189/2500000000 : ℝ)*X 2 1+(-116377849/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1077072513/2500000000 : ℝ)*X 0 0+(2301717917/5000000000 : ℝ)*X 0 1+(50383913/125000000 : ℝ)*X 0 2+(1077072513/2500000000 : ℝ)*X 1 0+(2301717917/5000000000 : ℝ)*X 1 1+(50383913/125000000 : ℝ)*X 1 2+(1077072513/2500000000 : ℝ)*X 2 0+(2301717917/5000000000 : ℝ)*X 2 1+(50383913/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1394_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32882704590967737540949713669/2932250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81977609/4000000000000 : ℝ)*(base19) + (1738172617/100000000000000 : ℝ)*(base23) + (103908741/100000000000000 : ℝ)*(lower2) + (165427167/50000000000000 : ℝ)*(upper3) + (168618851/100000000000000 : ℝ)*(upper5) + (2704907974306487/100000000000000 : ℝ)*(major0) + (2704907974306487/100000000000000 : ℝ)*(major1) + (2704907974306487/100000000000000 : ℝ)*(major2) + (3684516214205007/100000000000000 : ℝ)*(sp0) + (368453788419557/10000000000000 : ℝ)*(sp1) + (1842269097731589/50000000000000 : ℝ)*(sp2) + (1725262395776679/100000000000000 : ℝ)*(sp3) + (5929857697/25000000000000 : ℝ)*(sp4) + (827837209/6250000000000 : ℝ)*(sp7) + (1725275641172023/100000000000000 : ℝ)*(f.failure) + (736907986727159/20000000000000 : ℝ)*(f.sum) + (29943965916687/11729000000000000000000000000 : ℝ)*base65 + (26599929535698178777/11729000000000000000000000000000000 : ℝ)*base67 + (42405878844174178777/11729000000000000000000000000000000 : ℝ)*base69 + (8815145795481821223/11729000000000000000000000000000000 : ℝ)*base72 + (5416851857751/5864500000000000000000000000 : ℝ)*base73 + (55478914841721178777/11729000000000000000000000000000000 : ℝ)*base75 + (117169869087028178777/11729000000000000000000000000000000 : ℝ)*base77 + (74861772069012178777/11729000000000000000000000000000000 : ℝ)*base79 + (28613595857929/11729000000000000000000000000 : ℝ)*base81 + (39428239/10000000000000000000000 : ℝ)*base90 + (39428239/10000000000000000000000 : ℝ)*base92 + (39428239/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85153263108807177449425941/11729000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (260657687/25000000000000 : ℝ)*(base19) + (799732049/25000000000000 : ℝ)*(base23) + (30562327/12500000000000 : ℝ)*(upper3) + (318366157/100000000000000 : ℝ)*(lower4) + (31616697/50000000000000 : ℝ)*(upper5) + (10949905869457/400000000000 : ℝ)*(major0) + (10949905869457/400000000000 : ℝ)*(major1) + (10949905869457/400000000000 : ℝ)*(major2) + (4193746907/100000000000000 : ℝ)*(sp1) + (45623629433/100000000000000 : ℝ)*(sp2) + (116528244975083/3125000000000 : ℝ)*(sp4) + (3728898602825001/100000000000000 : ℝ)*(sp5) + (932213754161257/25000000000000 : ℝ)*(sp6) + (218256106690473/12500000000000 : ℝ)*(sp7) + (218256106690473/12500000000000 : ℝ)*(f.failure) + (116528244975083/3125000000000 : ℝ)*(f.sum) + (161773460027/366531250000000000000000000 : ℝ)*base66 + (152112708198600353/46916000000000000000000000000000 : ℝ)*base68 + (2940278320008353/46916000000000000000000000000000 : ℝ)*base70 + (202247740866799647/46916000000000000000000000000000 : ℝ)*base71 + (18055214832629/2932250000000000000000000000 : ℝ)*base74 + (187435953716996353/46916000000000000000000000000000 : ℝ)*base76 + (136864202040972353/46916000000000000000000000000000 : ℝ)*base78 + (495611065435164353/46916000000000000000000000000000 : ℝ)*base80 + (363423555609/183265625000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (7340911/1250000000000000000000 : ℝ)*base89 + (7340911/1250000000000000000000 : ℝ)*base91 + (7340911/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1394_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156781207/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1839/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2543/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15913/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1394_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1394_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156781207/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2543/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15913/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1394_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1394_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1394_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4353/1024 : ℝ) ≤ p) (hpb : p ≤ (2177/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156781207/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2543/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15913/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1394_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

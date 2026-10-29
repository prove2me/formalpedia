-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1604_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:39:48.512267+00:00
-- url     : https://prove2.me/submissions/882c633d-d304-4560-a7df-613fe2d158d7

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
theorem support_rectangle_w1604_s0_0 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-788462943/5000000000 : ℝ)*x 0 + (1461324943/2500000000 : ℝ)*x 1 + (1222121431/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (788462943/5000000000 : ℝ)^4735 ≤ (189447207023/2000000000000 : ℝ)^3711 := by
    have hnat : (788462943 : ℕ)^4735*2000000000000^3711 ≤ 189447207023^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788462943 5000000000 189447207023 2000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1461324943/2500000000 : ℝ)^4735 ≤ (50403453264303/100000000000000 : ℝ)^3711 := by
    have hnat : (1461324943 : ℕ)^4735*100000000000000^3711 ≤ 50403453264303^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1461324943 2500000000 50403453264303 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1222121431/2500000000 : ℝ)^4735 ≤ (20062093188797/50000000000000 : ℝ)^3711 := by
    have hnat : (1222121431 : ℕ)^4735*50000000000000^3711 ≤ 20062093188797^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1222121431 2500000000 20062093188797 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-788462943/5000000000 : ℝ), (1461324943/2500000000 : ℝ), (1222121431/2500000000 : ℝ)] ![(189447207023/2000000000000 : ℝ), (50403453264303/100000000000000 : ℝ), (20062093188797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-788462943/5000000000 : ℝ)|^4735 ≤ (189447207023/2000000000000 : ℝ)^3711
        have hw : |(-788462943/5000000000 : ℝ)|=(788462943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1461324943/2500000000 : ℝ)|^4735 ≤ (50403453264303/100000000000000 : ℝ)^3711
        have hw : |(1461324943/2500000000 : ℝ)|=(1461324943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1222121431/2500000000 : ℝ)|^4735 ≤ (20062093188797/50000000000000 : ℝ)^3711
        have hw : |(1222121431/2500000000 : ℝ)|=(1222121431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s0_1 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1091239537/2000000000 : ℝ)*x 0 + (-105370207/500000000 : ℝ)*x 1 + (4888485567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091239537/2000000000 : ℝ)^4735 ≤ (46162412359631/100000000000000 : ℝ)^3711 := by
    have hnat : (1091239537 : ℕ)^4735*100000000000000^3711 ≤ 46162412359631^3711*2000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091239537 2000000000 46162412359631 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105370207/500000000 : ℝ)^4735 ≤ (27426805797/200000000000 : ℝ)^3711 := by
    have hnat : (105370207 : ℕ)^4735*200000000000^3711 ≤ 27426805797^3711*500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105370207 500000000 27426805797 200000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4888485567/10000000000 : ℝ)^4735 ≤ (10031046183343/25000000000000 : ℝ)^3711 := by
    have hnat : (4888485567 : ℕ)^4735*25000000000000^3711 ≤ 10031046183343^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4888485567 10000000000 10031046183343 25000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091239537/2000000000 : ℝ), (-105370207/500000000 : ℝ), (4888485567/10000000000 : ℝ)] ![(46162412359631/100000000000000 : ℝ), (27426805797/200000000000 : ℝ), (10031046183343/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091239537/2000000000 : ℝ)|^4735 ≤ (46162412359631/100000000000000 : ℝ)^3711
        have hw : |(1091239537/2000000000 : ℝ)|=(1091239537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-105370207/500000000 : ℝ)|^4735 ≤ (27426805797/200000000000 : ℝ)^3711
        have hw : |(-105370207/500000000 : ℝ)|=(105370207/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4888485567/10000000000 : ℝ)|^4735 ≤ (10031046183343/25000000000000 : ℝ)^3711
        have hw : |(4888485567/10000000000 : ℝ)|=(4888485567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s0_2 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5456197549/10000000000 : ℝ)*x 0 + (4888485633/10000000000 : ℝ)*x 1 + (-1053702117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5456197549/10000000000 : ℝ)^4735 ≤ (9232482178299/20000000000000 : ℝ)^3711 := by
    have hnat : (5456197549 : ℕ)^4735*20000000000000^3711 ≤ 9232482178299^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456197549 10000000000 9232482178299 20000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4888485633/10000000000 : ℝ)^4735 ≤ (40124185424573/100000000000000 : ℝ)^3711 := by
    have hnat : (4888485633 : ℕ)^4735*100000000000000^3711 ≤ 40124185424573^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4888485633 10000000000 40124185424573 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053702117/5000000000 : ℝ)^4735 ≤ (13713403678967/100000000000000 : ℝ)^3711 := by
    have hnat : (1053702117 : ℕ)^4735*100000000000000^3711 ≤ 13713403678967^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053702117 5000000000 13713403678967 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5456197549/10000000000 : ℝ), (4888485633/10000000000 : ℝ), (-1053702117/5000000000 : ℝ)] ![(9232482178299/20000000000000 : ℝ), (40124185424573/100000000000000 : ℝ), (13713403678967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5456197549/10000000000 : ℝ)|^4735 ≤ (9232482178299/20000000000000 : ℝ)^3711
        have hw : |(5456197549/10000000000 : ℝ)|=(5456197549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4888485633/10000000000 : ℝ)|^4735 ≤ (40124185424573/100000000000000 : ℝ)^3711
        have hw : |(4888485633/10000000000 : ℝ)|=(4888485633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1053702117/5000000000 : ℝ)|^4735 ≤ (13713403678967/100000000000000 : ℝ)^3711
        have hw : |(-1053702117/5000000000 : ℝ)|=(1053702117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s0_3 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4112736049/10000000000 : ℝ)*x 0 + (3073355473/10000000000 : ℝ)*x 1 + (1351502447/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4112736049/10000000000 : ℝ)^4735 ≤ (6437029271079/20000000000000 : ℝ)^3711 := by
    have hnat : (4112736049 : ℕ)^4735*20000000000000^3711 ≤ 6437029271079^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4112736049 10000000000 6437029271079 20000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3073355473/10000000000 : ℝ)^4735 ≤ (22193536480233/100000000000000 : ℝ)^3711 := by
    have hnat : (3073355473 : ℕ)^4735*100000000000000^3711 ≤ 22193536480233^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3073355473 10000000000 22193536480233 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351502447/2500000000 : ℝ)^4735 ≤ (45621317145049/100000000000000 : ℝ)^3711 := by
    have hnat : (1351502447 : ℕ)^4735*100000000000000^3711 ≤ 45621317145049^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351502447 2500000000 45621317145049 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4112736049/10000000000 : ℝ), (3073355473/10000000000 : ℝ), (1351502447/2500000000 : ℝ)] ![(6437029271079/20000000000000 : ℝ), (22193536480233/100000000000000 : ℝ), (45621317145049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4112736049/10000000000 : ℝ)|^4735 ≤ (6437029271079/20000000000000 : ℝ)^3711
        have hw : |(4112736049/10000000000 : ℝ)|=(4112736049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3073355473/10000000000 : ℝ)|^4735 ≤ (22193536480233/100000000000000 : ℝ)^3711
        have hw : |(3073355473/10000000000 : ℝ)|=(3073355473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351502447/2500000000 : ℝ)|^4735 ≤ (45621317145049/100000000000000 : ℝ)^3711
        have hw : |(1351502447/2500000000 : ℝ)|=(1351502447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s0_4 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-315960341/2000000000 : ℝ)*x 0 + (4912772589/10000000000 : ℝ)*x 1 + (1455036793/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (315960341/2000000000 : ℝ)^4735 ≤ (4747203604907/50000000000000 : ℝ)^3711 := by
    have hnat : (315960341 : ℕ)^4735*50000000000000^3711 ≤ 4747203604907^3711*2000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315960341 2000000000 4747203604907 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4912772589/10000000000 : ℝ)^4735 ≤ (2018935544233/5000000000000 : ℝ)^3711 := by
    have hnat : (4912772589 : ℕ)^4735*5000000000000^3711 ≤ 2018935544233^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4912772589 10000000000 2018935544233 5000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1455036793/2500000000 : ℝ)^4735 ≤ (25063440941651/50000000000000 : ℝ)^3711 := by
    have hnat : (1455036793 : ℕ)^4735*50000000000000^3711 ≤ 25063440941651^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1455036793 2500000000 25063440941651 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-315960341/2000000000 : ℝ), (4912772589/10000000000 : ℝ), (1455036793/2500000000 : ℝ)] ![(4747203604907/50000000000000 : ℝ), (2018935544233/5000000000000 : ℝ), (25063440941651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-315960341/2000000000 : ℝ)|^4735 ≤ (4747203604907/50000000000000 : ℝ)^3711
        have hw : |(-315960341/2000000000 : ℝ)|=(315960341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4912772589/10000000000 : ℝ)|^4735 ≤ (2018935544233/5000000000000 : ℝ)^3711
        have hw : |(4912772589/10000000000 : ℝ)|=(4912772589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1455036793/2500000000 : ℝ)|^4735 ≤ (25063440941651/50000000000000 : ℝ)^3711
        have hw : |(1455036793/2500000000 : ℝ)|=(1455036793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s0_5 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194866409/10000000000 : ℝ)*x 0 + (-23514837/200000000 : ℝ)*x 1 + (5820147503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194866409/10000000000 : ℝ)^4735 ≤ (21680086266149/50000000000000 : ℝ)^3711 := by
    have hnat : (5194866409 : ℕ)^4735*50000000000000^3711 ≤ 21680086266149^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194866409 10000000000 21680086266149 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23514837/200000000 : ℝ)^4735 ≤ (651294192857/10000000000000 : ℝ)^3711 := by
    have hnat : (23514837 : ℕ)^4735*10000000000000^3711 ≤ 651294192857^3711*200000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23514837 200000000 651294192857 10000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5820147503/10000000000 : ℝ)^4735 ≤ (12531721380181/25000000000000 : ℝ)^3711 := by
    have hnat : (5820147503 : ℕ)^4735*25000000000000^3711 ≤ 12531721380181^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5820147503 10000000000 12531721380181 25000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194866409/10000000000 : ℝ), (-23514837/200000000 : ℝ), (5820147503/10000000000 : ℝ)] ![(21680086266149/50000000000000 : ℝ), (651294192857/10000000000000 : ℝ), (12531721380181/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194866409/10000000000 : ℝ)|^4735 ≤ (21680086266149/50000000000000 : ℝ)^3711
        have hw : |(5194866409/10000000000 : ℝ)|=(5194866409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-23514837/200000000 : ℝ)|^4735 ≤ (651294192857/10000000000000 : ℝ)^3711
        have hw : |(-23514837/200000000 : ℝ)|=(23514837/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5820147503/10000000000 : ℝ)|^4735 ≤ (12531721380181/25000000000000 : ℝ)^3711
        have hw : |(5820147503/10000000000 : ℝ)|=(5820147503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s0_6 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519486653/1000000000 : ℝ)*x 0 + (5820147187/10000000000 : ℝ)*x 1 + (-1175742161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519486653/1000000000 : ℝ)^4735 ≤ (5420021727617/12500000000000 : ℝ)^3711 := by
    have hnat : (519486653 : ℕ)^4735*12500000000000^3711 ≤ 5420021727617^3711*1000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519486653 1000000000 5420021727617 12500000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5820147187/10000000000 : ℝ)^4735 ≤ (50126882048139/100000000000000 : ℝ)^3711 := by
    have hnat : (5820147187 : ℕ)^4735*100000000000000^3711 ≤ 50126882048139^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5820147187 10000000000 50126882048139 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1175742161/10000000000 : ℝ)^4735 ≤ (6512944126707/100000000000000 : ℝ)^3711 := by
    have hnat : (1175742161 : ℕ)^4735*100000000000000^3711 ≤ 6512944126707^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1175742161 10000000000 6512944126707 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519486653/1000000000 : ℝ), (5820147187/10000000000 : ℝ), (-1175742161/10000000000 : ℝ)] ![(5420021727617/12500000000000 : ℝ), (50126882048139/100000000000000 : ℝ), (6512944126707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519486653/1000000000 : ℝ)|^4735 ≤ (5420021727617/12500000000000 : ℝ)^3711
        have hw : |(519486653/1000000000 : ℝ)|=(519486653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5820147187/10000000000 : ℝ)|^4735 ≤ (50126882048139/100000000000000 : ℝ)^3711
        have hw : |(5820147187/10000000000 : ℝ)|=(5820147187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1175742161/10000000000 : ℝ)|^4735 ≤ (6512944126707/100000000000000 : ℝ)^3711
        have hw : |(-1175742161/10000000000 : ℝ)|=(1175742161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s0_7 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4119748539/10000000000 : ℝ)*x 0 + (668350071/1250000000 : ℝ)*x 1 + (3134675101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4119748539/10000000000 : ℝ)^4735 ≤ (32255183437801/100000000000000 : ℝ)^3711 := by
    have hnat : (4119748539 : ℕ)^4735*100000000000000^3711 ≤ 32255183437801^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4119748539 10000000000 32255183437801 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (668350071/1250000000 : ℝ)^4735 ≤ (4498474026829/10000000000000 : ℝ)^3711 := by
    have hnat : (668350071 : ℕ)^4735*10000000000000^3711 ≤ 4498474026829^3711*1250000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668350071 1250000000 4498474026829 10000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3134675101/10000000000 : ℝ)^4735 ≤ (22760076278381/100000000000000 : ℝ)^3711 := by
    have hnat : (3134675101 : ℕ)^4735*100000000000000^3711 ≤ 22760076278381^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3134675101 10000000000 22760076278381 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4119748539/10000000000 : ℝ), (668350071/1250000000 : ℝ), (3134675101/10000000000 : ℝ)] ![(32255183437801/100000000000000 : ℝ), (4498474026829/10000000000000 : ℝ), (22760076278381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4119748539/10000000000 : ℝ)|^4735 ≤ (32255183437801/100000000000000 : ℝ)^3711
        have hw : |(4119748539/10000000000 : ℝ)|=(4119748539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(668350071/1250000000 : ℝ)|^4735 ≤ (4498474026829/10000000000000 : ℝ)^3711
        have hw : |(668350071/1250000000 : ℝ)|=(668350071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3134675101/10000000000 : ℝ)|^4735 ≤ (22760076278381/100000000000000 : ℝ)^3711
        have hw : |(3134675101/10000000000 : ℝ)|=(3134675101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1604_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42974227/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3891/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24381/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4731/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4731 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4731*1^1024 ≤ 0^1024*1^4731 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4731 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4731/1024 : ℝ) ≤ (725171171299181237/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4731 ≤ (725171171299181237/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4731*50000000000000000000^1024 ≤ 725171171299181237^1024*5^4731 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 725171171299181237 50000000000000000000 4731 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (725171171299181237/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4731/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4731 := by
      have hnat : (1 : ℕ)^1024*1^4731 ≤ 1^4731*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4731 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50725171171299181237/50000000000000000000 : ℝ) ≤ (10031215045386047/10000000000000000 : ℝ) ^ (4731/1024 : ℝ) := by
    have hpowers : (50725171171299181237/50000000000000000000 : ℝ)^1024 ≤ (10031215045386047/10000000000000000 : ℝ)^4731 := by
      have hnat : (50725171171299181237 : ℕ)^1024*10000000000000000^4731 ≤ 10031215045386047^4731*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50725171171299181237 50000000000000000000 10031215045386047 10000000000000000 1024 4731 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10031215045386047/10000000000000000 : ℝ)) (X := (50725171171299181237/50000000000000000000 : ℝ)) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25725171171299181237/25000000000000000000 : ℝ) ≤ (5031215045386047/5000000000000000 : ℝ) ^ (4731/1024 : ℝ) := by
    have hpowers : (25725171171299181237/25000000000000000000 : ℝ)^1024 ≤ (5031215045386047/5000000000000000 : ℝ)^4731 := by
      have hnat : (25725171171299181237 : ℕ)^1024*5000000000000000^4731 ≤ 5031215045386047^4731*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25725171171299181237 25000000000000000000 5031215045386047 5000000000000000 1024 4731 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5031215045386047/5000000000000000 : ℝ)) (X := (25725171171299181237/25000000000000000000 : ℝ)) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(31215045386047/4000000000000000 : ℝ)*(0 : ℝ))^(4731/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(31215045386047/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(725171171299181237/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(31215045386047/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4731/1024 : ℝ) := by
    rw [show (1 : ℝ)+(31215045386047/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10031215045386047/10000000000000000 : ℝ) by norm_num, show 1+(725171171299181237/50000000000000000000 : ℝ)+(0 : ℝ)=(50725171171299181237/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(725171171299181237/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(31215045386047/4000000000000000 : ℝ)*(2/5 : ℝ))^(4731/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(31215045386047/4000000000000000 : ℝ)*(2/5 : ℝ)=(5031215045386047/5000000000000000 : ℝ) by norm_num, show 1+2*(725171171299181237/50000000000000000000 : ℝ)=(25725171171299181237/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(31215045386047/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4731/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (31215045386047/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(31215045386047/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4731/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (31215045386047/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(31215045386047/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4731/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (31215045386047/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-788462943/5000000000 : ℝ)*X 0 0+(1461324943/2500000000 : ℝ)*X 0 1+(1222121431/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1091239537/2000000000 : ℝ)*X 1 0+(-105370207/500000000 : ℝ)*X 1 1+(4888485567/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5456197549/10000000000 : ℝ)*X 2 0+(4888485633/10000000000 : ℝ)*X 2 1+(-1053702117/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4112736049/10000000000 : ℝ)*X 0 0+(3073355473/10000000000 : ℝ)*X 0 1+(1351502447/2500000000 : ℝ)*X 0 2+(4112736049/10000000000 : ℝ)*X 1 0+(3073355473/10000000000 : ℝ)*X 1 1+(1351502447/2500000000 : ℝ)*X 1 2+(4112736049/10000000000 : ℝ)*X 2 0+(3073355473/10000000000 : ℝ)*X 2 1+(1351502447/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-315960341/2000000000 : ℝ)*X 0 0+(4912772589/10000000000 : ℝ)*X 0 1+(1455036793/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5194866409/10000000000 : ℝ)*X 1 0+(-23514837/200000000 : ℝ)*X 1 1+(5820147503/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((519486653/1000000000 : ℝ)*X 2 0+(5820147187/10000000000 : ℝ)*X 2 1+(-1175742161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4119748539/10000000000 : ℝ)*X 0 0+(668350071/1250000000 : ℝ)*X 0 1+(3134675101/10000000000 : ℝ)*X 0 2+(4119748539/10000000000 : ℝ)*X 1 0+(668350071/1250000000 : ℝ)*X 1 1+(3134675101/10000000000 : ℝ)*X 1 2+(4119748539/10000000000 : ℝ)*X 2 0+(668350071/1250000000 : ℝ)*X 2 1+(3134675101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (360196800533599940811237/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7978233/50000000000000 : ℝ)*(base1) + (689731029/100000000000000 : ℝ)*(base19) + (663680111/100000000000000 : ℝ)*(base23) + (106979139/100000000000000 : ℝ)*(upper3) + (70758579/100000000000000 : ℝ)*(upper5) + (368459651763581/50000000000000 : ℝ)*(major0) + (368459651763581/50000000000000 : ℝ)*(major1) + (368459651763581/50000000000000 : ℝ)*(major2) + (261284430369991/25000000000000 : ℝ)*(sp0) + (1045139391858123/100000000000000 : ℝ)*(sp1) + (1045139417909041/100000000000000 : ℝ)*(sp2) + (107174302680343/25000000000000 : ℝ)*(sp3) + (475213131/20000000000000 : ℝ)*(sp4) + (1178721729/100000000000000 : ℝ)*(sp7) + (26793650337473/6250000000000 : ℝ)*(f.failure) + (32660627549661/3125000000000 : ℝ)*(f.sum) + (210305192154307/100000000000000000000000000000 : ℝ)*base65 + (679641486045693/200000000000000000000000000000 : ℝ)*base68 + (562013552045693/200000000000000000000000000000 : ℝ)*base70 + (170362837354307/200000000000000000000000000000 : ℝ)*base71 + (19202339354307/100000000000000000000000000000 : ℝ)*base73 + (38666618954307/200000000000000000000000000000 : ℝ)*base75 + (640743786554307/200000000000000000000000000000 : ℝ)*base77 + (121483276045693/200000000000000000000000000000 : ℝ)*base80 + (48812603054307/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (683371/156250000000000000000 : ℝ)*base89 + (683371/156250000000000000000 : ℝ)*base91 + (683371/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (133664463855958639279233/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2238147/200000000000 : ℝ)*(base19) + (232946703/20000000000000 : ℝ)*(base23) + (198688351/100000000000000 : ℝ)*(base32) + (224378109/100000000000000 : ℝ)*(upper3) + (3320033/12500000000000 : ℝ)*(upper5) + (388533271037413/50000000000000 : ℝ)*(major0) + (388533271037413/50000000000000 : ℝ)*(major1) + (388533271037413/50000000000000 : ℝ)*(major2) + (750961573/25000000000000 : ℝ)*(sp1) + (8503059/250000000000 : ℝ)*(sp2) + (1102079084185747/100000000000000 : ℝ)*(sp4) + (220414992253191/20000000000000 : ℝ)*(sp5) + (1102074518228633/100000000000000 : ℝ)*(sp6) + (90410724611253/20000000000000 : ℝ)*(sp7) + (56506727718077/12500000000000 : ℝ)*(f.failure) + (1102079084185747/100000000000000 : ℝ)*(f.sum) + (132962054823589/100000000000000000000000000000 : ℝ)*base66 + (21646735423589/200000000000000000000000000000 : ℝ)*base68 + (401300284623589/200000000000000000000000000000 : ℝ)*base70 + (792754524823589/200000000000000000000000000000 : ℝ)*base72 + (16816523823589/100000000000000000000000000000 : ℝ)*base74 + (64474373623589/200000000000000000000000000000 : ℝ)*base76 + (818608579823589/200000000000000000000000000000 : ℝ)*base78 + (2132097773023589/200000000000000000000000000000 : ℝ)*base80 + (33028819976411/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1751479/312500000000000000000 : ℝ)*base89 + (1751479/312500000000000000000 : ℝ)*base91 + (1751479/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1604_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42974227/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3891/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24381/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1604_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1604_s1_0 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1703134813/10000000000 : ℝ)*x 0 + (2767811473/5000000000 : ℝ)*x 1 + (1279148391/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1703134813/10000000000 : ℝ)^4735 ≤ (2612538232117/25000000000000 : ℝ)^3711 := by
    have hnat : (1703134813 : ℕ)^4735*25000000000000^3711 ≤ 2612538232117^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1703134813 10000000000 2612538232117 25000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2767811473/5000000000 : ℝ)^4735 ≤ (23510766740747/50000000000000 : ℝ)^3711 := by
    have hnat : (2767811473 : ℕ)^4735*50000000000000^3711 ≤ 23510766740747^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2767811473 5000000000 23510766740747 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1279148391/2500000000 : ℝ)^4735 ≤ (5316039196859/12500000000000 : ℝ)^3711 := by
    have hnat : (1279148391 : ℕ)^4735*12500000000000^3711 ≤ 5316039196859^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279148391 2500000000 5316039196859 12500000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1703134813/10000000000 : ℝ), (2767811473/5000000000 : ℝ), (1279148391/2500000000 : ℝ)] ![(2612538232117/25000000000000 : ℝ), (23510766740747/50000000000000 : ℝ), (5316039196859/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1703134813/10000000000 : ℝ)|^4735 ≤ (2612538232117/25000000000000 : ℝ)^3711
        have hw : |(-1703134813/10000000000 : ℝ)|=(1703134813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2767811473/5000000000 : ℝ)|^4735 ≤ (23510766740747/50000000000000 : ℝ)^3711
        have hw : |(2767811473/5000000000 : ℝ)|=(2767811473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1279148391/2500000000 : ℝ)|^4735 ≤ (5316039196859/12500000000000 : ℝ)^3711
        have hw : |(1279148391/2500000000 : ℝ)|=(1279148391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s1_1 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2686885161/5000000000 : ℝ)*x 0 + (-1922507333/10000000000 : ℝ)*x 1 + (5116593423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686885161/5000000000 : ℝ)^4735 ≤ (45274460624159/100000000000000 : ℝ)^3711 := by
    have hnat : (2686885161 : ℕ)^4735*100000000000000^3711 ≤ 45274460624159^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686885161 5000000000 45274460624159 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1922507333/10000000000 : ℝ)^4735 ≤ (6098613642391/50000000000000 : ℝ)^3711 := by
    have hnat : (1922507333 : ℕ)^4735*50000000000000^3711 ≤ 6098613642391^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922507333 10000000000 6098613642391 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5116593423/10000000000 : ℝ)^4735 ≤ (42528312079513/100000000000000 : ℝ)^3711 := by
    have hnat : (5116593423 : ℕ)^4735*100000000000000^3711 ≤ 42528312079513^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5116593423 10000000000 42528312079513 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686885161/5000000000 : ℝ), (-1922507333/10000000000 : ℝ), (5116593423/10000000000 : ℝ)] ![(45274460624159/100000000000000 : ℝ), (6098613642391/50000000000000 : ℝ), (42528312079513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686885161/5000000000 : ℝ)|^4735 ≤ (45274460624159/100000000000000 : ℝ)^3711
        have hw : |(2686885161/5000000000 : ℝ)|=(2686885161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1922507333/10000000000 : ℝ)|^4735 ≤ (6098613642391/50000000000000 : ℝ)^3711
        have hw : |(-1922507333/10000000000 : ℝ)|=(1922507333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5116593423/10000000000 : ℝ)|^4735 ≤ (42528312079513/100000000000000 : ℝ)^3711
        have hw : |(5116593423/10000000000 : ℝ)|=(5116593423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s1_2 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343442487/2500000000 : ℝ)*x 0 + (2558296873/5000000000 : ℝ)*x 1 + (-1922507407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343442487/2500000000 : ℝ)^4735 ≤ (11318614150927/25000000000000 : ℝ)^3711 := by
    have hnat : (1343442487 : ℕ)^4735*25000000000000^3711 ≤ 11318614150927^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343442487 2500000000 11318614150927 25000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2558296873/5000000000 : ℝ)^4735 ≤ (42528315505051/100000000000000 : ℝ)^3711 := by
    have hnat : (2558296873 : ℕ)^4735*100000000000000^3711 ≤ 42528315505051^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2558296873 5000000000 42528315505051 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1922507407/10000000000 : ℝ)^4735 ≤ (12197227883819/100000000000000 : ℝ)^3711 := by
    have hnat : (1922507407 : ℕ)^4735*100000000000000^3711 ≤ 12197227883819^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922507407 10000000000 12197227883819 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343442487/2500000000 : ℝ), (2558296873/5000000000 : ℝ), (-1922507407/10000000000 : ℝ)] ![(11318614150927/25000000000000 : ℝ), (42528315505051/100000000000000 : ℝ), (12197227883819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343442487/2500000000 : ℝ)|^4735 ≤ (11318614150927/25000000000000 : ℝ)^3711
        have hw : |(1343442487/2500000000 : ℝ)|=(1343442487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2558296873/5000000000 : ℝ)|^4735 ≤ (42528315505051/100000000000000 : ℝ)^3711
        have hw : |(2558296873/5000000000 : ℝ)|=(2558296873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1922507407/10000000000 : ℝ)|^4735 ≤ (12197227883819/100000000000000 : ℝ)^3711
        have hw : |(-1922507407/10000000000 : ℝ)|=(1922507407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s1_3 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4205577739/10000000000 : ℝ)*x 0 + (929706829/2500000000 : ℝ)*x 1 + (1185098783/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4205577739/10000000000 : ℝ)^4735 ≤ (4139381787407/12500000000000 : ℝ)^3711 := by
    have hnat : (4205577739 : ℕ)^4735*12500000000000^3711 ≤ 4139381787407^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205577739 10000000000 4139381787407 12500000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (929706829/2500000000 : ℝ)^4735 ≤ (14152572748981/50000000000000 : ℝ)^3711 := by
    have hnat : (929706829 : ℕ)^4735*50000000000000^3711 ≤ 14152572748981^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929706829 2500000000 14152572748981 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1185098783/2500000000 : ℝ)^4735 ≤ (3857980018129/10000000000000 : ℝ)^3711 := by
    have hnat : (1185098783 : ℕ)^4735*10000000000000^3711 ≤ 3857980018129^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1185098783 2500000000 3857980018129 10000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4205577739/10000000000 : ℝ), (929706829/2500000000 : ℝ), (1185098783/2500000000 : ℝ)] ![(4139381787407/12500000000000 : ℝ), (14152572748981/50000000000000 : ℝ), (3857980018129/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4205577739/10000000000 : ℝ)|^4735 ≤ (4139381787407/12500000000000 : ℝ)^3711
        have hw : |(4205577739/10000000000 : ℝ)|=(4205577739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(929706829/2500000000 : ℝ)|^4735 ≤ (14152572748981/50000000000000 : ℝ)^3711
        have hw : |(929706829/2500000000 : ℝ)|=(929706829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1185098783/2500000000 : ℝ)|^4735 ≤ (3857980018129/10000000000000 : ℝ)^3711
        have hw : |(1185098783/2500000000 : ℝ)|=(1185098783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s1_4 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-170337063/1000000000 : ℝ)*x 0 + (1280301623/2500000000 : ℝ)*x 1 + (69136721/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170337063/1000000000 : ℝ)^4735 ≤ (2090399831907/20000000000000 : ℝ)^3711 := by
    have hnat : (170337063 : ℕ)^4735*20000000000000^3711 ≤ 2090399831907^3711*1000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170337063 1000000000 2090399831907 20000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1280301623/2500000000 : ℝ)^4735 ≤ (5322155189649/12500000000000 : ℝ)^3711 := by
    have hnat : (1280301623 : ℕ)^4735*12500000000000^3711 ≤ 5322155189649^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280301623 2500000000 5322155189649 12500000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69136721/125000000 : ℝ)^4735 ≤ (23485379655253/50000000000000 : ℝ)^3711 := by
    have hnat : (69136721 : ℕ)^4735*50000000000000^3711 ≤ 23485379655253^3711*125000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69136721 125000000 23485379655253 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-170337063/1000000000 : ℝ), (1280301623/2500000000 : ℝ), (69136721/125000000 : ℝ)] ![(2090399831907/20000000000000 : ℝ), (5322155189649/12500000000000 : ℝ), (23485379655253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-170337063/1000000000 : ℝ)|^4735 ≤ (2090399831907/20000000000000 : ℝ)^3711
        have hw : |(-170337063/1000000000 : ℝ)|=(170337063/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1280301623/2500000000 : ℝ)|^4735 ≤ (5322155189649/12500000000000 : ℝ)^3711
        have hw : |(1280301623/2500000000 : ℝ)|=(1280301623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(69136721/125000000 : ℝ)|^4735 ≤ (23485379655253/50000000000000 : ℝ)^3711
        have hw : |(69136721/125000000 : ℝ)|=(69136721/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s1_5 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5262401101/10000000000 : ℝ)*x 0 + (-377040731/2500000000 : ℝ)*x 1 + (1382734497/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5262401101/10000000000 : ℝ)^4735 ≤ (11020174114991/25000000000000 : ℝ)^3711 := by
    have hnat : (5262401101 : ℕ)^4735*25000000000000^3711 ≤ 11020174114991^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262401101 10000000000 11020174114991 25000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (377040731/2500000000 : ℝ)^4735 ≤ (8948540875381/100000000000000 : ℝ)^3711 := by
    have hnat : (377040731 : ℕ)^4735*100000000000000^3711 ≤ 8948540875381^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377040731 2500000000 8948540875381 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1382734497/2500000000 : ℝ)^4735 ≤ (11742690661977/25000000000000 : ℝ)^3711 := by
    have hnat : (1382734497 : ℕ)^4735*25000000000000^3711 ≤ 11742690661977^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382734497 2500000000 11742690661977 25000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5262401101/10000000000 : ℝ), (-377040731/2500000000 : ℝ), (1382734497/2500000000 : ℝ)] ![(11020174114991/25000000000000 : ℝ), (8948540875381/100000000000000 : ℝ), (11742690661977/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5262401101/10000000000 : ℝ)|^4735 ≤ (11020174114991/25000000000000 : ℝ)^3711
        have hw : |(5262401101/10000000000 : ℝ)|=(5262401101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-377040731/2500000000 : ℝ)|^4735 ≤ (8948540875381/100000000000000 : ℝ)^3711
        have hw : |(-377040731/2500000000 : ℝ)|=(377040731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1382734497/2500000000 : ℝ)|^4735 ≤ (11742690661977/25000000000000 : ℝ)^3711
        have hw : |(1382734497/2500000000 : ℝ)|=(1382734497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s1_6 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5262400503/10000000000 : ℝ)*x 0 + (1382734553/2500000000 : ℝ)*x 1 + (-188520431/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5262400503/10000000000 : ℝ)^4735 ≤ (44080690068583/100000000000000 : ℝ)^3711 := by
    have hnat : (5262400503 : ℕ)^4735*100000000000000^3711 ≤ 44080690068583^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262400503 10000000000 44080690068583 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1382734553/2500000000 : ℝ)^4735 ≤ (4697076507511/10000000000000 : ℝ)^3711 := by
    have hnat : (1382734553 : ℕ)^4735*10000000000000^3711 ≤ 4697076507511^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382734553 2500000000 4697076507511 10000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188520431/1250000000 : ℝ)^4735 ≤ (11185681053/125000000000 : ℝ)^3711 := by
    have hnat : (188520431 : ℕ)^4735*125000000000^3711 ≤ 11185681053^3711*1250000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188520431 1250000000 11185681053 125000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5262400503/10000000000 : ℝ), (1382734553/2500000000 : ℝ), (-188520431/1250000000 : ℝ)] ![(44080690068583/100000000000000 : ℝ), (4697076507511/10000000000000 : ℝ), (11185681053/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5262400503/10000000000 : ℝ)|^4735 ≤ (44080690068583/100000000000000 : ℝ)^3711
        have hw : |(5262400503/10000000000 : ℝ)|=(5262400503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1382734553/2500000000 : ℝ)|^4735 ≤ (4697076507511/10000000000000 : ℝ)^3711
        have hw : |(1382734553/2500000000 : ℝ)|=(1382734553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-188520431/1250000000 : ℝ)|^4735 ≤ (11185681053/125000000000 : ℝ)^3711
        have hw : |(-188520431/1250000000 : ℝ)|=(188520431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s1_7 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (841230339/2000000000 : ℝ)*x 0 + (4729150139/10000000000 : ℝ)*x 1 + (1865124329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (841230339/2000000000 : ℝ)^4735 ≤ (33120820843289/100000000000000 : ℝ)^3711 := by
    have hnat : (841230339 : ℕ)^4735*100000000000000^3711 ≤ 33120820843289^3711*2000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841230339 2000000000 33120820843289 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4729150139/10000000000 : ℝ)^4735 ≤ (19231533891689/50000000000000 : ℝ)^3711 := by
    have hnat : (4729150139 : ℕ)^4735*50000000000000^3711 ≤ 19231533891689^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4729150139 10000000000 19231533891689 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1865124329/5000000000 : ℝ)^4735 ≤ (14208055680261/50000000000000 : ℝ)^3711 := by
    have hnat : (1865124329 : ℕ)^4735*50000000000000^3711 ≤ 14208055680261^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1865124329 5000000000 14208055680261 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(841230339/2000000000 : ℝ), (4729150139/10000000000 : ℝ), (1865124329/5000000000 : ℝ)] ![(33120820843289/100000000000000 : ℝ), (19231533891689/50000000000000 : ℝ), (14208055680261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(841230339/2000000000 : ℝ)|^4735 ≤ (33120820843289/100000000000000 : ℝ)^3711
        have hw : |(841230339/2000000000 : ℝ)|=(841230339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4729150139/10000000000 : ℝ)|^4735 ≤ (19231533891689/50000000000000 : ℝ)^3711
        have hw : |(4729150139/10000000000 : ℝ)|=(4729150139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1865124329/5000000000 : ℝ)|^4735 ≤ (14208055680261/50000000000000 : ℝ)^3711
        have hw : |(1865124329/5000000000 : ℝ)|=(1865124329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1604_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42974227/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24381/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3891/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9021/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8949/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24381/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3891/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24381/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3891/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24381/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3891/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24381/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3891/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24381/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3891/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24381/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3891/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3891/100000 : ℝ) ^ (4731/1024 : ℝ) ≤ (956682171861/3125000000000000000 : ℝ) := by
    have hpowers : (3891/100000 : ℝ)^4731 ≤ (956682171861/3125000000000000000 : ℝ)^1024 := by
      have hnat : (3891 : ℕ)^4731*3125000000000000000^1024 ≤ 956682171861^1024*100000^4731 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3891 100000 956682171861 3125000000000000000 4731 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3891/100000 : ℝ)) (X := (956682171861/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24381/100000 : ℝ) ^ (4731/1024 : ℝ) ≤ (147267246568284993/100000000000000000000 : ℝ) := by
    have hpowers : (24381/100000 : ℝ)^4731 ≤ (147267246568284993/100000000000000000000 : ℝ)^1024 := by
      have hnat : (24381 : ℕ)^4731*100000000000000000000^1024 ≤ 147267246568284993^1024*100000^4731 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24381 100000 147267246568284993 100000000000000000000 4731 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24381/100000 : ℝ)) (X := (147267246568284993/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562500956682171861/1562500000000000000 : ℝ) ≤ (1250000165655009/1250000000000000 : ℝ) ^ (4731/1024 : ℝ) := by
    have hpowers : (1562500956682171861/1562500000000000000 : ℝ)^1024 ≤ (1250000165655009/1250000000000000 : ℝ)^4731 := by
      have hnat : (1562500956682171861 : ℕ)^1024*1250000000000000^4731 ≤ 1250000165655009^4731*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562500956682171861 1562500000000000000 1250000165655009 1250000000000000 1024 4731 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000165655009/1250000000000000 : ℝ)) (X := (1562500956682171861/1562500000000000000 : ℝ)) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20029459572079556909/20000000000000000000 : ℝ) ≤ (1250398293284901/1250000000000000 : ℝ) ^ (4731/1024 : ℝ) := by
    have hpowers : (20029459572079556909/20000000000000000000 : ℝ)^1024 ≤ (1250398293284901/1250000000000000 : ℝ)^4731 := by
      have hnat : (20029459572079556909 : ℕ)^1024*1250000000000000^4731 ≤ 1250398293284901^4731*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20029459572079556909 20000000000000000000 1250398293284901 1250000000000000 1024 4731 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250398293284901/1250000000000000 : ℝ)) (X := (20029459572079556909/20000000000000000000 : ℝ)) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50147267246568284993/50000000000000000000 : ℝ) ≤ (1250796420914793/1250000000000000 : ℝ) ^ (4731/1024 : ℝ) := by
    have hpowers : (50147267246568284993/50000000000000000000 : ℝ)^1024 ≤ (1250796420914793/1250000000000000 : ℝ)^4731 := by
      have hnat : (50147267246568284993 : ℕ)^1024*1250000000000000^4731 ≤ 1250796420914793^4731*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50147267246568284993 50000000000000000000 1250796420914793 1250000000000000 1024 4731 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250796420914793/1250000000000000 : ℝ)) (X := (50147267246568284993/50000000000000000000 : ℝ)) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(956682171861/3125000000000000000 : ℝ) ≤ ((4268234194175885811/4268750000000000000 : ℝ)+2*(33177302491/21343750000000 : ℝ)*(3891/100000 : ℝ))^(4731/1024 : ℝ) := by
    rw [show (4268234194175885811/4268750000000000000 : ℝ)+2*(33177302491/21343750000000 : ℝ)*(3891/100000 : ℝ)=(1250000165655009/1250000000000000 : ℝ) by norm_num, show 1+2*(956682171861/3125000000000000000 : ℝ)=(1562500956682171861/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(147267246568284993/100000000000000000000 : ℝ)+(956682171861/3125000000000000000 : ℝ) ≤ ((4268234194175885811/4268750000000000000 : ℝ)+(33177302491/21343750000000 : ℝ)*((24381/100000 : ℝ)+(3891/100000 : ℝ)))^(4731/1024 : ℝ) := by
    rw [show (4268234194175885811/4268750000000000000 : ℝ)+(33177302491/21343750000000 : ℝ)*((24381/100000 : ℝ)+(3891/100000 : ℝ))=(1250398293284901/1250000000000000 : ℝ) by norm_num, show 1+(147267246568284993/100000000000000000000 : ℝ)+(956682171861/3125000000000000000 : ℝ)=(20029459572079556909/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(147267246568284993/100000000000000000000 : ℝ) ≤ ((4268234194175885811/4268750000000000000 : ℝ)+2*(33177302491/21343750000000 : ℝ)*(24381/100000 : ℝ))^(4731/1024 : ℝ) := by
    rw [show (4268234194175885811/4268750000000000000 : ℝ)+2*(33177302491/21343750000000 : ℝ)*(24381/100000 : ℝ)=(1250796420914793/1250000000000000 : ℝ) by norm_num, show 1+2*(147267246568284993/100000000000000000000 : ℝ)=(50147267246568284993/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4268234194175885811/4268750000000000000 : ℝ)*(X 1 0+X 2 0)+(33177302491/21343750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4731/1024 : ℝ)) (lo := (3891/100000 : ℝ)) (hi := (24381/100000 : ℝ)) (c := (4268234194175885811/4268750000000000000 : ℝ)) (alpha := (33177302491/21343750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4268234194175885811/4268750000000000000 : ℝ)*(X 0 1+X 2 1)+(33177302491/21343750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4731/1024 : ℝ)) (lo := (3891/100000 : ℝ)) (hi := (24381/100000 : ℝ)) (c := (4268234194175885811/4268750000000000000 : ℝ)) (alpha := (33177302491/21343750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4268234194175885811/4268750000000000000 : ℝ)*(X 0 2+X 1 2)+(33177302491/21343750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4731/1024 : ℝ)) (lo := (3891/100000 : ℝ)) (hi := (24381/100000 : ℝ)) (c := (4268234194175885811/4268750000000000000 : ℝ)) (alpha := (33177302491/21343750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1703134813/10000000000 : ℝ)*X 0 0+(2767811473/5000000000 : ℝ)*X 0 1+(1279148391/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2686885161/5000000000 : ℝ)*X 1 0+(-1922507333/10000000000 : ℝ)*X 1 1+(5116593423/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1343442487/2500000000 : ℝ)*X 2 0+(2558296873/5000000000 : ℝ)*X 2 1+(-1922507407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4205577739/10000000000 : ℝ)*X 0 0+(929706829/2500000000 : ℝ)*X 0 1+(1185098783/2500000000 : ℝ)*X 0 2+(4205577739/10000000000 : ℝ)*X 1 0+(929706829/2500000000 : ℝ)*X 1 1+(1185098783/2500000000 : ℝ)*X 1 2+(4205577739/10000000000 : ℝ)*X 2 0+(929706829/2500000000 : ℝ)*X 2 1+(1185098783/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-170337063/1000000000 : ℝ)*X 0 0+(1280301623/2500000000 : ℝ)*X 0 1+(69136721/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5262401101/10000000000 : ℝ)*X 1 0+(-377040731/2500000000 : ℝ)*X 1 1+(1382734497/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5262400503/10000000000 : ℝ)*X 2 0+(1382734553/2500000000 : ℝ)*X 2 1+(-188520431/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((841230339/2000000000 : ℝ)*X 0 0+(4729150139/10000000000 : ℝ)*X 0 1+(1865124329/5000000000 : ℝ)*X 0 2+(841230339/2000000000 : ℝ)*X 1 0+(4729150139/10000000000 : ℝ)*X 1 1+(1865124329/5000000000 : ℝ)*X 1 2+(841230339/2000000000 : ℝ)*X 2 0+(4729150139/10000000000 : ℝ)*X 2 1+(1865124329/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62179569233356040877640929/10671875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20045601/25000000000000 : ℝ)*(base1) + (1354920289/100000000000000 : ℝ)*(base19) + (594413569/50000000000000 : ℝ)*(base23) + (167810283/100000000000000 : ℝ)*(upper3) + (96904793/100000000000000 : ℝ)*(upper5) + (84134643719871/5000000000000 : ℝ)*(major0) + (84134643719871/5000000000000 : ℝ)*(major1) + (84134643719871/5000000000000 : ℝ)*(major2) + (2386478984165527/100000000000000 : ℝ)*(sp0) + (1193243832848817/50000000000000 : ℝ)*(sp1) + (477297566358157/20000000000000 : ℝ)*(sp2) + (15295184972789/1562500000000 : ℝ)*(sp3) + (10116634801/100000000000000 : ℝ)*(sp4) + (576939961/12500000000000 : ℝ)*(sp7) + (244724133490147/25000000000000 : ℝ)*(f.failure) + (596622255154481/25000000000000 : ℝ)*(f.sum) + (3125403288241/3415000000000000000000000000 : ℝ)*base66 + (130897369867837119/21343750000000000000000000000000 : ℝ)*base68 + (285739149055524619/21343750000000000000000000000000 : ℝ)*base70 + (76158886603774619/21343750000000000000000000000000 : ℝ)*base72 + (1367632785393/1707500000000000000000000000 : ℝ)*base74 + (25814775309962119/21343750000000000000000000000000 : ℝ)*base76 + (207387693024619/21343750000000000000000000000000 : ℝ)*base78 + (99174580605587119/21343750000000000000000000000000 : ℝ)*base80 + (19001636036311/3415000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4441369/625000000000000000000 : ℝ)*base89 + (4441369/625000000000000000000 : ℝ)*base91 + (4441369/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (980015740969485775816573677/106718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (903547151/50000000000000 : ℝ)*(base19) + (1560585103/100000000000000 : ℝ)*(base23) + (178079/625000000000 : ℝ)*(upper2) + (31806457/10000000000000 : ℝ)*(upper3) + (137909473/100000000000000 : ℝ)*(upper5) + (860430260939831/50000000000000 : ℝ)*(major0) + (860430260939831/50000000000000 : ℝ)*(major1) + (860430260939831/50000000000000 : ℝ)*(major2) + (3407237811/25000000000000 : ℝ)*(sp1) + (3131871297/25000000000000 : ℝ)*(sp2) + (305077550329041/12500000000000 : ℝ)*(sp4) + (1220302483293391/50000000000000 : ℝ)*(sp5) + (610151578640509/25000000000000 : ℝ)*(sp6) + (31284385469423/3125000000000 : ℝ)*(sp7) + (31284385469423/3125000000000 : ℝ)*(f.failure) + (305077550329041/12500000000000 : ℝ)*(f.sum) + (2943898573917/1067187500000000000000000000 : ℝ)*base65 + (731962483098162059/213437500000000000000000000000000 : ℝ)*base68 + (1150331976531837941/213437500000000000000000000000000 : ℝ)*base69 + (457980566348712941/213437500000000000000000000000000 : ℝ)*base71 + (1491142005157/4268750000000000000000000000 : ℝ)*base74 + (253921100719412059/213437500000000000000000000000000 : ℝ)*base76 + (1106914493815587941/213437500000000000000000000000000 : ℝ)*base77 + (1201209146829337941/213437500000000000000000000000000 : ℝ)*base79 + (20635495208093/4268750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (376479/78125000000000000000 : ℝ)*base90 + (376479/78125000000000000000 : ℝ)*base92 + (376479/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1604_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42974227/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24381/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3891/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9021/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8949/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1604_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1604_s2_0 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-214735821/1250000000 : ℝ)*x 0 + (218774489/400000000 : ℝ)*x 1 + (2586604047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214735821/1250000000 : ℝ)^4735 ≤ (2113156234959/20000000000000 : ℝ)^3711 := by
    have hnat : (214735821 : ℕ)^4735*20000000000000^3711 ≤ 2113156234959^3711*1250000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214735821 1250000000 2113156234959 20000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218774489/400000000 : ℝ)^4735 ≤ (11576143103321/25000000000000 : ℝ)^3711 := by
    have hnat : (218774489 : ℕ)^4735*25000000000000^3711 ≤ 11576143103321^3711*400000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218774489 400000000 11576143103321 25000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2586604047/5000000000 : ℝ)^4735 ≤ (43129646393199/100000000000000 : ℝ)^3711 := by
    have hnat : (2586604047 : ℕ)^4735*100000000000000^3711 ≤ 43129646393199^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586604047 5000000000 43129646393199 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214735821/1250000000 : ℝ), (218774489/400000000 : ℝ), (2586604047/5000000000 : ℝ)] ![(2113156234959/20000000000000 : ℝ), (11576143103321/25000000000000 : ℝ), (43129646393199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214735821/1250000000 : ℝ)|^4735 ≤ (2113156234959/20000000000000 : ℝ)^3711
        have hw : |(-214735821/1250000000 : ℝ)|=(214735821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218774489/400000000 : ℝ)|^4735 ≤ (11576143103321/25000000000000 : ℝ)^3711
        have hw : |(218774489/400000000 : ℝ)|=(218774489/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2586604047/5000000000 : ℝ)|^4735 ≤ (43129646393199/100000000000000 : ℝ)^3711
        have hw : |(2586604047/5000000000 : ℝ)|=(2586604047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s2_1 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1339137451/2500000000 : ℝ)*x 0 + (-187088891/1000000000 : ℝ)*x 1 + (129330203/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339137451/2500000000 : ℝ)^4735 ≤ (9017884840563/20000000000000 : ℝ)^3711 := by
    have hnat : (1339137451 : ℕ)^4735*20000000000000^3711 ≤ 9017884840563^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339137451 2500000000 9017884840563 20000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (187088891/1000000000 : ℝ)^4735 ≤ (11780929110813/100000000000000 : ℝ)^3711 := by
    have hnat : (187088891 : ℕ)^4735*100000000000000^3711 ≤ 11780929110813^3711*1000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187088891 1000000000 11780929110813 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129330203/250000000 : ℝ)^4735 ≤ (43129646669777/100000000000000 : ℝ)^3711 := by
    have hnat : (129330203 : ℕ)^4735*100000000000000^3711 ≤ 43129646669777^3711*250000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129330203 250000000 43129646669777 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1339137451/2500000000 : ℝ), (-187088891/1000000000 : ℝ), (129330203/250000000 : ℝ)] ![(9017884840563/20000000000000 : ℝ), (11780929110813/100000000000000 : ℝ), (43129646669777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1339137451/2500000000 : ℝ)|^4735 ≤ (9017884840563/20000000000000 : ℝ)^3711
        have hw : |(1339137451/2500000000 : ℝ)|=(1339137451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-187088891/1000000000 : ℝ)|^4735 ≤ (11780929110813/100000000000000 : ℝ)^3711
        have hw : |(-187088891/1000000000 : ℝ)|=(187088891/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129330203/250000000 : ℝ)|^4735 ≤ (43129646669777/100000000000000 : ℝ)^3711
        have hw : |(129330203/250000000 : ℝ)|=(129330203/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s2_2 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535654983/1000000000 : ℝ)*x 0 + (1293302021/2500000000 : ℝ)*x 1 + (-1870888923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535654983/1000000000 : ℝ)^4735 ≤ (2818089030129/6250000000000 : ℝ)^3711 := by
    have hnat : (535654983 : ℕ)^4735*6250000000000^3711 ≤ 2818089030129^3711*1000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535654983 1000000000 2818089030129 6250000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293302021/2500000000 : ℝ)^4735 ≤ (21564823143411/50000000000000 : ℝ)^3711 := by
    have hnat : (1293302021 : ℕ)^4735*50000000000000^3711 ≤ 21564823143411^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293302021 2500000000 21564823143411 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870888923/10000000000 : ℝ)^4735 ≤ (11780929215261/100000000000000 : ℝ)^3711 := by
    have hnat : (1870888923 : ℕ)^4735*100000000000000^3711 ≤ 11780929215261^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870888923 10000000000 11780929215261 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535654983/1000000000 : ℝ), (1293302021/2500000000 : ℝ), (-1870888923/10000000000 : ℝ)] ![(2818089030129/6250000000000 : ℝ), (21564823143411/50000000000000 : ℝ), (11780929215261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535654983/1000000000 : ℝ)|^4735 ≤ (2818089030129/6250000000000 : ℝ)^3711
        have hw : |(535654983/1000000000 : ℝ)|=(535654983/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1293302021/2500000000 : ℝ)|^4735 ≤ (21564823143411/50000000000000 : ℝ)^3711
        have hw : |(1293302021/2500000000 : ℝ)|=(1293302021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1870888923/10000000000 : ℝ)|^4735 ≤ (11780929215261/100000000000000 : ℝ)^3711
        have hw : |(-1870888923/10000000000 : ℝ)|=(1870888923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s2_3 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054111229/2500000000 : ℝ)*x 0 + (1933724863/5000000000 : ℝ)*x 1 + (2294727609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054111229/2500000000 : ℝ)^4735 ≤ (33224273823829/100000000000000 : ℝ)^3711 := by
    have hnat : (1054111229 : ℕ)^4735*100000000000000^3711 ≤ 33224273823829^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054111229 2500000000 33224273823829 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1933724863/5000000000 : ℝ)^4735 ≤ (29756381998081/100000000000000 : ℝ)^3711 := by
    have hnat : (1933724863 : ℕ)^4735*100000000000000^3711 ≤ 29756381998081^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933724863 5000000000 29756381998081 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2294727609/5000000000 : ℝ)^4735 ≤ (37019344158243/100000000000000 : ℝ)^3711 := by
    have hnat : (2294727609 : ℕ)^4735*100000000000000^3711 ≤ 37019344158243^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2294727609 5000000000 37019344158243 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054111229/2500000000 : ℝ), (1933724863/5000000000 : ℝ), (2294727609/5000000000 : ℝ)] ![(33224273823829/100000000000000 : ℝ), (29756381998081/100000000000000 : ℝ), (37019344158243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054111229/2500000000 : ℝ)|^4735 ≤ (33224273823829/100000000000000 : ℝ)^3711
        have hw : |(1054111229/2500000000 : ℝ)|=(1054111229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1933724863/5000000000 : ℝ)|^4735 ≤ (29756381998081/100000000000000 : ℝ)^3711
        have hw : |(1933724863/5000000000 : ℝ)|=(1933724863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2294727609/5000000000 : ℝ)|^4735 ≤ (37019344158243/100000000000000 : ℝ)^3711
        have hw : |(2294727609/5000000000 : ℝ)|=(2294727609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s2_4 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-858984849/5000000000 : ℝ)*x 0 + (323469989/625000000 : ℝ)*x 1 + (683378133/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (858984849/5000000000 : ℝ)^4735 ≤ (2113286709817/20000000000000 : ℝ)^3711 := by
    have hnat : (858984849 : ℕ)^4735*20000000000000^3711 ≤ 2113286709817^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858984849 5000000000 2113286709817 20000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323469989/625000000 : ℝ)^4735 ≤ (5394279905387/12500000000000 : ℝ)^3711 := by
    have hnat : (323469989 : ℕ)^4735*12500000000000^3711 ≤ 5394279905387^3711*625000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323469989 625000000 5394279905387 12500000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683378133/1250000000 : ℝ)^4735 ≤ (4627932718843/10000000000000 : ℝ)^3711 := by
    have hnat : (683378133 : ℕ)^4735*10000000000000^3711 ≤ 4627932718843^3711*1250000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683378133 1250000000 4627932718843 10000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-858984849/5000000000 : ℝ), (323469989/625000000 : ℝ), (683378133/1250000000 : ℝ)] ![(2113286709817/20000000000000 : ℝ), (5394279905387/12500000000000 : ℝ), (4627932718843/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-858984849/5000000000 : ℝ)|^4735 ≤ (2113286709817/20000000000000 : ℝ)^3711
        have hw : |(-858984849/5000000000 : ℝ)|=(858984849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323469989/625000000 : ℝ)|^4735 ≤ (5394279905387/12500000000000 : ℝ)^3711
        have hw : |(323469989/625000000 : ℝ)|=(323469989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683378133/1250000000 : ℝ)|^4735 ≤ (4627932718843/10000000000000 : ℝ)^3711
        have hw : |(683378133/1250000000 : ℝ)|=(683378133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s2_5 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277972787/10000000000 : ℝ)*x 0 + (-63082873/400000000 : ℝ)*x 1 + (1366756277/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277972787/10000000000 : ℝ)^4735 ≤ (884943868391/2000000000000 : ℝ)^3711 := by
    have hnat : (5277972787 : ℕ)^4735*2000000000000^3711 ≤ 884943868391^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277972787 10000000000 884943868391 2000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63082873/400000000 : ℝ)^4735 ≤ (4736739447313/50000000000000 : ℝ)^3711 := by
    have hnat : (63082873 : ℕ)^4735*50000000000000^3711 ≤ 4736739447313^3711*400000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63082873 400000000 4736739447313 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1366756277/2500000000 : ℝ)^4735 ≤ (1851173106547/4000000000000 : ℝ)^3711 := by
    have hnat : (1366756277 : ℕ)^4735*4000000000000^3711 ≤ 1851173106547^3711*2500000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366756277 2500000000 1851173106547 4000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277972787/10000000000 : ℝ), (-63082873/400000000 : ℝ), (1366756277/2500000000 : ℝ)] ![(884943868391/2000000000000 : ℝ), (4736739447313/50000000000000 : ℝ), (1851173106547/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277972787/10000000000 : ℝ)|^4735 ≤ (884943868391/2000000000000 : ℝ)^3711
        have hw : |(5277972787/10000000000 : ℝ)|=(5277972787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-63082873/400000000 : ℝ)|^4735 ≤ (4736739447313/50000000000000 : ℝ)^3711
        have hw : |(-63082873/400000000 : ℝ)|=(63082873/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1366756277/2500000000 : ℝ)|^4735 ≤ (1851173106547/4000000000000 : ℝ)^3711
        have hw : |(1366756277/2500000000 : ℝ)|=(1366756277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s2_6 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638986453/5000000000 : ℝ)*x 0 + (341689039/625000000 : ℝ)*x 1 + (-1577072341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638986453/5000000000 : ℝ)^4735 ≤ (44247194692451/100000000000000 : ℝ)^3711 := by
    have hnat : (2638986453 : ℕ)^4735*100000000000000^3711 ≤ 44247194692451^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638986453 5000000000 44247194692451 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341689039/625000000 : ℝ)^4735 ≤ (46279322435979/100000000000000 : ℝ)^3711 := by
    have hnat : (341689039 : ℕ)^4735*100000000000000^3711 ≤ 46279322435979^3711*625000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341689039 625000000 46279322435979 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577072341/10000000000 : ℝ)^4735 ≤ (9473482849537/100000000000000 : ℝ)^3711 := by
    have hnat : (1577072341 : ℕ)^4735*100000000000000^3711 ≤ 9473482849537^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577072341 10000000000 9473482849537 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638986453/5000000000 : ℝ), (341689039/625000000 : ℝ), (-1577072341/10000000000 : ℝ)] ![(44247194692451/100000000000000 : ℝ), (46279322435979/100000000000000 : ℝ), (9473482849537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638986453/5000000000 : ℝ)|^4735 ≤ (44247194692451/100000000000000 : ℝ)^3711
        have hw : |(2638986453/5000000000 : ℝ)|=(2638986453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341689039/625000000 : ℝ)|^4735 ≤ (46279322435979/100000000000000 : ℝ)^3711
        have hw : |(341689039/625000000 : ℝ)|=(341689039/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1577072341/10000000000 : ℝ)|^4735 ≤ (9473482849537/100000000000000 : ℝ)^3711
        have hw : |(-1577072341/10000000000 : ℝ)|=(1577072341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1604_s2_7 (p : ℝ) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4216648063/10000000000 : ℝ)*x 0 + (2291909771/5000000000 : ℝ)*x 1 + (1936573879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4216648063/10000000000 : ℝ)^4735 ≤ (33226316273649/100000000000000 : ℝ)^3711 := by
    have hnat : (4216648063 : ℕ)^4735*100000000000000^3711 ≤ 33226316273649^3711*10000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216648063 10000000000 33226316273649 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2291909771/5000000000 : ℝ)^4735 ≤ (18480676016547/50000000000000 : ℝ)^3711 := by
    have hnat : (2291909771 : ℕ)^4735*50000000000000^3711 ≤ 18480676016547^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291909771 5000000000 18480676016547 50000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1936573879/5000000000 : ℝ)^4735 ≤ (29812331677343/100000000000000 : ℝ)^3711 := by
    have hnat : (1936573879 : ℕ)^4735*100000000000000^3711 ≤ 29812331677343^3711*5000000000^4735 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936573879 5000000000 29812331677343 100000000000000 4735 3711 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4735/1024 : ℝ)) 4735 3711 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4216648063/10000000000 : ℝ), (2291909771/5000000000 : ℝ), (1936573879/5000000000 : ℝ)] ![(33226316273649/100000000000000 : ℝ), (18480676016547/50000000000000 : ℝ), (29812331677343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4216648063/10000000000 : ℝ)|^4735 ≤ (33226316273649/100000000000000 : ℝ)^3711
        have hw : |(4216648063/10000000000 : ℝ)|=(4216648063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2291909771/5000000000 : ℝ)|^4735 ≤ (18480676016547/50000000000000 : ℝ)^3711
        have hw : |(2291909771/5000000000 : ℝ)|=(2291909771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1936573879/5000000000 : ℝ)|^4735 ≤ (29812331677343/100000000000000 : ℝ)^3711
        have hw : |(1936573879/5000000000 : ℝ)|=(1936573879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1604_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42974227/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8949/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9021/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2561/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (413/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8949/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9021/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8949/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9021/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8949/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9021/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8949/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9021/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8949/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9021/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8949/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9021/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9021/100000 : ℝ) ^ (4731/1024 : ℝ) ≤ (148988999422763/10000000000000000000 : ℝ) := by
    have hpowers : (9021/100000 : ℝ)^4731 ≤ (148988999422763/10000000000000000000 : ℝ)^1024 := by
      have hnat : (9021 : ℕ)^4731*10000000000000000000^1024 ≤ 148988999422763^1024*100000^4731 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9021 100000 148988999422763 10000000000000000000 4731 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9021/100000 : ℝ)) (X := (148988999422763/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8949/50000 : ℝ) ^ (4731/1024 : ℝ) ≤ (8826921290429729/25000000000000000000 : ℝ) := by
    have hpowers : (8949/50000 : ℝ)^4731 ≤ (8826921290429729/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8949 : ℕ)^4731*25000000000000000000^1024 ≤ 8826921290429729^1024*50000^4731 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8949 50000 8826921290429729 25000000000000000000 4731 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8949/50000 : ℝ)) (X := (8826921290429729/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000148988999422763/5000000000000000000 : ℝ) ≤ (10000064495013479/10000000000000000 : ℝ) ^ (4731/1024 : ℝ) := by
    have hpowers : (5000148988999422763/5000000000000000000 : ℝ)^1024 ≤ (10000064495013479/10000000000000000 : ℝ)^4731 := by
      have hnat : (5000148988999422763 : ℕ)^1024*10000000000000000^4731 ≤ 10000064495013479^4731*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000148988999422763 5000000000000000000 10000064495013479 10000000000000000 1024 4731 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000064495013479/10000000000000000 : ℝ)) (X := (5000148988999422763/5000000000000000000 : ℝ)) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018398787577973273/50000000000000000000 : ℝ) ≤ (625049771831959/625000000000000 : ℝ) ^ (4731/1024 : ℝ) := by
    have hpowers : (50018398787577973273/50000000000000000000 : ℝ)^1024 ≤ (625049771831959/625000000000000 : ℝ)^4731 := by
      have hnat : (50018398787577973273 : ℕ)^1024*625000000000000^4731 ≤ 625049771831959^4731*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018398787577973273 50000000000000000000 625049771831959 625000000000000 1024 4731 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625049771831959/625000000000000 : ℝ)) (X := (50018398787577973273/50000000000000000000 : ℝ)) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508826921290429729/12500000000000000000 : ℝ) ≤ (10001528203609209/10000000000000000 : ℝ) ^ (4731/1024 : ℝ) := by
    have hpowers : (12508826921290429729/12500000000000000000 : ℝ)^1024 ≤ (10001528203609209/10000000000000000 : ℝ)^4731 := by
      have hnat : (12508826921290429729 : ℕ)^1024*10000000000000000^4731 ≤ 10001528203609209^4731*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508826921290429729 12500000000000000000 10001528203609209 10000000000000000 1024 4731 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001528203609209/10000000000000000 : ℝ)) (X := (12508826921290429729/12500000000000000000 : ℝ)) (by norm_num) 4731 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(148988999422763/10000000000000000000 : ℝ) ≤ ((29585789468997524251/29590000000000000000 : ℝ)+2*(146370859573/177540000000000 : ℝ)*(9021/100000 : ℝ))^(4731/1024 : ℝ) := by
    rw [show (29585789468997524251/29590000000000000000 : ℝ)+2*(146370859573/177540000000000 : ℝ)*(9021/100000 : ℝ)=(10000064495013479/10000000000000000 : ℝ) by norm_num, show 1+2*(148988999422763/10000000000000000000 : ℝ)=(5000148988999422763/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8826921290429729/25000000000000000000 : ℝ)+(148988999422763/10000000000000000000 : ℝ) ≤ ((29585789468997524251/29590000000000000000 : ℝ)+(146370859573/177540000000000 : ℝ)*((8949/50000 : ℝ)+(9021/100000 : ℝ)))^(4731/1024 : ℝ) := by
    rw [show (29585789468997524251/29590000000000000000 : ℝ)+(146370859573/177540000000000 : ℝ)*((8949/50000 : ℝ)+(9021/100000 : ℝ))=(625049771831959/625000000000000 : ℝ) by norm_num, show 1+(8826921290429729/25000000000000000000 : ℝ)+(148988999422763/10000000000000000000 : ℝ)=(50018398787577973273/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8826921290429729/25000000000000000000 : ℝ) ≤ ((29585789468997524251/29590000000000000000 : ℝ)+2*(146370859573/177540000000000 : ℝ)*(8949/50000 : ℝ))^(4731/1024 : ℝ) := by
    rw [show (29585789468997524251/29590000000000000000 : ℝ)+2*(146370859573/177540000000000 : ℝ)*(8949/50000 : ℝ)=(10001528203609209/10000000000000000 : ℝ) by norm_num, show 1+2*(8826921290429729/25000000000000000000 : ℝ)=(12508826921290429729/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29585789468997524251/29590000000000000000 : ℝ)*(X 1 0+X 2 0)+(146370859573/177540000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4731/1024 : ℝ)) (lo := (9021/100000 : ℝ)) (hi := (8949/50000 : ℝ)) (c := (29585789468997524251/29590000000000000000 : ℝ)) (alpha := (146370859573/177540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29585789468997524251/29590000000000000000 : ℝ)*(X 0 1+X 2 1)+(146370859573/177540000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4731/1024 : ℝ)) (lo := (9021/100000 : ℝ)) (hi := (8949/50000 : ℝ)) (c := (29585789468997524251/29590000000000000000 : ℝ)) (alpha := (146370859573/177540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29585789468997524251/29590000000000000000 : ℝ)*(X 0 2+X 1 2)+(146370859573/177540000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4731/1024 : ℝ)) (lo := (9021/100000 : ℝ)) (hi := (8949/50000 : ℝ)) (c := (29585789468997524251/29590000000000000000 : ℝ)) (alpha := (146370859573/177540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-214735821/1250000000 : ℝ)*X 0 0+(218774489/400000000 : ℝ)*X 0 1+(2586604047/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1339137451/2500000000 : ℝ)*X 1 0+(-187088891/1000000000 : ℝ)*X 1 1+(129330203/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535654983/1000000000 : ℝ)*X 2 0+(1293302021/2500000000 : ℝ)*X 2 1+(-1870888923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1054111229/2500000000 : ℝ)*X 0 0+(1933724863/5000000000 : ℝ)*X 0 1+(2294727609/5000000000 : ℝ)*X 0 2+(1054111229/2500000000 : ℝ)*X 1 0+(1933724863/5000000000 : ℝ)*X 1 1+(2294727609/5000000000 : ℝ)*X 1 2+(1054111229/2500000000 : ℝ)*X 2 0+(1933724863/5000000000 : ℝ)*X 2 1+(2294727609/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-858984849/5000000000 : ℝ)*X 0 0+(323469989/625000000 : ℝ)*X 0 1+(683378133/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277972787/10000000000 : ℝ)*X 1 0+(-63082873/400000000 : ℝ)*X 1 1+(1366756277/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638986453/5000000000 : ℝ)*X 2 0+(341689039/625000000 : ℝ)*X 2 1+(-1577072341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4216648063/10000000000 : ℝ)*X 0 0+(2291909771/5000000000 : ℝ)*X 0 1+(1936573879/5000000000 : ℝ)*X 0 2+(4216648063/10000000000 : ℝ)*X 1 0+(2291909771/5000000000 : ℝ)*X 1 1+(1936573879/5000000000 : ℝ)*X 1 2+(4216648063/10000000000 : ℝ)*X 2 0+(2291909771/5000000000 : ℝ)*X 2 1+(1936573879/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1604_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (429624455989548975717120557/92468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31352261/4000000000000 : ℝ)*(base19) + (749949249/100000000000000 : ℝ)*(base23) + (6728769/25000000000000 : ℝ)*(lower2) + (24435723/20000000000000 : ℝ)*(upper3) + (77363583/100000000000000 : ℝ)*(upper5) + (148802419930981/6250000000000 : ℝ)*(major0) + (148802419930981/6250000000000 : ℝ)*(major1) + (148802419930981/6250000000000 : ℝ)*(major2) + (105519673597179/3125000000000 : ℝ)*(sp0) + (6594995679813/195312500000 : ℝ)*(sp1) + (844159455480383/25000000000000 : ℝ)*(sp2) + (692517297517037/50000000000000 : ℝ)*(sp3) + (9016761053/100000000000000 : ℝ)*(sp4) + (4116014583/100000000000000 : ℝ)*(sp7) + (1385038711048657/100000000000000 : ℝ)*(f.failure) + (1688319285935391/50000000000000 : ℝ)*(f.sum) + (28557212640347/8877000000000000000000000000 : ℝ)*base66 + (2203263358461785693/554812500000000000000000000000000 : ℝ)*base67 + (1331963789063285693/554812500000000000000000000000000 : ℝ)*base69 + (4065107498465848193/554812500000000000000000000000000 : ℝ)*base71 + (3237140614529/4438500000000000000000000000 : ℝ)*base73 + (5005763645486214307/554812500000000000000000000000000 : ℝ)*base76 + (646212524938651807/554812500000000000000000000000000 : ℝ)*base78 + (1298794030809785693/554812500000000000000000000000000 : ℝ)*base79 + (17403415579019/4438500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6036861/2500000000000000000000 : ℝ)*base90 + (6036861/2500000000000000000000 : ℝ)*base92 + (6036861/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (798310190293710559720579059/92468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1227653163/100000000000000 : ℝ)*(base19) + (147704087/10000000000000 : ℝ)*(base23) + (9472701/6250000000000 : ℝ)*(upper3) + (58727891/50000000000000 : ℝ)*(lower4) + (18648807/12500000000000 : ℝ)*(upper5) + (151174609176201/6250000000000 : ℝ)*(major0) + (151174609176201/6250000000000 : ℝ)*(major1) + (151174609176201/6250000000000 : ℝ)*(major2) + (7147696669/50000000000000 : ℝ)*(sp1) + (1090355117/10000000000000 : ℝ)*(sp2) + (343046838391119/10000000000000 : ℝ)*(sp4) + (3430452860864689/100000000000000 : ℝ)*(sp5) + (68609120066383/2000000000000 : ℝ)*(sp6) + (175889852743833/12500000000000 : ℝ)*(sp7) + (175889852743833/12500000000000 : ℝ)*(f.failure) + (343046838391119/10000000000000 : ℝ)*(f.sum) + (2189355636513/739750000000000000000000000 : ℝ)*base66 + (763767644401949549/184937500000000000000000000000000 : ℝ)*base68 + (3283535723152949549/184937500000000000000000000000000 : ℝ)*base70 + (1342341169430762049/184937500000000000000000000000000 : ℝ)*base72 + (15513290651459/2959000000000000000000000000 : ℝ)*base73 + (3285209372759699549/184937500000000000000000000000000 : ℝ)*base76 + (830568619917949549/184937500000000000000000000000000 : ℝ)*base78 + (2471106450019449549/184937500000000000000000000000000 : ℝ)*base80 + (2475526474103/739750000000000000000000000 : ℝ)*base82 + (2192091/312500000000000000000 : ℝ)*base89 + (2192091/312500000000000000000 : ℝ)*base91 + (2192091/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1604_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42974227/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8949/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9021/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2561/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (413/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1604_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1604_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42974227/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2561/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (413/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1604_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1604_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1604_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4731/1024 : ℝ) ≤ p) (hpb : p ≤ (4735/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (42974227/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2561/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (413/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1604_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

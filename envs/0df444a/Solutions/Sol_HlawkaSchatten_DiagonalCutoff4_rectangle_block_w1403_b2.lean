-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1403_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:46:42.804639+00:00
-- url     : https://prove2.me/submissions/531a60ee-0ab7-4b81-bc5a-cb4d74529940

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
theorem support_rectangle_w1403_s6_0 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-996210657/5000000000 : ℝ)*x 0 + (5409565173/10000000000 : ℝ)*x 1 + (5246290767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (996210657/5000000000 : ℝ)^4363 ≤ (6074161736693/50000000000000 : ℝ)^3339 := by
    have hnat : (996210657 : ℕ)^4363*50000000000000^3339 ≤ 6074161736693^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996210657 5000000000 6074161736693 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409565173/10000000000 : ℝ)^4363 ≤ (22402627347959/50000000000000 : ℝ)^3339 := by
    have hnat : (5409565173 : ℕ)^4363*50000000000000^3339 ≤ 22402627347959^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409565173 10000000000 22402627347959 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246290767/10000000000 : ℝ)^4363 ≤ (5380802726811/12500000000000 : ℝ)^3339 := by
    have hnat : (5246290767 : ℕ)^4363*12500000000000^3339 ≤ 5380802726811^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246290767 10000000000 5380802726811 12500000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-996210657/5000000000 : ℝ), (5409565173/10000000000 : ℝ), (5246290767/10000000000 : ℝ)] ![(6074161736693/50000000000000 : ℝ), (22402627347959/50000000000000 : ℝ), (5380802726811/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-996210657/5000000000 : ℝ)|^4363 ≤ (6074161736693/50000000000000 : ℝ)^3339
        have hw : |(-996210657/5000000000 : ℝ)|=(996210657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409565173/10000000000 : ℝ)|^4363 ≤ (22402627347959/50000000000000 : ℝ)^3339
        have hw : |(5409565173/10000000000 : ℝ)|=(5409565173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246290767/10000000000 : ℝ)|^4363 ≤ (5380802726811/12500000000000 : ℝ)^3339
        have hw : |(5246290767/10000000000 : ℝ)|=(5246290767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s6_1 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336965559/2500000000 : ℝ)*x 0 + (-518891313/2500000000 : ℝ)*x 1 + (5246290829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336965559/2500000000 : ℝ)^4363 ≤ (44138633759801/100000000000000 : ℝ)^3339 := by
    have hnat : (1336965559 : ℕ)^4363*100000000000000^3339 ≤ 44138633759801^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336965559 2500000000 44138633759801 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518891313/2500000000 : ℝ)^4363 ≤ (12814943750667/100000000000000 : ℝ)^3339 := by
    have hnat : (518891313 : ℕ)^4363*100000000000000^3339 ≤ 12814943750667^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518891313 2500000000 12814943750667 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246290829/10000000000 : ℝ)^4363 ≤ (21523211239609/50000000000000 : ℝ)^3339 := by
    have hnat : (5246290829 : ℕ)^4363*50000000000000^3339 ≤ 21523211239609^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246290829 10000000000 21523211239609 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336965559/2500000000 : ℝ), (-518891313/2500000000 : ℝ), (5246290829/10000000000 : ℝ)] ![(44138633759801/100000000000000 : ℝ), (12814943750667/100000000000000 : ℝ), (21523211239609/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336965559/2500000000 : ℝ)|^4363 ≤ (44138633759801/100000000000000 : ℝ)^3339
        have hw : |(1336965559/2500000000 : ℝ)|=(1336965559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-518891313/2500000000 : ℝ)|^4363 ≤ (12814943750667/100000000000000 : ℝ)^3339
        have hw : |(-518891313/2500000000 : ℝ)|=(518891313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246290829/10000000000 : ℝ)|^4363 ≤ (21523211239609/50000000000000 : ℝ)^3339
        have hw : |(5246290829/10000000000 : ℝ)|=(5246290829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s6_2 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347862229/10000000000 : ℝ)*x 0 + (655786351/1250000000 : ℝ)*x 1 + (-2075565289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347862229/10000000000 : ℝ)^4363 ≤ (11034658421077/25000000000000 : ℝ)^3339 := by
    have hnat : (5347862229 : ℕ)^4363*25000000000000^3339 ≤ 11034658421077^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347862229 10000000000 11034658421077 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655786351/1250000000 : ℝ)^4363 ≤ (43046422254067/100000000000000 : ℝ)^3339 := by
    have hnat : (655786351 : ℕ)^4363*100000000000000^3339 ≤ 43046422254067^3339*1250000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655786351 1250000000 43046422254067 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2075565289/10000000000 : ℝ)^4363 ≤ (3203736012293/25000000000000 : ℝ)^3339 := by
    have hnat : (2075565289 : ℕ)^4363*25000000000000^3339 ≤ 3203736012293^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075565289 10000000000 3203736012293 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347862229/10000000000 : ℝ), (655786351/1250000000 : ℝ), (-2075565289/10000000000 : ℝ)] ![(11034658421077/25000000000000 : ℝ), (43046422254067/100000000000000 : ℝ), (3203736012293/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347862229/10000000000 : ℝ)|^4363 ≤ (11034658421077/25000000000000 : ℝ)^3339
        have hw : |(5347862229/10000000000 : ℝ)|=(5347862229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655786351/1250000000 : ℝ)|^4363 ≤ (43046422254067/100000000000000 : ℝ)^3339
        have hw : |(655786351/1250000000 : ℝ)|=(655786351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2075565289/10000000000 : ℝ)|^4363 ≤ (3203736012293/25000000000000 : ℝ)^3339
        have hw : |(-2075565289/10000000000 : ℝ)|=(2075565289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s6_3 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4310917527/10000000000 : ℝ)*x 0 + (82784373/200000000 : ℝ)*x 1 + (897814741/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310917527/10000000000 : ℝ)^4363 ≤ (33304279991873/100000000000000 : ℝ)^3339 := by
    have hnat : (4310917527 : ℕ)^4363*100000000000000^3339 ≤ 33304279991873^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310917527 10000000000 33304279991873 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82784373/200000000 : ℝ)^4363 ≤ (7895423329511/25000000000000 : ℝ)^3339 := by
    have hnat : (82784373 : ℕ)^4363*25000000000000^3339 ≤ 7895423329511^3339*200000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82784373 200000000 7895423329511 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897814741/2000000000 : ℝ)^4363 ≤ (35114026674819/100000000000000 : ℝ)^3339 := by
    have hnat : (897814741 : ℕ)^4363*100000000000000^3339 ≤ 35114026674819^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897814741 2000000000 35114026674819 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310917527/10000000000 : ℝ), (82784373/200000000 : ℝ), (897814741/2000000000 : ℝ)] ![(33304279991873/100000000000000 : ℝ), (7895423329511/25000000000000 : ℝ), (35114026674819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310917527/10000000000 : ℝ)|^4363 ≤ (33304279991873/100000000000000 : ℝ)^3339
        have hw : |(4310917527/10000000000 : ℝ)|=(4310917527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82784373/200000000 : ℝ)|^4363 ≤ (7895423329511/25000000000000 : ℝ)^3339
        have hw : |(82784373/200000000 : ℝ)|=(82784373/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897814741/2000000000 : ℝ)|^4363 ≤ (35114026674819/100000000000000 : ℝ)^3339
        have hw : |(897814741/2000000000 : ℝ)|=(897814741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s6_4 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1992432943/10000000000 : ℝ)*x 0 + (2623439191/5000000000 : ℝ)*x 1 + (216358979/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1992432943/10000000000 : ℝ)^4363 ≤ (12148416123663/100000000000000 : ℝ)^3339 := by
    have hnat : (1992432943 : ℕ)^4363*100000000000000^3339 ≤ 12148416123663^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992432943 10000000000 12148416123663 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623439191/5000000000 : ℝ)^4363 ≤ (43052722007087/100000000000000 : ℝ)^3339 := by
    have hnat : (2623439191 : ℕ)^4363*100000000000000^3339 ≤ 43052722007087^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623439191 5000000000 43052722007087 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216358979/400000000 : ℝ)^4363 ≤ (2799928866197/6250000000000 : ℝ)^3339 := by
    have hnat : (216358979 : ℕ)^4363*6250000000000^3339 ≤ 2799928866197^3339*400000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216358979 400000000 2799928866197 6250000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1992432943/10000000000 : ℝ), (2623439191/5000000000 : ℝ), (216358979/400000000 : ℝ)] ![(12148416123663/100000000000000 : ℝ), (43052722007087/100000000000000 : ℝ), (2799928866197/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1992432943/10000000000 : ℝ)|^4363 ≤ (12148416123663/100000000000000 : ℝ)^3339
        have hw : |(-1992432943/10000000000 : ℝ)|=(1992432943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623439191/5000000000 : ℝ)|^4363 ≤ (43052722007087/100000000000000 : ℝ)^3339
        have hw : |(2623439191/5000000000 : ℝ)|=(2623439191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216358979/400000000 : ℝ)|^4363 ≤ (2799928866197/6250000000000 : ℝ)^3339
        have hw : |(216358979/400000000 : ℝ)|=(216358979/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s6_5 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305525961/10000000000 : ℝ)*x 0 + (-1912881503/10000000000 : ℝ)*x 1 + (338060907/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305525961/10000000000 : ℝ)^4363 ≤ (2184130281663/5000000000000 : ℝ)^3339 := by
    have hnat : (5305525961 : ℕ)^4363*5000000000000^3339 ≤ 2184130281663^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305525961 10000000000 2184130281663 5000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1912881503/10000000000 : ℝ)^4363 ≤ (11518532092367/100000000000000 : ℝ)^3339 := by
    have hnat : (1912881503 : ℕ)^4363*100000000000000^3339 ≤ 11518532092367^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912881503 10000000000 11518532092367 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338060907/625000000 : ℝ)^4363 ≤ (22399431129789/50000000000000 : ℝ)^3339 := by
    have hnat : (338060907 : ℕ)^4363*50000000000000^3339 ≤ 22399431129789^3339*625000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338060907 625000000 22399431129789 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305525961/10000000000 : ℝ), (-1912881503/10000000000 : ℝ), (338060907/625000000 : ℝ)] ![(2184130281663/5000000000000 : ℝ), (11518532092367/100000000000000 : ℝ), (22399431129789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305525961/10000000000 : ℝ)|^4363 ≤ (2184130281663/5000000000000 : ℝ)^3339
        have hw : |(5305525961/10000000000 : ℝ)|=(5305525961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1912881503/10000000000 : ℝ)|^4363 ≤ (11518532092367/100000000000000 : ℝ)^3339
        have hw : |(-1912881503/10000000000 : ℝ)|=(1912881503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338060907/625000000 : ℝ)|^4363 ≤ (22399431129789/50000000000000 : ℝ)^3339
        have hw : |(338060907/625000000 : ℝ)|=(338060907/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s6_6 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212221023/400000000 : ℝ)*x 0 + (2704487393/5000000000 : ℝ)*x 1 + (-956440827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212221023/400000000 : ℝ)^4363 ≤ (21841300740253/50000000000000 : ℝ)^3339 := by
    have hnat : (212221023 : ℕ)^4363*50000000000000^3339 ≤ 21841300740253^3339*400000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212221023 400000000 21841300740253 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704487393/5000000000 : ℝ)^4363 ≤ (44798865224897/100000000000000 : ℝ)^3339 := by
    have hnat : (2704487393 : ℕ)^4363*100000000000000^3339 ≤ 44798865224897^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704487393 5000000000 44798865224897 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (956440827/5000000000 : ℝ)^4363 ≤ (1439816660059/12500000000000 : ℝ)^3339 := by
    have hnat : (956440827 : ℕ)^4363*12500000000000^3339 ≤ 1439816660059^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956440827 5000000000 1439816660059 12500000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212221023/400000000 : ℝ), (2704487393/5000000000 : ℝ), (-956440827/5000000000 : ℝ)] ![(21841300740253/50000000000000 : ℝ), (44798865224897/100000000000000 : ℝ), (1439816660059/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212221023/400000000 : ℝ)|^4363 ≤ (21841300740253/50000000000000 : ℝ)^3339
        have hw : |(212221023/400000000 : ℝ)|=(212221023/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704487393/5000000000 : ℝ)|^4363 ≤ (44798865224897/100000000000000 : ℝ)^3339
        have hw : |(2704487393/5000000000 : ℝ)|=(2704487393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-956440827/5000000000 : ℝ)|^4363 ≤ (1439816660059/12500000000000 : ℝ)^3339
        have hw : |(-956440827/5000000000 : ℝ)|=(956440827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s6_7 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4310942327/10000000000 : ℝ)*x 0 + (4487814693/10000000000 : ℝ)*x 1 + (2070242079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310942327/10000000000 : ℝ)^4363 ≤ (16652265171973/50000000000000 : ℝ)^3339 := by
    have hnat : (4310942327 : ℕ)^4363*50000000000000^3339 ≤ 16652265171973^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310942327 10000000000 16652265171973 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487814693/10000000000 : ℝ)^4363 ≤ (8775289721807/25000000000000 : ℝ)^3339 := by
    have hnat : (4487814693 : ℕ)^4363*25000000000000^3339 ≤ 8775289721807^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487814693 10000000000 8775289721807 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2070242079/5000000000 : ℝ)^4363 ≤ (31594310753477/100000000000000 : ℝ)^3339 := by
    have hnat : (2070242079 : ℕ)^4363*100000000000000^3339 ≤ 31594310753477^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070242079 5000000000 31594310753477 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310942327/10000000000 : ℝ), (4487814693/10000000000 : ℝ), (2070242079/5000000000 : ℝ)] ![(16652265171973/50000000000000 : ℝ), (8775289721807/25000000000000 : ℝ), (31594310753477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310942327/10000000000 : ℝ)|^4363 ≤ (16652265171973/50000000000000 : ℝ)^3339
        have hw : |(4310942327/10000000000 : ℝ)|=(4310942327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487814693/10000000000 : ℝ)|^4363 ≤ (8775289721807/25000000000000 : ℝ)^3339
        have hw : |(4487814693/10000000000 : ℝ)|=(4487814693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2070242079/5000000000 : ℝ)|^4363 ≤ (31594310753477/100000000000000 : ℝ)^3339
        have hw : |(2070242079/5000000000 : ℝ)|=(2070242079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1403_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2257/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14743/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11281/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11281/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11281/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11281/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11281/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (11281/100000 : ℝ) ^ (2181/512 : ℝ) ≤ (1837608006374861/20000000000000000000 : ℝ) := by
    have hpowers : (11281/100000 : ℝ)^2181 ≤ (1837608006374861/20000000000000000000 : ℝ)^512 := by
      have hnat : (11281 : ℕ)^2181*20000000000000000000^512 ≤ 1837608006374861^512*100000^2181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11281 100000 1837608006374861 20000000000000000000 2181 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11281/100000 : ℝ)) (X := (1837608006374861/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3687/25000 : ℝ) ^ (2181/512 : ℝ) ≤ (14386924409131449/50000000000000000000 : ℝ) := by
    have hpowers : (3687/25000 : ℝ)^2181 ≤ (14386924409131449/50000000000000000000 : ℝ)^512 := by
      have hnat : (3687 : ℕ)^2181*50000000000000000000^512 ≤ 14386924409131449^512*25000^2181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3687 25000 14386924409131449 50000000000000000000 2181 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3687/25000 : ℝ)) (X := (14386924409131449/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001837608006374861/10000000000000000000 : ℝ) ≤ (2000086271357533/2000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (10001837608006374861/10000000000000000000 : ℝ)^512 ≤ (2000086271357533/2000000000000000 : ℝ)^2181 := by
      have hnat : (10001837608006374861 : ℕ)^512*2000000000000000^2181 ≤ 2000086271357533^2181*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001837608006374861 10000000000000000000 2000086271357533 2000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000086271357533/2000000000000000 : ℝ)) (X := (10001837608006374861/10000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037961888850137203/100000000000000000000 : ℝ) ≤ (10000891043766929/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (100037961888850137203/100000000000000000000 : ℝ)^512 ≤ (10000891043766929/10000000000000000 : ℝ)^2181 := by
      have hnat : (100037961888850137203 : ℕ)^512*10000000000000000^2181 ≤ 10000891043766929^2181*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037961888850137203 100000000000000000000 10000891043766929 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000891043766929/10000000000000000 : ℝ)) (X := (100037961888850137203/100000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014386924409131449/25000000000000000000 : ℝ) ≤ (10001350730746193/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (25014386924409131449/25000000000000000000 : ℝ)^512 ≤ (10001350730746193/10000000000000000 : ℝ)^2181 := by
      have hnat : (25014386924409131449 : ℕ)^512*10000000000000000^2181 ≤ 10001350730746193^2181*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014386924409131449 25000000000000000000 10001350730746193 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001350730746193/10000000000000000 : ℝ)) (X := (25014386924409131449/25000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1837608006374861/20000000000000000000 : ℝ) ≤ ((34661124056356680187/34670000000000000000 : ℝ)+2*(7182609051/5417187500000 : ℝ)*(11281/100000 : ℝ))^(2181/512 : ℝ) := by
    rw [show (34661124056356680187/34670000000000000000 : ℝ)+2*(7182609051/5417187500000 : ℝ)*(11281/100000 : ℝ)=(2000086271357533/2000000000000000 : ℝ) by norm_num, show 1+2*(1837608006374861/20000000000000000000 : ℝ)=(10001837608006374861/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14386924409131449/50000000000000000000 : ℝ)+(1837608006374861/20000000000000000000 : ℝ) ≤ ((34661124056356680187/34670000000000000000 : ℝ)+(7182609051/5417187500000 : ℝ)*((3687/25000 : ℝ)+(11281/100000 : ℝ)))^(2181/512 : ℝ) := by
    rw [show (34661124056356680187/34670000000000000000 : ℝ)+(7182609051/5417187500000 : ℝ)*((3687/25000 : ℝ)+(11281/100000 : ℝ))=(10000891043766929/10000000000000000 : ℝ) by norm_num, show 1+(14386924409131449/50000000000000000000 : ℝ)+(1837608006374861/20000000000000000000 : ℝ)=(100037961888850137203/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14386924409131449/50000000000000000000 : ℝ) ≤ ((34661124056356680187/34670000000000000000 : ℝ)+2*(7182609051/5417187500000 : ℝ)*(3687/25000 : ℝ))^(2181/512 : ℝ) := by
    rw [show (34661124056356680187/34670000000000000000 : ℝ)+2*(7182609051/5417187500000 : ℝ)*(3687/25000 : ℝ)=(10001350730746193/10000000000000000 : ℝ) by norm_num, show 1+2*(14386924409131449/50000000000000000000 : ℝ)=(25014386924409131449/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34661124056356680187/34670000000000000000 : ℝ)*(X 1 0+X 2 0)+(7182609051/5417187500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (11281/100000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (34661124056356680187/34670000000000000000 : ℝ)) (alpha := (7182609051/5417187500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34661124056356680187/34670000000000000000 : ℝ)*(X 0 1+X 2 1)+(7182609051/5417187500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (11281/100000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (34661124056356680187/34670000000000000000 : ℝ)) (alpha := (7182609051/5417187500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34661124056356680187/34670000000000000000 : ℝ)*(X 0 2+X 1 2)+(7182609051/5417187500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (11281/100000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (34661124056356680187/34670000000000000000 : ℝ)) (alpha := (7182609051/5417187500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-996210657/5000000000 : ℝ)*X 0 0+(5409565173/10000000000 : ℝ)*X 0 1+(5246290767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336965559/2500000000 : ℝ)*X 1 0+(-518891313/2500000000 : ℝ)*X 1 1+(5246290829/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347862229/10000000000 : ℝ)*X 2 0+(655786351/1250000000 : ℝ)*X 2 1+(-2075565289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4310917527/10000000000 : ℝ)*X 0 0+(82784373/200000000 : ℝ)*X 0 1+(897814741/2000000000 : ℝ)*X 0 2+(4310917527/10000000000 : ℝ)*X 1 0+(82784373/200000000 : ℝ)*X 1 1+(897814741/2000000000 : ℝ)*X 1 2+(4310917527/10000000000 : ℝ)*X 2 0+(82784373/200000000 : ℝ)*X 2 1+(897814741/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1992432943/10000000000 : ℝ)*X 0 0+(2623439191/5000000000 : ℝ)*X 0 1+(216358979/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305525961/10000000000 : ℝ)*X 1 0+(-1912881503/10000000000 : ℝ)*X 1 1+(338060907/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212221023/400000000 : ℝ)*X 2 0+(2704487393/5000000000 : ℝ)*X 2 1+(-956440827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4310942327/10000000000 : ℝ)*X 0 0+(4487814693/10000000000 : ℝ)*X 0 1+(2070242079/5000000000 : ℝ)*X 0 2+(4310942327/10000000000 : ℝ)*X 1 0+(4487814693/10000000000 : ℝ)*X 1 1+(2070242079/5000000000 : ℝ)*X 1 2+(4310942327/10000000000 : ℝ)*X 2 0+(4487814693/10000000000 : ℝ)*X 2 1+(2070242079/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1258671230157920243298697047/108343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2170752207/100000000000000 : ℝ)*(base19) + (1014195547/50000000000000 : ℝ)*(base23) + (14369087/20000000000000 : ℝ)*(lower2) + (40615627/12500000000000 : ℝ)*(upper3) + (22340251/12500000000000 : ℝ)*(upper5) + (561445271252927/12500000000000 : ℝ)*(major0) + (561445271252927/12500000000000 : ℝ)*(major1) + (561445271252927/12500000000000 : ℝ)*(major2) + (3062354057402459/50000000000000 : ℝ)*(sp0) + (3062375868016813/50000000000000 : ℝ)*(sp1) + (3062375939197369/50000000000000 : ℝ)*(sp2) + (714586720508599/25000000000000 : ℝ)*(sp3) + (9158396183/20000000000000 : ℝ)*(sp4) + (2895497547/12500000000000 : ℝ)*(sp7) + (714592511503693/25000000000000 : ℝ)*(f.failure) + (6124753906785833/100000000000000 : ℝ)*(f.sum) + (22149275916421/17335000000000000000000000000 : ℝ)*base66 + (569547373336457349/433375000000000000000000000000000 : ℝ)*base67 + (4038757393322167651/433375000000000000000000000000000 : ℝ)*base70 + (2681081953258042651/433375000000000000000000000000000 : ℝ)*base72 + (7564175673933/2166875000000000000000000000 : ℝ)*base73 + (6070280376589792651/433375000000000000000000000000000 : ℝ)*base76 + (3370582993660792651/433375000000000000000000000000000 : ℝ)*base78 + (1940980116328542651/433375000000000000000000000000000 : ℝ)*base80 + (44240503921843/8667500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (12116819/2500000000000000000000 : ℝ)*base89 + (12116819/2500000000000000000000 : ℝ)*base91 + (12116819/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3117444714753038706273053253/866750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (693119419/100000000000000 : ℝ)*(base19) + (22506213/10000000000000 : ℝ)*(base23) + (56592669/50000000000000 : ℝ)*(lower1) + (3857327/25000000000000 : ℝ)*(upper2) + (64686077/50000000000000 : ℝ)*(upper3) + (89663787/100000000000000 : ℝ)*(upper5) + (4524132472834373/100000000000000 : ℝ)*(major0) + (4524132472834373/100000000000000 : ℝ)*(major1) + (4524132472834373/100000000000000 : ℝ)*(major2) + (6053546481/100000000000000 : ℝ)*(sp1) + (1542291868751059/25000000000000 : ℝ)*(sp4) + (192786272760573/3125000000000 : ℝ)*(sp5) + (3084583624971053/50000000000000 : ℝ)*(sp6) + (1439548675387153/50000000000000 : ℝ)*(sp7) + (1439548675387153/50000000000000 : ℝ)*(f.failure) + (1542291868751059/25000000000000 : ℝ)*(f.sum) + (67437674513141/8667500000000000000000000000 : ℝ)*base65 + (5758032927341132249/3467000000000000000000000000000000 : ℝ)*base68 + (187903174824487132249/3467000000000000000000000000000000 : ℝ)*base70 + (9032539068629132249/3467000000000000000000000000000000 : ℝ)*base72 + (31775268957371/8667500000000000000000000000 : ℝ)*base73 + (44685352631514132249/3467000000000000000000000000000000 : ℝ)*base76 + (47177265409875132249/3467000000000000000000000000000000 : ℝ)*base78 + (28610639133070867751/3467000000000000000000000000000000 : ℝ)*base79 + (2035223191481/135429687500000000000000000 : ℝ)*base82 + (6809999/5000000000000000000000 : ℝ)*base89 + (6809999/5000000000000000000000 : ℝ)*base91 + (6809999/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1403_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2257/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1403_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1403_s7_0 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-398485337/2000000000 : ℝ)*x 0 + (5409530023/10000000000 : ℝ)*x 1 + (2623161129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398485337/2000000000 : ℝ)^4363 ≤ (6074183132531/50000000000000 : ℝ)^3339 := by
    have hnat : (398485337 : ℕ)^4363*50000000000000^3339 ≤ 6074183132531^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398485337 2000000000 6074183132531 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409530023/10000000000 : ℝ)^4363 ≤ (11201218569649/25000000000000 : ℝ)^3339 := by
    have hnat : (5409530023 : ℕ)^4363*25000000000000^3339 ≤ 11201218569649^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409530023 10000000000 11201218569649 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623161129/5000000000 : ℝ)^4363 ≤ (43046759443957/100000000000000 : ℝ)^3339 := by
    have hnat : (2623161129 : ℕ)^4363*100000000000000^3339 ≤ 43046759443957^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623161129 5000000000 43046759443957 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-398485337/2000000000 : ℝ), (5409530023/10000000000 : ℝ), (2623161129/5000000000 : ℝ)] ![(6074183132531/50000000000000 : ℝ), (11201218569649/25000000000000 : ℝ), (43046759443957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-398485337/2000000000 : ℝ)|^4363 ≤ (6074183132531/50000000000000 : ℝ)^3339
        have hw : |(-398485337/2000000000 : ℝ)|=(398485337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409530023/10000000000 : ℝ)|^4363 ≤ (11201218569649/25000000000000 : ℝ)^3339
        have hw : |(5409530023/10000000000 : ℝ)|=(5409530023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623161129/5000000000 : ℝ)|^4363 ≤ (43046759443957/100000000000000 : ℝ)^3339
        have hw : |(2623161129/5000000000 : ℝ)|=(2623161129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s7_1 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336963103/2500000000 : ℝ)*x 0 + (-259442087/1250000000 : ℝ)*x 1 + (2623161099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336963103/2500000000 : ℝ)^4363 ≤ (8827705562217/20000000000000 : ℝ)^3339 := by
    have hnat : (1336963103 : ℕ)^4363*20000000000000^3339 ≤ 8827705562217^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336963103 2500000000 8827705562217 20000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259442087/1250000000 : ℝ)^4363 ≤ (1601839171281/12500000000000 : ℝ)^3339 := by
    have hnat : (259442087 : ℕ)^4363*12500000000000^3339 ≤ 1601839171281^3339*1250000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259442087 1250000000 1601839171281 12500000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623161099/5000000000 : ℝ)^4363 ≤ (43046758800669/100000000000000 : ℝ)^3339 := by
    have hnat : (2623161099 : ℕ)^4363*100000000000000^3339 ≤ 43046758800669^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623161099 5000000000 43046758800669 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336963103/2500000000 : ℝ), (-259442087/1250000000 : ℝ), (2623161099/5000000000 : ℝ)] ![(8827705562217/20000000000000 : ℝ), (1601839171281/12500000000000 : ℝ), (43046758800669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336963103/2500000000 : ℝ)|^4363 ≤ (8827705562217/20000000000000 : ℝ)^3339
        have hw : |(1336963103/2500000000 : ℝ)|=(1336963103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-259442087/1250000000 : ℝ)|^4363 ≤ (1601839171281/12500000000000 : ℝ)^3339
        have hw : |(-259442087/1250000000 : ℝ)|=(259442087/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623161099/5000000000 : ℝ)|^4363 ≤ (43046758800669/100000000000000 : ℝ)^3339
        have hw : |(2623161099/5000000000 : ℝ)|=(2623161099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s7_2 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347852827/10000000000 : ℝ)*x 0 + (20985287/40000000 : ℝ)*x 1 + (-2075536737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347852827/10000000000 : ℝ)^4363 ≤ (22069266143363/50000000000000 : ℝ)^3339 := by
    have hnat : (5347852827 : ℕ)^4363*50000000000000^3339 ≤ 22069266143363^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347852827 10000000000 22069266143363 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20985287/40000000 : ℝ)^4363 ≤ (43046753997451/100000000000000 : ℝ)^3339 := by
    have hnat : (20985287 : ℕ)^4363*100000000000000^3339 ≤ 43046753997451^3339*40000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20985287 40000000 43046753997451 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2075536737/10000000000 : ℝ)^4363 ≤ (6407356850511/50000000000000 : ℝ)^3339 := by
    have hnat : (2075536737 : ℕ)^4363*50000000000000^3339 ≤ 6407356850511^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075536737 10000000000 6407356850511 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347852827/10000000000 : ℝ), (20985287/40000000 : ℝ), (-2075536737/10000000000 : ℝ)] ![(22069266143363/50000000000000 : ℝ), (43046753997451/100000000000000 : ℝ), (6407356850511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347852827/10000000000 : ℝ)|^4363 ≤ (22069266143363/50000000000000 : ℝ)^3339
        have hw : |(5347852827/10000000000 : ℝ)|=(5347852827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20985287/40000000 : ℝ)|^4363 ≤ (43046753997451/100000000000000 : ℝ)^3339
        have hw : |(20985287/40000000 : ℝ)|=(20985287/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2075536737/10000000000 : ℝ)|^4363 ≤ (6407356850511/50000000000000 : ℝ)^3339
        have hw : |(-2075536737/10000000000 : ℝ)|=(2075536737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s7_3 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4310919939/10000000000 : ℝ)*x 0 + (2069644529/5000000000 : ℝ)*x 1 + (1122250661/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310919939/10000000000 : ℝ)^4363 ≤ (8326076085153/25000000000000 : ℝ)^3339 := by
    have hnat : (4310919939 : ℕ)^4363*25000000000000^3339 ≤ 8326076085153^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310919939 10000000000 8326076085153 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069644529/5000000000 : ℝ)^4363 ≤ (3158239527257/10000000000000 : ℝ)^3339 := by
    have hnat : (2069644529 : ℕ)^4363*10000000000000^3339 ≤ 3158239527257^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069644529 5000000000 3158239527257 10000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122250661/2500000000 : ℝ)^4363 ≤ (17145166193/48828125000 : ℝ)^3339 := by
    have hnat : (1122250661 : ℕ)^4363*48828125000^3339 ≤ 17145166193^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122250661 2500000000 17145166193 48828125000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310919939/10000000000 : ℝ), (2069644529/5000000000 : ℝ), (1122250661/2500000000 : ℝ)] ![(8326076085153/25000000000000 : ℝ), (3158239527257/10000000000000 : ℝ), (17145166193/48828125000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310919939/10000000000 : ℝ)|^4363 ≤ (8326076085153/25000000000000 : ℝ)^3339
        have hw : |(4310919939/10000000000 : ℝ)|=(4310919939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2069644529/5000000000 : ℝ)|^4363 ≤ (3158239527257/10000000000000 : ℝ)^3339
        have hw : |(2069644529/5000000000 : ℝ)|=(2069644529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122250661/2500000000 : ℝ)|^4363 ≤ (17145166193/48828125000 : ℝ)^3339
        have hw : |(1122250661/2500000000 : ℝ)|=(1122250661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s7_4 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1992438437/10000000000 : ℝ)*x 0 + (1049381791/2000000000 : ℝ)*x 1 + (5408940141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1992438437/10000000000 : ℝ)^4363 ≤ (607422994769/5000000000000 : ℝ)^3339 := by
    have hnat : (1992438437 : ℕ)^4363*5000000000000^3339 ≤ 607422994769^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992438437 10000000000 607422994769 5000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049381791/2000000000 : ℝ)^4363 ≤ (21526524902753/50000000000000 : ℝ)^3339 := by
    have hnat : (1049381791 : ℕ)^4363*50000000000000^3339 ≤ 21526524902753^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049381791 2000000000 21526524902753 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408940141/10000000000 : ℝ)^4363 ≤ (5599811285697/12500000000000 : ℝ)^3339 := by
    have hnat : (5408940141 : ℕ)^4363*12500000000000^3339 ≤ 5599811285697^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408940141 10000000000 5599811285697 12500000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1992438437/10000000000 : ℝ), (1049381791/2000000000 : ℝ), (5408940141/10000000000 : ℝ)] ![(607422994769/5000000000000 : ℝ), (21526524902753/50000000000000 : ℝ), (5599811285697/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1992438437/10000000000 : ℝ)|^4363 ≤ (607422994769/5000000000000 : ℝ)^3339
        have hw : |(-1992438437/10000000000 : ℝ)|=(1992438437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049381791/2000000000 : ℝ)|^4363 ≤ (21526524902753/50000000000000 : ℝ)^3339
        have hw : |(1049381791/2000000000 : ℝ)|=(1049381791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408940141/10000000000 : ℝ)|^4363 ≤ (5599811285697/12500000000000 : ℝ)^3339
        have hw : |(5408940141/10000000000 : ℝ)|=(5408940141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_s7_5 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (862188849/2000000000 : ℝ)*x 0 + (4487745007/10000000000 : ℝ)*x 1 + (828110729/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862188849/2000000000 : ℝ)^4363 ≤ (33304549705871/100000000000000 : ℝ)^3339 := by
    have hnat : (862188849 : ℕ)^4363*100000000000000^3339 ≤ 33304549705871^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862188849 2000000000 33304549705871 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487745007/10000000000 : ℝ)^4363 ≤ (4387555836341/12500000000000 : ℝ)^3339 := by
    have hnat : (4487745007 : ℕ)^4363*12500000000000^3339 ≤ 4387555836341^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487745007 10000000000 4387555836341 12500000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (828110729/2000000000 : ℝ)^4363 ≤ (31595003590731/100000000000000 : ℝ)^3339 := by
    have hnat : (828110729 : ℕ)^4363*100000000000000^3339 ≤ 31595003590731^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828110729 2000000000 31595003590731 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862188849/2000000000 : ℝ), (4487745007/10000000000 : ℝ), (828110729/2000000000 : ℝ)] ![(33304549705871/100000000000000 : ℝ), (4387555836341/12500000000000 : ℝ), (31595003590731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862188849/2000000000 : ℝ)|^4363 ≤ (33304549705871/100000000000000 : ℝ)^3339
        have hw : |(862188849/2000000000 : ℝ)|=(862188849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487745007/10000000000 : ℝ)|^4363 ≤ (4387555836341/12500000000000 : ℝ)^3339
        have hw : |(4487745007/10000000000 : ℝ)|=(4487745007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(828110729/2000000000 : ℝ)|^4363 ≤ (31595003590731/100000000000000 : ℝ)^3339
        have hw : |(828110729/2000000000 : ℝ)|=(828110729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1403_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2257/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5643/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14743/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2257/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2257/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2257/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2257/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2257/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2257/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2257/20000 : ℝ) ^ (2181/512 : ℝ) ≤ (9201925865519151/100000000000000000000 : ℝ) := by
    have hpowers : (2257/20000 : ℝ)^2181 ≤ (9201925865519151/100000000000000000000 : ℝ)^512 := by
      have hnat : (2257 : ℕ)^2181*100000000000000000000^512 ≤ 9201925865519151^512*20000^2181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2257 20000 9201925865519151 100000000000000000000 2181 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2257/20000 : ℝ)) (X := (9201925865519151/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14743/100000 : ℝ) ^ (2181/512 : ℝ) ≤ (2873231703766959/10000000000000000000 : ℝ) := by
    have hpowers : (14743/100000 : ℝ)^2181 ≤ (2873231703766959/10000000000000000000 : ℝ)^512 := by
      have hnat : (14743 : ℕ)^2181*10000000000000000000^512 ≤ 2873231703766959^512*100000^2181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14743 100000 2873231703766959 10000000000000000000 2181 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14743/100000 : ℝ)) (X := (2873231703766959/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009201925865519151/50000000000000000000 : ℝ) ≤ (10000432008648873/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (50009201925865519151/50000000000000000000 : ℝ)^512 ≤ (10000432008648873/10000000000000000 : ℝ)^2181 := by
      have hnat : (50009201925865519151 : ℕ)^512*10000000000000000^2181 ≤ 10000432008648873^2181*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009201925865519151 50000000000000000000 10000432008648873 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000432008648873/10000000000000000 : ℝ)) (X := (50009201925865519151/50000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037934242903188741/100000000000000000000 : ℝ) ≤ (1250111299369217/1250000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (100037934242903188741/100000000000000000000 : ℝ)^512 ≤ (1250111299369217/1250000000000000 : ℝ)^2181 := by
      have hnat : (100037934242903188741 : ℕ)^512*1250000000000000^2181 ≤ 1250111299369217^2181*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037934242903188741 100000000000000000000 1250111299369217 1250000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250111299369217/1250000000000000 : ℝ)) (X := (100037934242903188741/100000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002873231703766959/5000000000000000000 : ℝ) ≤ (10001348781258599/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (5002873231703766959/5000000000000000000 : ℝ)^512 ≤ (10001348781258599/10000000000000000 : ℝ)^2181 := by
      have hnat : (5002873231703766959 : ℕ)^512*10000000000000000^2181 ≤ 10001348781258599^2181*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002873231703766959 5000000000000000000 10001348781258599 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001348781258599/10000000000000000 : ℝ)) (X := (5002873231703766959/5000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9201925865519151/100000000000000000000 : ℝ) ≤ ((8642787026751761231/8645000000000000000 : ℝ)+2*(458386304863/345800000000000 : ℝ)*(2257/20000 : ℝ))^(2181/512 : ℝ) := by
    rw [show (8642787026751761231/8645000000000000000 : ℝ)+2*(458386304863/345800000000000 : ℝ)*(2257/20000 : ℝ)=(10000432008648873/10000000000000000 : ℝ) by norm_num, show 1+2*(9201925865519151/100000000000000000000 : ℝ)=(50009201925865519151/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2873231703766959/10000000000000000000 : ℝ)+(9201925865519151/100000000000000000000 : ℝ) ≤ ((8642787026751761231/8645000000000000000 : ℝ)+(458386304863/345800000000000 : ℝ)*((14743/100000 : ℝ)+(2257/20000 : ℝ)))^(2181/512 : ℝ) := by
    rw [show (8642787026751761231/8645000000000000000 : ℝ)+(458386304863/345800000000000 : ℝ)*((14743/100000 : ℝ)+(2257/20000 : ℝ))=(1250111299369217/1250000000000000 : ℝ) by norm_num, show 1+(2873231703766959/10000000000000000000 : ℝ)+(9201925865519151/100000000000000000000 : ℝ)=(100037934242903188741/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2873231703766959/10000000000000000000 : ℝ) ≤ ((8642787026751761231/8645000000000000000 : ℝ)+2*(458386304863/345800000000000 : ℝ)*(14743/100000 : ℝ))^(2181/512 : ℝ) := by
    rw [show (8642787026751761231/8645000000000000000 : ℝ)+2*(458386304863/345800000000000 : ℝ)*(14743/100000 : ℝ)=(10001348781258599/10000000000000000 : ℝ) by norm_num, show 1+2*(2873231703766959/10000000000000000000 : ℝ)=(5002873231703766959/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8642787026751761231/8645000000000000000 : ℝ)*(X 1 0+X 2 0)+(458386304863/345800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (2257/20000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (8642787026751761231/8645000000000000000 : ℝ)) (alpha := (458386304863/345800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8642787026751761231/8645000000000000000 : ℝ)*(X 0 1+X 2 1)+(458386304863/345800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (2257/20000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (8642787026751761231/8645000000000000000 : ℝ)) (alpha := (458386304863/345800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8642787026751761231/8645000000000000000 : ℝ)*(X 0 2+X 1 2)+(458386304863/345800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (2257/20000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (8642787026751761231/8645000000000000000 : ℝ)) (alpha := (458386304863/345800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-398485337/2000000000 : ℝ)*X 0 0+(5409530023/10000000000 : ℝ)*X 0 1+(2623161129/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336963103/2500000000 : ℝ)*X 1 0+(-259442087/1250000000 : ℝ)*X 1 1+(2623161099/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347852827/10000000000 : ℝ)*X 2 0+(20985287/40000000 : ℝ)*X 2 1+(-2075536737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4310919939/10000000000 : ℝ)*X 0 0+(2069644529/5000000000 : ℝ)*X 0 1+(1122250661/2500000000 : ℝ)*X 0 2+(4310919939/10000000000 : ℝ)*X 1 0+(2069644529/5000000000 : ℝ)*X 1 1+(1122250661/2500000000 : ℝ)*X 1 2+(4310919939/10000000000 : ℝ)*X 2 0+(2069644529/5000000000 : ℝ)*X 2 1+(1122250661/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1992438437/10000000000 : ℝ)*X 0 0+(1049381791/2000000000 : ℝ)*X 0 1+(5408940141/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((862188849/2000000000 : ℝ)*X 0 0+(4487745007/10000000000 : ℝ)*X 0 1+(828110729/2000000000 : ℝ)*X 0 2+(862188849/2000000000 : ℝ)*X 1 0+(4487745007/10000000000 : ℝ)*X 1 1+(828110729/2000000000 : ℝ)*X 1 2+(862188849/2000000000 : ℝ)*X 2 0+(4487745007/10000000000 : ℝ)*X 2 1+(828110729/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (596597096553433748304808467/61750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (566579353/50000000000000 : ℝ)*(base19) + (1181754813/100000000000000 : ℝ)*(base23) + (29770799/12500000000000 : ℝ)*(lower2) + (282287227/100000000000000 : ℝ)*(upper3) + (9876609/100000000000000 : ℝ)*(lower4) + (4493347343000611/100000000000000 : ℝ)*(major0) + (4493347343000611/100000000000000 : ℝ)*(major1) + (4493347343000611/100000000000000 : ℝ)*(major2) + (245086990106661/4000000000000 : ℝ)*(sp0) + (3063593562294823/50000000000000 : ℝ)*(sp1) + (306359353799677/5000000000000 : ℝ)*(sp2) + (714872649727329/25000000000000 : ℝ)*(sp3) + (13505081827/100000000000000 : ℝ)*(sp4) + (1550729383/10000000000000 : ℝ)*(sp5) + (1429753053101573/50000000000000 : ℝ)*(f.failure) + (47868658263659/781250000000 : ℝ)*(f.sum) + (44095007166793/17290000000000000000000000000 : ℝ)*base65 + (9967000735929562859/864500000000000000000000000000000 : ℝ)*base68 + (11338236845218062859/864500000000000000000000000000000 : ℝ)*base70 + (4537140406035562859/864500000000000000000000000000000 : ℝ)*base72 + (28596742844087/17290000000000000000000000000 : ℝ)*base74 + (15610449615907562859/864500000000000000000000000000000 : ℝ)*base76 + (7866685585541562859/864500000000000000000000000000000 : ℝ)*base78 + (9424833139959562859/864500000000000000000000000000000 : ℝ)*base80 + (28341565820167/17290000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (44088859/5000000000000000000000 : ℝ)*base89 + (44088859/5000000000000000000000 : ℝ)*base91 + (44088859/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1403_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2257/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1403_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1403_box_0 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-914927157/5000000000 : ℝ)*x 0 + (43098949/80000000 : ℝ)*x 1 + (5387368133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (914927157/5000000000 : ℝ)^4363 ≤ (2173929244931/20000000000000 : ℝ)^3339 := by
    have hnat : (914927157 : ℕ)^4363*20000000000000^3339 ≤ 2173929244931^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914927157 5000000000 2173929244931 20000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43098949/80000000 : ℝ)^4363 ≤ (8913035906951/20000000000000 : ℝ)^3339 := by
    have hnat : (43098949 : ℕ)^4363*20000000000000^3339 ≤ 8913035906951^3339*80000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43098949 80000000 8913035906951 20000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387368133/10000000000 : ℝ)^4363 ≤ (44565174216699/100000000000000 : ℝ)^3339 := by
    have hnat : (5387368133 : ℕ)^4363*100000000000000^3339 ≤ 44565174216699^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387368133 10000000000 44565174216699 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-914927157/5000000000 : ℝ), (43098949/80000000 : ℝ), (5387368133/10000000000 : ℝ)] ![(2173929244931/20000000000000 : ℝ), (8913035906951/20000000000000 : ℝ), (44565174216699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-914927157/5000000000 : ℝ)|^4363 ≤ (2173929244931/20000000000000 : ℝ)^3339
        have hw : |(-914927157/5000000000 : ℝ)|=(914927157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43098949/80000000 : ℝ)|^4363 ≤ (8913035906951/20000000000000 : ℝ)^3339
        have hw : |(43098949/80000000 : ℝ)|=(43098949/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387368133/10000000000 : ℝ)|^4363 ≤ (44565174216699/100000000000000 : ℝ)^3339
        have hw : |(5387368133/10000000000 : ℝ)|=(5387368133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_box_1 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285854543/10000000000 : ℝ)*x 0 + (-1969211057/10000000000 : ℝ)*x 1 + (1346842001/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285854543/10000000000 : ℝ)^4363 ≤ (21735546245617/50000000000000 : ℝ)^3339 := by
    have hnat : (5285854543 : ℕ)^4363*50000000000000^3339 ≤ 21735546245617^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285854543 10000000000 21735546245617 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1969211057/10000000000 : ℝ)^4363 ≤ (11963734676697/100000000000000 : ℝ)^3339 := by
    have hnat : (1969211057 : ℕ)^4363*100000000000000^3339 ≤ 11963734676697^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1969211057 10000000000 11963734676697 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346842001/2500000000 : ℝ)^4363 ≤ (44565172822331/100000000000000 : ℝ)^3339 := by
    have hnat : (1346842001 : ℕ)^4363*100000000000000^3339 ≤ 44565172822331^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346842001 2500000000 44565172822331 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285854543/10000000000 : ℝ), (-1969211057/10000000000 : ℝ), (1346842001/2500000000 : ℝ)] ![(21735546245617/50000000000000 : ℝ), (11963734676697/100000000000000 : ℝ), (44565172822331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285854543/10000000000 : ℝ)|^4363 ≤ (21735546245617/50000000000000 : ℝ)^3339
        have hw : |(5285854543/10000000000 : ℝ)|=(5285854543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1969211057/10000000000 : ℝ)|^4363 ≤ (11963734676697/100000000000000 : ℝ)^3339
        have hw : |(-1969211057/10000000000 : ℝ)|=(1969211057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346842001/2500000000 : ℝ)|^4363 ≤ (44565172822331/100000000000000 : ℝ)^3339
        have hw : |(1346842001/2500000000 : ℝ)|=(1346842001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_box_2 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057170979/2000000000 : ℝ)*x 0 + (1346842041/2500000000 : ℝ)*x 1 + (-984605181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057170979/2000000000 : ℝ)^4363 ≤ (43471096273889/100000000000000 : ℝ)^3339 := by
    have hnat : (1057170979 : ℕ)^4363*100000000000000^3339 ≤ 43471096273889^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057170979 2000000000 43471096273889 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346842041/2500000000 : ℝ)^4363 ≤ (2228258727589/5000000000000 : ℝ)^3339 := by
    have hnat : (1346842041 : ℕ)^4363*5000000000000^3339 ≤ 2228258727589^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346842041 2500000000 2228258727589 5000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (984605181/5000000000 : ℝ)^4363 ≤ (5981864579689/50000000000000 : ℝ)^3339 := by
    have hnat : (984605181 : ℕ)^4363*50000000000000^3339 ≤ 5981864579689^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984605181 5000000000 5981864579689 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057170979/2000000000 : ℝ), (1346842041/2500000000 : ℝ), (-984605181/5000000000 : ℝ)] ![(43471096273889/100000000000000 : ℝ), (2228258727589/5000000000000 : ℝ), (5981864579689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057170979/2000000000 : ℝ)|^4363 ≤ (43471096273889/100000000000000 : ℝ)^3339
        have hw : |(1057170979/2000000000 : ℝ)|=(1057170979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346842041/2500000000 : ℝ)|^4363 ≤ (2228258727589/5000000000000 : ℝ)^3339
        have hw : |(1346842041/2500000000 : ℝ)|=(1346842041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-984605181/5000000000 : ℝ)|^4363 ≤ (5981864579689/50000000000000 : ℝ)^3339
        have hw : |(-984605181/5000000000 : ℝ)|=(984605181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_box_3 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (891550753/2000000000 : ℝ)*x 0 + (212063139/500000000 : ℝ)*x 1 + (2120631367/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (891550753/2000000000 : ℝ)^4363 ≤ (34794249111661/100000000000000 : ℝ)^3339 := by
    have hnat : (891550753 : ℕ)^4363*100000000000000^3339 ≤ 34794249111661^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891550753 2000000000 34794249111661 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212063139/500000000 : ℝ)^4363 ≤ (32602875665411/100000000000000 : ℝ)^3339 := by
    have hnat : (212063139 : ℕ)^4363*100000000000000^3339 ≤ 32602875665411^3339*500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212063139 500000000 32602875665411 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2120631367/5000000000 : ℝ)^4363 ≤ (16301437601681/50000000000000 : ℝ)^3339 := by
    have hnat : (2120631367 : ℕ)^4363*50000000000000^3339 ≤ 16301437601681^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120631367 5000000000 16301437601681 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(891550753/2000000000 : ℝ), (212063139/500000000 : ℝ), (2120631367/5000000000 : ℝ)] ![(34794249111661/100000000000000 : ℝ), (32602875665411/100000000000000 : ℝ), (16301437601681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(891550753/2000000000 : ℝ)|^4363 ≤ (34794249111661/100000000000000 : ℝ)^3339
        have hw : |(891550753/2000000000 : ℝ)|=(891550753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(212063139/500000000 : ℝ)|^4363 ≤ (32602875665411/100000000000000 : ℝ)^3339
        have hw : |(212063139/500000000 : ℝ)|=(212063139/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2120631367/5000000000 : ℝ)|^4363 ≤ (16301437601681/50000000000000 : ℝ)^3339
        have hw : |(2120631367/5000000000 : ℝ)|=(2120631367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_box_4 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-539433513/2500000000 : ℝ)*x 0 + (2633056989/5000000000 : ℝ)*x 1 + (5266113903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539433513/2500000000 : ℝ)^4363 ≤ (3370461000643/25000000000000 : ℝ)^3339 := by
    have hnat : (539433513 : ℕ)^4363*25000000000000^3339 ≤ 3370461000643^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539433513 2500000000 3370461000643 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633056989/5000000000 : ℝ)^4363 ≤ (21629539199373/50000000000000 : ℝ)^3339 := by
    have hnat : (2633056989 : ℕ)^4363*50000000000000^3339 ≤ 21629539199373^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633056989 5000000000 21629539199373 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266113903/10000000000 : ℝ)^4363 ≤ (43259077593707/100000000000000 : ℝ)^3339 := by
    have hnat : (5266113903 : ℕ)^4363*100000000000000^3339 ≤ 43259077593707^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266113903 10000000000 43259077593707 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-539433513/2500000000 : ℝ), (2633056989/5000000000 : ℝ), (5266113903/10000000000 : ℝ)] ![(3370461000643/25000000000000 : ℝ), (21629539199373/50000000000000 : ℝ), (43259077593707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-539433513/2500000000 : ℝ)|^4363 ≤ (3370461000643/25000000000000 : ℝ)^3339
        have hw : |(-539433513/2500000000 : ℝ)|=(539433513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633056989/5000000000 : ℝ)|^4363 ≤ (21629539199373/50000000000000 : ℝ)^3339
        have hw : |(2633056989/5000000000 : ℝ)|=(2633056989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266113903/10000000000 : ℝ)|^4363 ≤ (43259077593707/100000000000000 : ℝ)^3339
        have hw : |(5266113903/10000000000 : ℝ)|=(5266113903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_box_5 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2685402237/5000000000 : ℝ)*x 0 + (-403654619/2000000000 : ℝ)*x 1 + (658264281/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685402237/5000000000 : ℝ)^4363 ≤ (22193110586479/50000000000000 : ℝ)^3339 := by
    have hnat : (2685402237 : ℕ)^4363*50000000000000^3339 ≤ 22193110586479^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685402237 5000000000 22193110586479 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403654619/2000000000 : ℝ)^4363 ≤ (1235469751373/10000000000000 : ℝ)^3339 := by
    have hnat : (403654619 : ℕ)^4363*10000000000000^3339 ≤ 1235469751373^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403654619 2000000000 1235469751373 10000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658264281/1250000000 : ℝ)^4363 ≤ (5407385162111/12500000000000 : ℝ)^3339 := by
    have hnat : (658264281 : ℕ)^4363*12500000000000^3339 ≤ 5407385162111^3339*1250000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658264281 1250000000 5407385162111 12500000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685402237/5000000000 : ℝ), (-403654619/2000000000 : ℝ), (658264281/1250000000 : ℝ)] ![(22193110586479/50000000000000 : ℝ), (1235469751373/10000000000000 : ℝ), (5407385162111/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685402237/5000000000 : ℝ)|^4363 ≤ (22193110586479/50000000000000 : ℝ)^3339
        have hw : |(2685402237/5000000000 : ℝ)|=(2685402237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-403654619/2000000000 : ℝ)|^4363 ≤ (1235469751373/10000000000000 : ℝ)^3339
        have hw : |(-403654619/2000000000 : ℝ)|=(403654619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658264281/1250000000 : ℝ)|^4363 ≤ (5407385162111/12500000000000 : ℝ)^3339
        have hw : |(658264281/1250000000 : ℝ)|=(658264281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_box_6 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370804641/10000000000 : ℝ)*x 0 + (5266113839/10000000000 : ℝ)*x 1 + (-1009136709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370804641/10000000000 : ℝ)^4363 ≤ (22193111488183/50000000000000 : ℝ)^3339 := by
    have hnat : (5370804641 : ℕ)^4363*50000000000000^3339 ≤ 22193111488183^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370804641 10000000000 22193111488183 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266113839/10000000000 : ℝ)^4363 ≤ (2162953845337/5000000000000 : ℝ)^3339 := by
    have hnat : (5266113839 : ℕ)^4363*5000000000000^3339 ≤ 2162953845337^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266113839 10000000000 2162953845337 5000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1009136709/5000000000 : ℝ)^4363 ≤ (12354700097319/100000000000000 : ℝ)^3339 := by
    have hnat : (1009136709 : ℕ)^4363*100000000000000^3339 ≤ 12354700097319^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009136709 5000000000 12354700097319 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370804641/10000000000 : ℝ), (5266113839/10000000000 : ℝ), (-1009136709/5000000000 : ℝ)] ![(22193111488183/50000000000000 : ℝ), (2162953845337/5000000000000 : ℝ), (12354700097319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370804641/10000000000 : ℝ)|^4363 ≤ (22193111488183/50000000000000 : ℝ)^3339
        have hw : |(5370804641/10000000000 : ℝ)|=(5370804641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266113839/10000000000 : ℝ)|^4363 ≤ (2162953845337/5000000000000 : ℝ)^3339
        have hw : |(5266113839/10000000000 : ℝ)|=(5266113839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1009136709/5000000000 : ℝ)|^4363 ≤ (12354700097319/100000000000000 : ℝ)^3339
        have hw : |(-1009136709/5000000000 : ℝ)|=(1009136709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_box_7 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2081536147/5000000000 : ℝ)*x 0 + (4388551877/10000000000 : ℝ)*x 1 + (2194275893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2081536147/5000000000 : ℝ)^4363 ≤ (6363943783217/20000000000000 : ℝ)^3339 := by
    have hnat : (2081536147 : ℕ)^4363*20000000000000^3339 ≤ 6363943783217^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081536147 5000000000 6363943783217 20000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4388551877/10000000000 : ℝ)^4363 ≤ (34090140999869/100000000000000 : ℝ)^3339 := by
    have hnat : (4388551877 : ℕ)^4363*100000000000000^3339 ≤ 34090140999869^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4388551877 10000000000 34090140999869 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2194275893/5000000000 : ℝ)^4363 ≤ (34090140076197/100000000000000 : ℝ)^3339 := by
    have hnat : (2194275893 : ℕ)^4363*100000000000000^3339 ≤ 34090140076197^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194275893 5000000000 34090140076197 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2081536147/5000000000 : ℝ), (4388551877/10000000000 : ℝ), (2194275893/5000000000 : ℝ)] ![(6363943783217/20000000000000 : ℝ), (34090140999869/100000000000000 : ℝ), (34090140076197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2081536147/5000000000 : ℝ)|^4363 ≤ (6363943783217/20000000000000 : ℝ)^3339
        have hw : |(2081536147/5000000000 : ℝ)|=(2081536147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4388551877/10000000000 : ℝ)|^4363 ≤ (34090140999869/100000000000000 : ℝ)^3339
        have hw : |(4388551877/10000000000 : ℝ)|=(4388551877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2194275893/5000000000 : ℝ)|^4363 ≤ (34090140076197/100000000000000 : ℝ)^3339
        have hw : |(2194275893/5000000000 : ℝ)|=(2194275893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_box_8 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1044365779/5000000000 : ℝ)*x 0 + (1295590157/2500000000 : ℝ)*x 1 + (5401357751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044365779/5000000000 : ℝ)^4363 ≤ (12921268573857/100000000000000 : ℝ)^3339 := by
    have hnat : (1044365779 : ℕ)^4363*100000000000000^3339 ≤ 12921268573857^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044365779 5000000000 12921268573857 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295590157/2500000000 : ℝ)^4363 ≤ (21181141227161/50000000000000 : ℝ)^3339 := by
    have hnat : (1295590157 : ℕ)^4363*50000000000000^3339 ≤ 21181141227161^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295590157 2500000000 21181141227161 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401357751/10000000000 : ℝ)^4363 ≤ (2235822447501/5000000000000 : ℝ)^3339 := by
    have hnat : (5401357751 : ℕ)^4363*5000000000000^3339 ≤ 2235822447501^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401357751 10000000000 2235822447501 5000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1044365779/5000000000 : ℝ), (1295590157/2500000000 : ℝ), (5401357751/10000000000 : ℝ)] ![(12921268573857/100000000000000 : ℝ), (21181141227161/50000000000000 : ℝ), (2235822447501/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1044365779/5000000000 : ℝ)|^4363 ≤ (12921268573857/100000000000000 : ℝ)^3339
        have hw : |(-1044365779/5000000000 : ℝ)|=(1044365779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295590157/2500000000 : ℝ)|^4363 ≤ (21181141227161/50000000000000 : ℝ)^3339
        have hw : |(1295590157/2500000000 : ℝ)|=(1295590157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401357751/10000000000 : ℝ)|^4363 ≤ (2235822447501/5000000000000 : ℝ)^3339
        have hw : |(5401357751/10000000000 : ℝ)|=(5401357751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_box_9 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276049073/10000000000 : ℝ)*x 0 + (-1963422027/10000000000 : ℝ)*x 1 + (1080271573/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276049073/10000000000 : ℝ)^4363 ≤ (43365751124161/100000000000000 : ℝ)^3339 := by
    have hnat : (5276049073 : ℕ)^4363*100000000000000^3339 ≤ 43365751124161^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276049073 10000000000 43365751124161 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1963422027/10000000000 : ℝ)^4363 ≤ (1489724834897/12500000000000 : ℝ)^3339 := by
    have hnat : (1963422027 : ℕ)^4363*12500000000000^3339 ≤ 1489724834897^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963422027 10000000000 1489724834897 12500000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080271573/2000000000 : ℝ)^4363 ≤ (44716450183233/100000000000000 : ℝ)^3339 := by
    have hnat : (1080271573 : ℕ)^4363*100000000000000^3339 ≤ 44716450183233^3339*2000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080271573 2000000000 44716450183233 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276049073/10000000000 : ℝ), (-1963422027/10000000000 : ℝ), (1080271573/2000000000 : ℝ)] ![(43365751124161/100000000000000 : ℝ), (1489724834897/12500000000000 : ℝ), (44716450183233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276049073/10000000000 : ℝ)|^4363 ≤ (43365751124161/100000000000000 : ℝ)^3339
        have hw : |(5276049073/10000000000 : ℝ)|=(5276049073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1963422027/10000000000 : ℝ)|^4363 ≤ (1489724834897/12500000000000 : ℝ)^3339
        have hw : |(-1963422027/10000000000 : ℝ)|=(1963422027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080271573/2000000000 : ℝ)|^4363 ≤ (44716450183233/100000000000000 : ℝ)^3339
        have hw : |(1080271573/2000000000 : ℝ)|=(1080271573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_box_10 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276048471/10000000000 : ℝ)*x 0 + (5401358547/10000000000 : ℝ)*x 1 + (-245427739/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276048471/10000000000 : ℝ)^4363 ≤ (43365744658643/100000000000000 : ℝ)^3339 := by
    have hnat : (5276048471 : ℕ)^4363*100000000000000^3339 ≤ 43365744658643^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276048471 10000000000 43365744658643 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401358547/10000000000 : ℝ)^4363 ≤ (22358228780437/50000000000000 : ℝ)^3339 := by
    have hnat : (5401358547 : ℕ)^4363*50000000000000^3339 ≤ 22358228780437^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401358547 10000000000 22358228780437 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245427739/1250000000 : ℝ)^4363 ≤ (5958898883531/50000000000000 : ℝ)^3339 := by
    have hnat : (245427739 : ℕ)^4363*50000000000000^3339 ≤ 5958898883531^3339*1250000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245427739 1250000000 5958898883531 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276048471/10000000000 : ℝ), (5401358547/10000000000 : ℝ), (-245427739/1250000000 : ℝ)] ![(43365744658643/100000000000000 : ℝ), (22358228780437/50000000000000 : ℝ), (5958898883531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276048471/10000000000 : ℝ)|^4363 ≤ (43365744658643/100000000000000 : ℝ)^3339
        have hw : |(5276048471/10000000000 : ℝ)|=(5276048471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401358547/10000000000 : ℝ)|^4363 ≤ (22358228780437/50000000000000 : ℝ)^3339
        have hw : |(5401358547/10000000000 : ℝ)|=(5401358547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-245427739/1250000000 : ℝ)|^4363 ≤ (5958898883531/50000000000000 : ℝ)^3339
        have hw : |(-245427739/1250000000 : ℝ)|=(245427739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_box_11 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1122798783/2500000000 : ℝ)*x 0 + (2112127941/5000000000 : ℝ)*x 1 + (4224253847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1122798783/2500000000 : ℝ)^4363 ≤ (8783927829133/25000000000000 : ℝ)^3339 := by
    have hnat : (1122798783 : ℕ)^4363*25000000000000^3339 ≤ 8783927829133^3339*2500000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122798783 2500000000 8783927829133 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112127941/5000000000 : ℝ)^4363 ≤ (3243215454099/10000000000000 : ℝ)^3339 := by
    have hnat : (2112127941 : ℕ)^4363*10000000000000^3339 ≤ 3243215454099^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112127941 5000000000 3243215454099 10000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4224253847/10000000000 : ℝ)^4363 ≤ (32432134125549/100000000000000 : ℝ)^3339 := by
    have hnat : (4224253847 : ℕ)^4363*100000000000000^3339 ≤ 32432134125549^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224253847 10000000000 32432134125549 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1122798783/2500000000 : ℝ), (2112127941/5000000000 : ℝ), (4224253847/10000000000 : ℝ)] ![(8783927829133/25000000000000 : ℝ), (3243215454099/10000000000000 : ℝ), (32432134125549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1122798783/2500000000 : ℝ)|^4363 ≤ (8783927829133/25000000000000 : ℝ)^3339
        have hw : |(1122798783/2500000000 : ℝ)|=(1122798783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2112127941/5000000000 : ℝ)|^4363 ≤ (3243215454099/10000000000000 : ℝ)^3339
        have hw : |(2112127941/5000000000 : ℝ)|=(2112127941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4224253847/10000000000 : ℝ)|^4363 ≤ (32432134125549/100000000000000 : ℝ)^3339
        have hw : |(4224253847/10000000000 : ℝ)|=(4224253847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_box_12 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-9495411/50000000 : ℝ)*x 0 + (2734523411/5000000000 : ℝ)*x 1 + (656875159/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9495411/50000000 : ℝ)^4363 ≤ (11410076103313/100000000000000 : ℝ)^3339 := by
    have hnat : (9495411 : ℕ)^4363*100000000000000^3339 ≤ 11410076103313^3339*50000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9495411 50000000 11410076103313 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734523411/5000000000 : ℝ)^4363 ≤ (22725044527119/50000000000000 : ℝ)^3339 := by
    have hnat : (2734523411 : ℕ)^4363*50000000000000^3339 ≤ 22725044527119^3339*5000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734523411 5000000000 22725044527119 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656875159/1250000000 : ℝ)^4363 ≤ (4313983481877/10000000000000 : ℝ)^3339 := by
    have hnat : (656875159 : ℕ)^4363*10000000000000^3339 ≤ 4313983481877^3339*1250000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656875159 1250000000 4313983481877 10000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9495411/50000000 : ℝ), (2734523411/5000000000 : ℝ), (656875159/1250000000 : ℝ)] ![(11410076103313/100000000000000 : ℝ), (22725044527119/50000000000000 : ℝ), (4313983481877/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9495411/50000000 : ℝ)|^4363 ≤ (11410076103313/100000000000000 : ℝ)^3339
        have hw : |(-9495411/50000000 : ℝ)|=(9495411/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734523411/5000000000 : ℝ)|^4363 ≤ (22725044527119/50000000000000 : ℝ)^3339
        have hw : |(2734523411/5000000000 : ℝ)|=(2734523411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656875159/1250000000 : ℝ)|^4363 ≤ (4313983481877/10000000000000 : ℝ)^3339
        have hw : |(656875159/1250000000 : ℝ)|=(656875159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_box_13 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378587343/10000000000 : ℝ)*x 0 + (-2022668529/10000000000 : ℝ)*x 1 + (5255002403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378587343/10000000000 : ℝ)^4363 ≤ (44470285899531/100000000000000 : ℝ)^3339 := by
    have hnat : (5378587343 : ℕ)^4363*100000000000000^3339 ≤ 44470285899531^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378587343 10000000000 44470285899531 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2022668529/10000000000 : ℝ)^4363 ≤ (12389867133797/100000000000000 : ℝ)^3339 := by
    have hnat : (2022668529 : ℕ)^4363*100000000000000^3339 ≤ 12389867133797^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022668529 10000000000 12389867133797 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255002403/10000000000 : ℝ)^4363 ≤ (431398469509/1000000000000 : ℝ)^3339 := by
    have hnat : (5255002403 : ℕ)^4363*1000000000000^3339 ≤ 431398469509^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255002403 10000000000 431398469509 1000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378587343/10000000000 : ℝ), (-2022668529/10000000000 : ℝ), (5255002403/10000000000 : ℝ)] ![(44470285899531/100000000000000 : ℝ), (12389867133797/100000000000000 : ℝ), (431398469509/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378587343/10000000000 : ℝ)|^4363 ≤ (44470285899531/100000000000000 : ℝ)^3339
        have hw : |(5378587343/10000000000 : ℝ)|=(5378587343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2022668529/10000000000 : ℝ)|^4363 ≤ (12389867133797/100000000000000 : ℝ)^3339
        have hw : |(-2022668529/10000000000 : ℝ)|=(2022668529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255002403/10000000000 : ℝ)|^4363 ≤ (431398469509/1000000000000 : ℝ)^3339
        have hw : |(5255002403/10000000000 : ℝ)|=(5255002403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_box_14 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378588451/10000000000 : ℝ)*x 0 + (328437609/625000000 : ℝ)*x 1 + (-2022667917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378588451/10000000000 : ℝ)^4363 ≤ (1778811914799/4000000000000 : ℝ)^3339 := by
    have hnat : (5378588451 : ℕ)^4363*4000000000000^3339 ≤ 1778811914799^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378588451 10000000000 1778811914799 4000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328437609/625000000 : ℝ)^4363 ≤ (43139839881869/100000000000000 : ℝ)^3339 := by
    have hnat : (328437609 : ℕ)^4363*100000000000000^3339 ≤ 43139839881869^3339*625000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328437609 625000000 43139839881869 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2022667917/10000000000 : ℝ)^4363 ≤ (3097465558827/25000000000000 : ℝ)^3339 := by
    have hnat : (2022667917 : ℕ)^4363*25000000000000^3339 ≤ 3097465558827^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022667917 10000000000 3097465558827 25000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378588451/10000000000 : ℝ), (328437609/625000000 : ℝ), (-2022667917/10000000000 : ℝ)] ![(1778811914799/4000000000000 : ℝ), (43139839881869/100000000000000 : ℝ), (3097465558827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378588451/10000000000 : ℝ)|^4363 ≤ (1778811914799/4000000000000 : ℝ)^3339
        have hw : |(5378588451/10000000000 : ℝ)|=(5378588451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328437609/625000000 : ℝ)|^4363 ≤ (43139839881869/100000000000000 : ℝ)^3339
        have hw : |(328437609/625000000 : ℝ)|=(328437609/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2022667917/10000000000 : ℝ)|^4363 ≤ (3097465558827/25000000000000 : ℝ)^3339
        have hw : |(-2022667917/10000000000 : ℝ)|=(2022667917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1403_box_15 (p : ℝ) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (258476057/625000000 : ℝ)*x 0 + (4402038929/10000000000 : ℝ)*x 1 + (275127469/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258476057/625000000 : ℝ)^4363 ≤ (15772894776511/50000000000000 : ℝ)^3339 := by
    have hnat : (258476057 : ℕ)^4363*50000000000000^3339 ≤ 15772894776511^3339*625000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258476057 625000000 15772894776511 50000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4402038929/10000000000 : ℝ)^4363 ≤ (34227102294929/100000000000000 : ℝ)^3339 := by
    have hnat : (4402038929 : ℕ)^4363*100000000000000^3339 ≤ 34227102294929^3339*10000000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4402038929 10000000000 34227102294929 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275127469/625000000 : ℝ)^4363 ≤ (34227108136813/100000000000000 : ℝ)^3339 := by
    have hnat : (275127469 : ℕ)^4363*100000000000000^3339 ≤ 34227108136813^3339*625000000^4363 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275127469 625000000 34227108136813 100000000000000 4363 3339 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4363/1024 : ℝ)) 4363 3339 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258476057/625000000 : ℝ), (4402038929/10000000000 : ℝ), (275127469/625000000 : ℝ)] ![(15772894776511/50000000000000 : ℝ), (34227102294929/100000000000000 : ℝ), (34227108136813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258476057/625000000 : ℝ)|^4363 ≤ (15772894776511/50000000000000 : ℝ)^3339
        have hw : |(258476057/625000000 : ℝ)|=(258476057/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4402038929/10000000000 : ℝ)|^4363 ≤ (34227102294929/100000000000000 : ℝ)^3339
        have hw : |(4402038929/10000000000 : ℝ)|=(4402038929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275127469/625000000 : ℝ)|^4363 ≤ (34227108136813/100000000000000 : ℝ)^3339
        have hw : |(275127469/625000000 : ℝ)|=(275127469/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1403_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15721/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59061/100000 : ℝ) ∧ (5019/6250 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84587/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5643/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14743/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5643/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5643/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14743/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5643/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5643/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14743/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5643/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5643/50000 : ℝ) ^ (2181/512 : ℝ) ≤ (9205399831775581/100000000000000000000 : ℝ) := by
    have hpowers : (5643/50000 : ℝ)^2181 ≤ (9205399831775581/100000000000000000000 : ℝ)^512 := by
      have hnat : (5643 : ℕ)^2181*100000000000000000000^512 ≤ 9205399831775581^512*50000^2181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5643 50000 9205399831775581 100000000000000000000 2181 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5643/50000 : ℝ)) (X := (9205399831775581/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14743/100000 : ℝ) ^ (2181/512 : ℝ) ≤ (2873231703766959/10000000000000000000 : ℝ) := by
    have hpowers : (14743/100000 : ℝ)^2181 ≤ (2873231703766959/10000000000000000000 : ℝ)^512 := by
      have hnat : (14743 : ℕ)^2181*10000000000000000000^512 ≤ 2873231703766959^512*100000^2181 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14743 100000 2873231703766959 10000000000000000000 2181 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14743/100000 : ℝ)) (X := (2873231703766959/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009205399831775581/50000000000000000000 : ℝ) ≤ (10000432171731883/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (50009205399831775581/50000000000000000000 : ℝ)^512 ≤ (10000432171731883/10000000000000000 : ℝ)^2181 := by
      have hnat : (50009205399831775581 : ℕ)^512*10000000000000000^2181 ≤ 10000432171731883^2181*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009205399831775581 50000000000000000000 10000432171731883 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000432171731883/10000000000000000 : ℝ)) (X := (50009205399831775581/50000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037937716869445171/100000000000000000000 : ℝ) ≤ (10000890476483059/10000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (100037937716869445171/100000000000000000000 : ℝ)^512 ≤ (10000890476483059/10000000000000000 : ℝ)^2181 := by
      have hnat : (100037937716869445171 : ℕ)^512*10000000000000000^2181 ≤ 10000890476483059^2181*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037937716869445171 100000000000000000000 10000890476483059 10000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000890476483059/10000000000000000 : ℝ)) (X := (100037937716869445171/100000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002873231703766959/5000000000000000000 : ℝ) ≤ (2000269756246847/2000000000000000 : ℝ) ^ (2181/512 : ℝ) := by
    have hpowers : (5002873231703766959/5000000000000000000 : ℝ)^512 ≤ (2000269756246847/2000000000000000 : ℝ)^2181 := by
      have hnat : (5002873231703766959 : ℕ)^512*2000000000000000^2181 ≤ 2000269756246847^2181*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002873231703766959 5000000000000000000 2000269756246847 2000000000000000 512 2181 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000269756246847/2000000000000000 : ℝ)) (X := (5002873231703766959/5000000000000000000 : ℝ)) (by norm_num) 2181 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9205399831775581/100000000000000000000 : ℝ) ≤ ((34561149162833574859/34570000000000000000 : ℝ)+2*(57288093897/43212500000000 : ℝ)*(5643/50000 : ℝ))^(2181/512 : ℝ) := by
    rw [show (34561149162833574859/34570000000000000000 : ℝ)+2*(57288093897/43212500000000 : ℝ)*(5643/50000 : ℝ)=(10000432171731883/10000000000000000 : ℝ) by norm_num, show 1+2*(9205399831775581/100000000000000000000 : ℝ)=(50009205399831775581/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2873231703766959/10000000000000000000 : ℝ)+(9205399831775581/100000000000000000000 : ℝ) ≤ ((34561149162833574859/34570000000000000000 : ℝ)+(57288093897/43212500000000 : ℝ)*((14743/100000 : ℝ)+(5643/50000 : ℝ)))^(2181/512 : ℝ) := by
    rw [show (34561149162833574859/34570000000000000000 : ℝ)+(57288093897/43212500000000 : ℝ)*((14743/100000 : ℝ)+(5643/50000 : ℝ))=(10000890476483059/10000000000000000 : ℝ) by norm_num, show 1+(2873231703766959/10000000000000000000 : ℝ)+(9205399831775581/100000000000000000000 : ℝ)=(100037937716869445171/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2873231703766959/10000000000000000000 : ℝ) ≤ ((34561149162833574859/34570000000000000000 : ℝ)+2*(57288093897/43212500000000 : ℝ)*(14743/100000 : ℝ))^(2181/512 : ℝ) := by
    rw [show (34561149162833574859/34570000000000000000 : ℝ)+2*(57288093897/43212500000000 : ℝ)*(14743/100000 : ℝ)=(2000269756246847/2000000000000000 : ℝ) by norm_num, show 1+2*(2873231703766959/10000000000000000000 : ℝ)=(5002873231703766959/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34561149162833574859/34570000000000000000 : ℝ)*(X 1 0+X 2 0)+(57288093897/43212500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (5643/50000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (34561149162833574859/34570000000000000000 : ℝ)) (alpha := (57288093897/43212500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34561149162833574859/34570000000000000000 : ℝ)*(X 0 1+X 2 1)+(57288093897/43212500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (5643/50000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (34561149162833574859/34570000000000000000 : ℝ)) (alpha := (57288093897/43212500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34561149162833574859/34570000000000000000 : ℝ)*(X 0 2+X 1 2)+(57288093897/43212500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2181/512 : ℝ)) (lo := (5643/50000 : ℝ)) (hi := (14743/100000 : ℝ)) (c := (34561149162833574859/34570000000000000000 : ℝ)) (alpha := (57288093897/43212500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-914927157/5000000000 : ℝ)*X 0 0+(43098949/80000000 : ℝ)*X 0 1+(5387368133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285854543/10000000000 : ℝ)*X 1 0+(-1969211057/10000000000 : ℝ)*X 1 1+(1346842001/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1057170979/2000000000 : ℝ)*X 2 0+(1346842041/2500000000 : ℝ)*X 2 1+(-984605181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((891550753/2000000000 : ℝ)*X 0 0+(212063139/500000000 : ℝ)*X 0 1+(2120631367/5000000000 : ℝ)*X 0 2+(891550753/2000000000 : ℝ)*X 1 0+(212063139/500000000 : ℝ)*X 1 1+(2120631367/5000000000 : ℝ)*X 1 2+(891550753/2000000000 : ℝ)*X 2 0+(212063139/500000000 : ℝ)*X 2 1+(2120631367/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-539433513/2500000000 : ℝ)*X 0 0+(2633056989/5000000000 : ℝ)*X 0 1+(5266113903/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2685402237/5000000000 : ℝ)*X 1 0+(-403654619/2000000000 : ℝ)*X 1 1+(658264281/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5370804641/10000000000 : ℝ)*X 2 0+(5266113839/10000000000 : ℝ)*X 2 1+(-1009136709/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2081536147/5000000000 : ℝ)*X 0 0+(4388551877/10000000000 : ℝ)*X 0 1+(2194275893/5000000000 : ℝ)*X 0 2+(2081536147/5000000000 : ℝ)*X 1 0+(4388551877/10000000000 : ℝ)*X 1 1+(2194275893/5000000000 : ℝ)*X 1 2+(2081536147/5000000000 : ℝ)*X 2 0+(4388551877/10000000000 : ℝ)*X 2 1+(2194275893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1044365779/5000000000 : ℝ)*X 0 0+(1295590157/2500000000 : ℝ)*X 0 1+(5401357751/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276049073/10000000000 : ℝ)*X 1 0+(-1963422027/10000000000 : ℝ)*X 1 1+(1080271573/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276048471/10000000000 : ℝ)*X 2 0+(5401358547/10000000000 : ℝ)*X 2 1+(-245427739/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1122798783/2500000000 : ℝ)*X 0 0+(2112127941/5000000000 : ℝ)*X 0 1+(4224253847/10000000000 : ℝ)*X 0 2+(1122798783/2500000000 : ℝ)*X 1 0+(2112127941/5000000000 : ℝ)*X 1 1+(4224253847/10000000000 : ℝ)*X 1 2+(1122798783/2500000000 : ℝ)*X 2 0+(2112127941/5000000000 : ℝ)*X 2 1+(4224253847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-9495411/50000000 : ℝ)*X 0 0+(2734523411/5000000000 : ℝ)*X 0 1+(656875159/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5378587343/10000000000 : ℝ)*X 1 0+(-2022668529/10000000000 : ℝ)*X 1 1+(5255002403/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5378588451/10000000000 : ℝ)*X 2 0+(328437609/625000000 : ℝ)*X 2 1+(-2022667917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((258476057/625000000 : ℝ)*X 0 0+(4402038929/10000000000 : ℝ)*X 0 1+(275127469/625000000 : ℝ)*X 0 2+(258476057/625000000 : ℝ)*X 1 0+(4402038929/10000000000 : ℝ)*X 1 1+(275127469/625000000 : ℝ)*X 1 2+(258476057/625000000 : ℝ)*X 2 0+(4402038929/10000000000 : ℝ)*X 2 1+(275127469/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1403_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15721/25000 : ℝ) ≤ (-135863917335708744569163377534331/216062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36448983/100000000000000 : ℝ)*(upper1) + (18317577/25000000000000 : ℝ)*(upper2) + (26941123/50000000000000 : ℝ)*(upper3) + (21442901/100000000000000 : ℝ)*(upper5) + (373535005162601/12500000000000 : ℝ)*(major0) + (373535005162601/12500000000000 : ℝ)*(major1) + (373535005162601/12500000000000 : ℝ)*(major2) + (3231834753/50000000000000 : ℝ)*(sp2) + (12505557/781250000000 : ℝ)*(sp3) + (4095819250990499/100000000000000 : ℝ)*(sp4) + (4095707773101119/100000000000000 : ℝ)*(sp5) + (127994149603781/3125000000000 : ℝ)*(sp6) + (95084990991221/5000000000000 : ℝ)*(sp7) + (5573894469/5000000000000 : ℝ)*(sp13) + (475425355133929/25000000000000 : ℝ)*(f.failure) + (4095819250990499/100000000000000 : ℝ)*(f.sum) + (6787063572297/4321250000000000000000000000 : ℝ)*base65 + (1714069688953998259/432125000000000000000000000000000 : ℝ)*base67 + (5881106920863623259/432125000000000000000000000000000 : ℝ)*base69 + (2658358562482998259/432125000000000000000000000000000 : ℝ)*base71 + (27169977874867/17285000000000000000000000000 : ℝ)*base74 + (12849547733096748259/432125000000000000000000000000000 : ℝ)*base75 + (3807408323711498259/432125000000000000000000000000000 : ℝ)*base77 + (5249145925922748259/432125000000000000000000000000000 : ℝ)*base79 + (32621360328687/4321250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (9217993/2500000000000000000000 : ℝ)*base90 + (9217993/2500000000000000000000 : ℝ)*base92 + (9217993/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59061/100000 : ℝ) ≤ (1020914207326377135597153539601933/1728500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32491603/20000000000000 : ℝ)*(lower1) + (65918843/50000000000000 : ℝ)*(lower2) + (213472389/100000000000000 : ℝ)*(upper4) + (3059016886113457/100000000000000 : ℝ)*(major0) + (3059016886113457/100000000000000 : ℝ)*(major1) + (3059016886113457/100000000000000 : ℝ)*(major2) + (2075808326799383/50000000000000 : ℝ)*(sp0) + (415146224625001/10000000000000 : ℝ)*(sp1) + (207581212547659/5000000000000 : ℝ)*(sp2) + (973357592094679/50000000000000 : ℝ)*(sp3) + (4255124809/100000000000000 : ℝ)*(sp6) + (2217581461/100000000000000 : ℝ)*(sp7) + (5926239611/50000000000000 : ℝ)*(sp8) + (166259827979/100000000000000 : ℝ)*(sp9) + (1946717401770819/100000000000000 : ℝ)*(f.failure) + (1037907126519497/25000000000000 : ℝ)*(f.sum) + (17405053189073/4321250000000000000000000000 : ℝ)*base65 + (32151910270248977563/3457000000000000000000000000000000 : ℝ)*base67 + (29836542984393977563/3457000000000000000000000000000000 : ℝ)*base69 + (42518597323962977563/3457000000000000000000000000000000 : ℝ)*base71 + (258397970121/8642500000000000000000000000 : ℝ)*base73 + (13434076106718977563/3457000000000000000000000000000000 : ℝ)*base75 + (3400755590158977563/3457000000000000000000000000000000 : ℝ)*base77 + (23973667722263977563/3457000000000000000000000000000000 : ℝ)*base79 + (11518091977107/4321250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (9262877/10000000000000000000000 : ℝ)*base89 + (9262877/10000000000000000000000 : ℝ)*base91 + (9262877/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (5019/6250 : ℝ) ≤ (694047651456331207458540990991653/864250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2358703/2000000000000 : ℝ)*(upper1) + (93102453/50000000000000 : ℝ)*(upper3) + (33950217/25000000000000 : ℝ)*(upper4) + (160981783/50000000000000 : ℝ)*(lower5) + (1684144924444011/50000000000000 : ℝ)*(major0) + (1684144924444011/50000000000000 : ℝ)*(major1) + (1684144924444011/50000000000000 : ℝ)*(major2) + (11590170143/100000000000000 : ℝ)*(sp0) + (209398810199/50000000000000 : ℝ)*(sp2) + (6231616951/10000000000000 : ℝ)*(sp3) + (4566264747738893/100000000000000 : ℝ)*(sp8) + (1141569084477259/25000000000000 : ℝ)*(sp9) + (2282928770144319/50000000000000 : ℝ)*(sp10) + (535868064882947/25000000000000 : ℝ)*(sp11) + (1071767287850649/50000000000000 : ℝ)*(f.failure) + (1141569084477259/25000000000000 : ℝ)*(f.sum) + (32652412716289/8642500000000000000000000000 : ℝ)*base66 + (9741952747958819449/1728500000000000000000000000000000 : ℝ)*base67 + (18248750904233319449/1728500000000000000000000000000000 : ℝ)*base69 + (2333697061612680551/1728500000000000000000000000000000 : ℝ)*base72 + (4311435998833/4321250000000000000000000000 : ℝ)*base73 + (26239251235510319449/1728500000000000000000000000000000 : ℝ)*base75 + (3012301114392680551/1728500000000000000000000000000000 : ℝ)*base78 + (1215210256407319449/1728500000000000000000000000000000 : ℝ)*base79 + (11330226311333/4321250000000000000000000000 : ℝ)*base81 + (8581767/5000000000000000000000 : ℝ)*base89 + (8581767/5000000000000000000000 : ℝ)*base91 + (8581767/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84587/100000 : ℝ) ≤ (-731019554548598710584883620602253/864250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (240682911/100000000000000 : ℝ)*(lower1) + (110037451/25000000000000 : ℝ)*(lower2) + (13349593/6250000000000 : ℝ)*(upper5) + (1702727130131263/50000000000000 : ℝ)*(major0) + (1702727130131263/50000000000000 : ℝ)*(major1) + (1702727130131263/50000000000000 : ℝ)*(major2) + (22937536587/100000000000000 : ℝ)*(sp0) + (14314438367/100000000000000 : ℝ)*(sp5) + (14234581903/12500000000000 : ℝ)*(sp6) + (35298622707/25000000000000 : ℝ)*(sp7) + (583986853754677/12500000000000 : ℝ)*(sp12) + (1167975863283909/25000000000000 : ℝ)*(sp13) + (2335901945459389/50000000000000 : ℝ)*(sp14) + (1083522157584143/50000000000000 : ℝ)*(sp15) + (433437101931823/20000000000000 : ℝ)*(f.failure) + (4671917767574003/100000000000000 : ℝ)*(f.sum) + (77285312592983/8642500000000000000000000000 : ℝ)*base65 + (7285743565541016917/1728500000000000000000000000000000 : ℝ)*base67 + (589535433248016917/1728500000000000000000000000000000 : ℝ)*base69 + (10157963161690516917/1728500000000000000000000000000000 : ℝ)*base71 + (31807995489391/17285000000000000000000000000 : ℝ)*base73 + (20590853995169516917/1728500000000000000000000000000000 : ℝ)*base75 + (23963115233344516917/1728500000000000000000000000000000 : ℝ)*base77 + (16652279476022516917/1728500000000000000000000000000000 : ℝ)*base79 + (44276864141393/8642500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (4274609/2000000000000000000000 : ℝ)*base89 + (4274609/2000000000000000000000 : ℝ)*base91 + (4274609/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1403_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14743/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5643/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15721/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59061/100000 : ℝ) else (5019/6250 : ℝ) ≤ X j i ∧ X j i ≤ (84587/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1403_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1403_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15721/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59061/100000 : ℝ) else (5019/6250 : ℝ) ≤ X j i ∧ X j i ≤ (84587/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1403_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1403_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1403_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2181/512 : ℝ) ≤ p) (hpb : p ≤ (4363/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157137183/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11281/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15721/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59061/100000 : ℝ) else (5019/6250 : ℝ) ≤ X j i ∧ X j i ≤ (84587/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1403_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

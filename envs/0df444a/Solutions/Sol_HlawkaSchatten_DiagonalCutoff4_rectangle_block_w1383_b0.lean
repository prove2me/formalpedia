-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1383_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:23:37.118036+00:00
-- url     : https://prove2.me/submissions/4ab53f02-74e7-405c-8528-0392c744bdae

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
theorem support_rectangle_w1383_s0_0 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-892577157/5000000000 : ℝ)*x 0 + (597939649/1000000000 : ℝ)*x 1 + (2410298279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892577157/5000000000 : ℝ)^4343 ≤ (10490538527079/100000000000000 : ℝ)^3319 := by
    have hnat : (892577157 : ℕ)^4343*100000000000000^3319 ≤ 10490538527079^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892577157 5000000000 10490538527079 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (597939649/1000000000 : ℝ)^4343 ≤ (51021143740211/100000000000000 : ℝ)^3319 := by
    have hnat : (597939649 : ℕ)^4343*100000000000000^3319 ≤ 51021143740211^3319*1000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      597939649 1000000000 51021143740211 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2410298279/5000000000 : ℝ)^4343 ≤ (19244158856007/50000000000000 : ℝ)^3319 := by
    have hnat : (2410298279 : ℕ)^4343*50000000000000^3319 ≤ 19244158856007^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2410298279 5000000000 19244158856007 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-892577157/5000000000 : ℝ), (597939649/1000000000 : ℝ), (2410298279/5000000000 : ℝ)] ![(10490538527079/100000000000000 : ℝ), (51021143740211/100000000000000 : ℝ), (19244158856007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-892577157/5000000000 : ℝ)|^4343 ≤ (10490538527079/100000000000000 : ℝ)^3319
        have hw : |(-892577157/5000000000 : ℝ)|=(892577157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(597939649/1000000000 : ℝ)|^4343 ≤ (51021143740211/100000000000000 : ℝ)^3319
        have hw : |(597939649/1000000000 : ℝ)|=(597939649/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2410298279/5000000000 : ℝ)|^4343 ≤ (19244158856007/50000000000000 : ℝ)^3319
        have hw : |(2410298279/5000000000 : ℝ)|=(2410298279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s0_1 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1374306819/2500000000 : ℝ)*x 0 + (-610468111/2500000000 : ℝ)*x 1 + (4820597253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1374306819/2500000000 : ℝ)^4343 ≤ (5713222079671/12500000000000 : ℝ)^3319 := by
    have hnat : (1374306819 : ℕ)^4343*12500000000000^3319 ≤ 5713222079671^3319*2500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374306819 2500000000 5713222079671 12500000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (610468111/2500000000 : ℝ)^4343 ≤ (15805898375073/100000000000000 : ℝ)^3319 := by
    have hnat : (610468111 : ℕ)^4343*100000000000000^3319 ≤ 15805898375073^3319*2500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610468111 2500000000 15805898375073 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4820597253/10000000000 : ℝ)^4343 ≤ (38488324972999/100000000000000 : ℝ)^3319 := by
    have hnat : (4820597253 : ℕ)^4343*100000000000000^3319 ≤ 38488324972999^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4820597253 10000000000 38488324972999 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1374306819/2500000000 : ℝ), (-610468111/2500000000 : ℝ), (4820597253/10000000000 : ℝ)] ![(5713222079671/12500000000000 : ℝ), (15805898375073/100000000000000 : ℝ), (38488324972999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1374306819/2500000000 : ℝ)|^4343 ≤ (5713222079671/12500000000000 : ℝ)^3319
        have hw : |(1374306819/2500000000 : ℝ)|=(1374306819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-610468111/2500000000 : ℝ)|^4343 ≤ (15805898375073/100000000000000 : ℝ)^3319
        have hw : |(-610468111/2500000000 : ℝ)|=(610468111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4820597253/10000000000 : ℝ)|^4343 ≤ (38488324972999/100000000000000 : ℝ)^3319
        have hw : |(4820597253/10000000000 : ℝ)|=(4820597253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s0_2 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2748613563/5000000000 : ℝ)*x 0 + (602574557/1250000000 : ℝ)*x 1 + (-122093681/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2748613563/5000000000 : ℝ)^4343 ≤ (45705775005439/100000000000000 : ℝ)^3319 := by
    have hnat : (2748613563 : ℕ)^4343*100000000000000^3319 ≤ 45705775005439^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748613563 5000000000 45705775005439 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (602574557/1250000000 : ℝ)^4343 ≤ (38488316646373/100000000000000 : ℝ)^3319 := by
    have hnat : (602574557 : ℕ)^4343*100000000000000^3319 ≤ 38488316646373^3319*1250000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602574557 1250000000 38488316646373 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122093681/500000000 : ℝ)^4343 ≤ (15805908335687/100000000000000 : ℝ)^3319 := by
    have hnat : (122093681 : ℕ)^4343*100000000000000^3319 ≤ 15805908335687^3319*500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122093681 500000000 15805908335687 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2748613563/5000000000 : ℝ), (602574557/1250000000 : ℝ), (-122093681/500000000 : ℝ)] ![(45705775005439/100000000000000 : ℝ), (38488316646373/100000000000000 : ℝ), (15805908335687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2748613563/5000000000 : ℝ)|^4343 ≤ (45705775005439/100000000000000 : ℝ)^3319
        have hw : |(2748613563/5000000000 : ℝ)|=(2748613563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(602574557/1250000000 : ℝ)|^4343 ≤ (38488316646373/100000000000000 : ℝ)^3319
        have hw : |(602574557/1250000000 : ℝ)|=(602574557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-122093681/500000000 : ℝ)|^4343 ≤ (15805908335687/100000000000000 : ℝ)^3319
        have hw : |(-122093681/500000000 : ℝ)|=(122093681/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s0_3 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (834534637/2000000000 : ℝ)*x 0 + (3104781853/10000000000 : ℝ)*x 1 + (5569465567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (834534637/2000000000 : ℝ)^4343 ≤ (7966032822683/25000000000000 : ℝ)^3319 := by
    have hnat : (834534637 : ℕ)^4343*25000000000000^3319 ≤ 7966032822683^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834534637 2000000000 7966032822683 25000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3104781853/10000000000 : ℝ)^4343 ≤ (2164258531677/10000000000000 : ℝ)^3319 := by
    have hnat : (3104781853 : ℕ)^4343*10000000000000^3319 ≤ 2164258531677^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104781853 10000000000 2164258531677 10000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5569465567/10000000000 : ℝ)^4343 ≤ (23246641692623/50000000000000 : ℝ)^3319 := by
    have hnat : (5569465567 : ℕ)^4343*50000000000000^3319 ≤ 23246641692623^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5569465567 10000000000 23246641692623 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(834534637/2000000000 : ℝ), (3104781853/10000000000 : ℝ), (5569465567/10000000000 : ℝ)] ![(7966032822683/25000000000000 : ℝ), (2164258531677/10000000000000 : ℝ), (23246641692623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(834534637/2000000000 : ℝ)|^4343 ≤ (7966032822683/25000000000000 : ℝ)^3319
        have hw : |(834534637/2000000000 : ℝ)|=(834534637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3104781853/10000000000 : ℝ)|^4343 ≤ (2164258531677/10000000000000 : ℝ)^3319
        have hw : |(3104781853/10000000000 : ℝ)|=(3104781853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5569465567/10000000000 : ℝ)|^4343 ≤ (23246641692623/50000000000000 : ℝ)^3319
        have hw : |(5569465567/10000000000 : ℝ)|=(5569465567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s0_4 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-447350019/2500000000 : ℝ)*x 0 + (2425171939/5000000000 : ℝ)*x 1 + (5948585907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (447350019/2500000000 : ℝ)^4343 ≤ (10523198774189/100000000000000 : ℝ)^3319 := by
    have hnat : (447350019 : ℕ)^4343*100000000000000^3319 ≤ 10523198774189^3319*2500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447350019 2500000000 10523198774189 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2425171939/5000000000 : ℝ)^4343 ≤ (9699849269423/25000000000000 : ℝ)^3319 := by
    have hnat : (2425171939 : ℕ)^4343*25000000000000^3319 ≤ 9699849269423^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2425171939 5000000000 9699849269423 25000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5948585907/10000000000 : ℝ)^4343 ≤ (50677404140063/100000000000000 : ℝ)^3319 := by
    have hnat : (5948585907 : ℕ)^4343*100000000000000^3319 ≤ 50677404140063^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5948585907 10000000000 50677404140063 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-447350019/2500000000 : ℝ), (2425171939/5000000000 : ℝ), (5948585907/10000000000 : ℝ)] ![(10523198774189/100000000000000 : ℝ), (9699849269423/25000000000000 : ℝ), (50677404140063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-447350019/2500000000 : ℝ)|^4343 ≤ (10523198774189/100000000000000 : ℝ)^3319
        have hw : |(-447350019/2500000000 : ℝ)|=(447350019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2425171939/5000000000 : ℝ)|^4343 ≤ (9699849269423/25000000000000 : ℝ)^3319
        have hw : |(2425171939/5000000000 : ℝ)|=(2425171939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5948585907/10000000000 : ℝ)|^4343 ≤ (50677404140063/100000000000000 : ℝ)^3319
        have hw : |(5948585907/10000000000 : ℝ)|=(5948585907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s0_5 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5181176909/10000000000 : ℝ)*x 0 + (-262776891/2000000000 : ℝ)*x 1 + (2974292871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5181176909/10000000000 : ℝ)^4343 ≤ (42298208598167/100000000000000 : ℝ)^3319 := by
    have hnat : (5181176909 : ℕ)^4343*100000000000000^3319 ≤ 42298208598167^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181176909 10000000000 42298208598167 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262776891/2000000000 : ℝ)^4343 ≤ (7024389083749/100000000000000 : ℝ)^3319 := by
    have hnat : (262776891 : ℕ)^4343*100000000000000^3319 ≤ 7024389083749^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262776891 2000000000 7024389083749 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2974292871/5000000000 : ℝ)^4343 ≤ (50677402300701/100000000000000 : ℝ)^3319 := by
    have hnat : (2974292871 : ℕ)^4343*100000000000000^3319 ≤ 50677402300701^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2974292871 5000000000 50677402300701 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5181176909/10000000000 : ℝ), (-262776891/2000000000 : ℝ), (2974292871/5000000000 : ℝ)] ![(42298208598167/100000000000000 : ℝ), (7024389083749/100000000000000 : ℝ), (50677402300701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5181176909/10000000000 : ℝ)|^4343 ≤ (42298208598167/100000000000000 : ℝ)^3319
        have hw : |(5181176909/10000000000 : ℝ)|=(5181176909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-262776891/2000000000 : ℝ)|^4343 ≤ (7024389083749/100000000000000 : ℝ)^3319
        have hw : |(-262776891/2000000000 : ℝ)|=(262776891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2974292871/5000000000 : ℝ)|^4343 ≤ (50677402300701/100000000000000 : ℝ)^3319
        have hw : |(2974292871/5000000000 : ℝ)|=(2974292871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s0_6 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5181176583/10000000000 : ℝ)*x 0 + (5948585877/10000000000 : ℝ)*x 1 + (-656942369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5181176583/10000000000 : ℝ)^4343 ≤ (42298205115647/100000000000000 : ℝ)^3319 := by
    have hnat : (5181176583 : ℕ)^4343*100000000000000^3319 ≤ 42298205115647^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181176583 10000000000 42298205115647 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5948585877/10000000000 : ℝ)^4343 ≤ (25338701902817/50000000000000 : ℝ)^3319 := by
    have hnat : (5948585877 : ℕ)^4343*50000000000000^3319 ≤ 25338701902817^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5948585877 10000000000 25338701902817 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656942369/5000000000 : ℝ)^4343 ≤ (1404878212709/20000000000000 : ℝ)^3319 := by
    have hnat : (656942369 : ℕ)^4343*20000000000000^3319 ≤ 1404878212709^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656942369 5000000000 1404878212709 20000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5181176583/10000000000 : ℝ), (5948585877/10000000000 : ℝ), (-656942369/5000000000 : ℝ)] ![(42298205115647/100000000000000 : ℝ), (25338701902817/50000000000000 : ℝ), (1404878212709/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5181176583/10000000000 : ℝ)|^4343 ≤ (42298205115647/100000000000000 : ℝ)^3319
        have hw : |(5181176583/10000000000 : ℝ)|=(5181176583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5948585877/10000000000 : ℝ)|^4343 ≤ (25338701902817/50000000000000 : ℝ)^3319
        have hw : |(5948585877/10000000000 : ℝ)|=(5948585877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-656942369/5000000000 : ℝ)|^4343 ≤ (1404878212709/20000000000000 : ℝ)^3319
        have hw : |(-656942369/5000000000 : ℝ)|=(656942369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s0_7 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2090850571/5000000000 : ℝ)*x 0 + (5506194861/10000000000 : ℝ)*x 1 + (634062743/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2090850571/5000000000 : ℝ)^4343 ≤ (31954372441667/100000000000000 : ℝ)^3319 := by
    have hnat : (2090850571 : ℕ)^4343*100000000000000^3319 ≤ 31954372441667^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090850571 5000000000 31954372441667 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5506194861/10000000000 : ℝ)^4343 ≤ (22901682127271/50000000000000 : ℝ)^3319 := by
    have hnat : (5506194861 : ℕ)^4343*50000000000000^3319 ≤ 22901682127271^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506194861 10000000000 22901682127271 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (634062743/2000000000 : ℝ)^4343 ≤ (22242263294307/100000000000000 : ℝ)^3319 := by
    have hnat : (634062743 : ℕ)^4343*100000000000000^3319 ≤ 22242263294307^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634062743 2000000000 22242263294307 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2090850571/5000000000 : ℝ), (5506194861/10000000000 : ℝ), (634062743/2000000000 : ℝ)] ![(31954372441667/100000000000000 : ℝ), (22901682127271/50000000000000 : ℝ), (22242263294307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2090850571/5000000000 : ℝ)|^4343 ≤ (31954372441667/100000000000000 : ℝ)^3319
        have hw : |(2090850571/5000000000 : ℝ)|=(2090850571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5506194861/10000000000 : ℝ)|^4343 ≤ (22901682127271/50000000000000 : ℝ)^3319
        have hw : |(5506194861/10000000000 : ℝ)|=(5506194861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(634062743/2000000000 : ℝ)|^4343 ≤ (22242263294307/100000000000000 : ℝ)^3319
        have hw : |(634062743/2000000000 : ℝ)|=(634062743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1383_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39086603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (859/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26579/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (0 : ℝ) ^ (2171/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2171 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2171*1^512 ≤ 0^512*1^2171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2171 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2171/512 : ℝ) ≤ (513548073909596149/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2171 ≤ (513548073909596149/25000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2171*25000000000000000000^512 ≤ 513548073909596149^512*5^2171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 513548073909596149 25000000000000000000 2171 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (513548073909596149/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2171/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2171 := by
      have hnat : (1 : ℕ)^512*1^2171 ≤ 1^2171*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25513548073909596149/25000000000000000000 : ℝ) ≤ (2512017387573333/2500000000000000 : ℝ) ^ (2171/512 : ℝ) := by
    have hpowers : (25513548073909596149/25000000000000000000 : ℝ)^512 ≤ (2512017387573333/2500000000000000 : ℝ)^2171 := by
      have hnat : (25513548073909596149 : ℕ)^512*2500000000000000^2171 ≤ 2512017387573333^2171*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25513548073909596149 25000000000000000000 2512017387573333 2500000000000000 512 2171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2512017387573333/2500000000000000 : ℝ)) (X := (25513548073909596149/25000000000000000000 : ℝ)) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (13013548073909596149/12500000000000000000 : ℝ) ≤ (1262017387573333/1250000000000000 : ℝ) ^ (2171/512 : ℝ) := by
    have hpowers : (13013548073909596149/12500000000000000000 : ℝ)^512 ≤ (1262017387573333/1250000000000000 : ℝ)^2171 := by
      have hnat : (13013548073909596149 : ℕ)^512*1250000000000000^2171 ≤ 1262017387573333^2171*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13013548073909596149 12500000000000000000 1262017387573333 1250000000000000 512 2171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1262017387573333/1250000000000000 : ℝ)) (X := (13013548073909596149/12500000000000000000 : ℝ)) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(12017387573333/1000000000000000 : ℝ)*(0 : ℝ))^(2171/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(12017387573333/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(513548073909596149/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(12017387573333/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2171/512 : ℝ) := by
    rw [show (1 : ℝ)+(12017387573333/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2512017387573333/2500000000000000 : ℝ) by norm_num, show 1+(513548073909596149/25000000000000000000 : ℝ)+(0 : ℝ)=(25513548073909596149/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(513548073909596149/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(12017387573333/1000000000000000 : ℝ)*(2/5 : ℝ))^(2171/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(12017387573333/1000000000000000 : ℝ)*(2/5 : ℝ)=(1262017387573333/1250000000000000 : ℝ) by norm_num, show 1+2*(513548073909596149/25000000000000000000 : ℝ)=(13013548073909596149/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(12017387573333/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2171/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12017387573333/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(12017387573333/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2171/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12017387573333/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(12017387573333/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2171/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12017387573333/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-892577157/5000000000 : ℝ)*X 0 0+(597939649/1000000000 : ℝ)*X 0 1+(2410298279/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1374306819/2500000000 : ℝ)*X 1 0+(-610468111/2500000000 : ℝ)*X 1 1+(4820597253/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2748613563/5000000000 : ℝ)*X 2 0+(602574557/1250000000 : ℝ)*X 2 1+(-122093681/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((834534637/2000000000 : ℝ)*X 0 0+(3104781853/10000000000 : ℝ)*X 0 1+(5569465567/10000000000 : ℝ)*X 0 2+(834534637/2000000000 : ℝ)*X 1 0+(3104781853/10000000000 : ℝ)*X 1 1+(5569465567/10000000000 : ℝ)*X 1 2+(834534637/2000000000 : ℝ)*X 2 0+(3104781853/10000000000 : ℝ)*X 2 1+(5569465567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-447350019/2500000000 : ℝ)*X 0 0+(2425171939/5000000000 : ℝ)*X 0 1+(5948585907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5181176909/10000000000 : ℝ)*X 1 0+(-262776891/2000000000 : ℝ)*X 1 1+(2974292871/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5181176583/10000000000 : ℝ)*X 2 0+(5948585877/10000000000 : ℝ)*X 2 1+(-656942369/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2090850571/5000000000 : ℝ)*X 0 0+(5506194861/10000000000 : ℝ)*X 0 1+(634062743/2000000000 : ℝ)*X 0 2+(2090850571/5000000000 : ℝ)*X 1 0+(5506194861/10000000000 : ℝ)*X 1 1+(634062743/2000000000 : ℝ)*X 1 2+(2090850571/5000000000 : ℝ)*X 2 0+(5506194861/10000000000 : ℝ)*X 2 1+(634062743/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47207772409962415105791/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (221338557/100000000000000 : ℝ)*(base1) + (86462937/100000000000000 : ℝ)*(base16) + (22468431/6250000000000 : ℝ)*(base19) + (422410619/100000000000000 : ℝ)*(base23) + (25471047/100000000000000 : ℝ)*(upper3) + (634347603750791/100000000000000 : ℝ)*(major0) + (634347603750791/100000000000000 : ℝ)*(major1) + (634347603750791/100000000000000 : ℝ)*(major2) + (215740652493391/25000000000000 : ℝ)*(sp0) + (862962583845287/100000000000000 : ℝ)*(sp1) + (431481303696251/50000000000000 : ℝ)*(sp2) + (405731719072173/100000000000000 : ℝ)*(sp3) + (641168113/100000000000000 : ℝ)*(sp4) + (174344031/100000000000000 : ℝ)*(sp7) + (405732114754761/100000000000000 : ℝ)*(f.failure) + (10787037872539/1250000000000 : ℝ)*(f.sum) + (43762733106403/50000000000000000000000000000 : ℝ)*base65 + (228161014143597/100000000000000000000000000000 : ℝ)*base68 + (579901523356403/100000000000000000000000000000 : ℝ)*base69 + (166623107356403/100000000000000000000000000000 : ℝ)*base71 + (97362122343597/50000000000000000000000000000 : ℝ)*base74 + (320879482556403/100000000000000000000000000000 : ℝ)*base75 + (20327003356403/100000000000000000000000000000 : ℝ)*base77 + (759103047943597/100000000000000000000000000000 : ℝ)*base80 + (336731618456403/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (10566883/2500000000000000000000 : ℝ)*base89 + (10566883/2500000000000000000000 : ℝ)*base91 + (10566883/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8848270021564566960843/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (349882283/25000000000000 : ℝ)*(base19) + (267983949/20000000000000 : ℝ)*(base23) + (132162049/100000000000000 : ℝ)*(base32) + (48186977/25000000000000 : ℝ)*(upper3) + (32817749/25000000000000 : ℝ)*(upper5) + (167331184838561/25000000000000 : ℝ)*(major0) + (167331184838561/25000000000000 : ℝ)*(major1) + (167331184838561/25000000000000 : ℝ)*(major2) + (3184742759/100000000000000 : ℝ)*(sp1) + (786685703/25000000000000 : ℝ)*(sp2) + (455272806240941/50000000000000 : ℝ)*(sp4) + (910541028209991/100000000000000 : ℝ)*(sp5) + (36421645032773/4000000000000 : ℝ)*(sp6) + (26756471581341/6250000000000 : ℝ)*(sp7) + (214051838731753/50000000000000 : ℝ)*(f.failure) + (455272806240941/50000000000000 : ℝ)*(f.sum) + (3368342806187/12500000000000000000000000000 : ℝ)*base66 + (198566253393813/25000000000000000000000000000 : ℝ)*base67 + (202149503343813/25000000000000000000000000000 : ℝ)*base69 + (208255777318813/25000000000000000000000000000 : ℝ)*base71 + (14734719756313/12500000000000000000000000000 : ℝ)*base73 + (171310693968813/25000000000000000000000000000 : ℝ)*base75 + (126750965218813/25000000000000000000000000000 : ℝ)*base77 + (261698030868813/25000000000000000000000000000 : ℝ)*base79 + (18308556818813/12500000000000000000000000000 : ℝ)*base81 + (3005059/1250000000000000000000 : ℝ)*base89 + (3005059/1250000000000000000000 : ℝ)*base91 + (3005059/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1383_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39086603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (859/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26579/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1383_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1383_s1_0 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-491017757/2500000000 : ℝ)*x 0 + (281210839/500000000 : ℝ)*x 1 + (2530574199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (491017757/2500000000 : ℝ)^4343 ≤ (11887138823459/100000000000000 : ℝ)^3319 := by
    have hnat : (491017757 : ℕ)^4343*100000000000000^3319 ≤ 11887138823459^3319*2500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491017757 2500000000 11887138823459 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281210839/500000000 : ℝ)^4343 ≤ (23546129844829/50000000000000 : ℝ)^3319 := by
    have hnat : (281210839 : ℕ)^4343*50000000000000^3319 ≤ 23546129844829^3319*500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281210839 500000000 23546129844829 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2530574199/5000000000 : ℝ)^4343 ≤ (20510300731001/50000000000000 : ℝ)^3319 := by
    have hnat : (2530574199 : ℕ)^4343*50000000000000^3319 ≤ 20510300731001^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2530574199 5000000000 20510300731001 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-491017757/2500000000 : ℝ), (281210839/500000000 : ℝ), (2530574199/5000000000 : ℝ)] ![(11887138823459/100000000000000 : ℝ), (23546129844829/50000000000000 : ℝ), (20510300731001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-491017757/2500000000 : ℝ)|^4343 ≤ (11887138823459/100000000000000 : ℝ)^3319
        have hw : |(-491017757/2500000000 : ℝ)|=(491017757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281210839/500000000 : ℝ)|^4343 ≤ (23546129844829/50000000000000 : ℝ)^3319
        have hw : |(281210839/500000000 : ℝ)|=(281210839/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2530574199/5000000000 : ℝ)|^4343 ≤ (20510300731001/50000000000000 : ℝ)^3319
        have hw : |(2530574199/5000000000 : ℝ)|=(2530574199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s1_1 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2700737993/5000000000 : ℝ)*x 0 + (-452702529/2000000000 : ℝ)*x 1 + (5061149841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2700737993/5000000000 : ℝ)^4343 ≤ (4466685840179/10000000000000 : ℝ)^3319 := by
    have hnat : (2700737993 : ℕ)^4343*10000000000000^3319 ≤ 4466685840179^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700737993 5000000000 4466685840179 10000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (452702529/2000000000 : ℝ)^4343 ≤ (14312524821931/100000000000000 : ℝ)^3319 := by
    have hnat : (452702529 : ℕ)^4343*100000000000000^3319 ≤ 14312524821931^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452702529 2000000000 14312524821931 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5061149841/10000000000 : ℝ)^4343 ≤ (20510308382947/50000000000000 : ℝ)^3319 := by
    have hnat : (5061149841 : ℕ)^4343*50000000000000^3319 ≤ 20510308382947^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5061149841 10000000000 20510308382947 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2700737993/5000000000 : ℝ), (-452702529/2000000000 : ℝ), (5061149841/10000000000 : ℝ)] ![(4466685840179/10000000000000 : ℝ), (14312524821931/100000000000000 : ℝ), (20510308382947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2700737993/5000000000 : ℝ)|^4343 ≤ (4466685840179/10000000000000 : ℝ)^3319
        have hw : |(2700737993/5000000000 : ℝ)|=(2700737993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-452702529/2000000000 : ℝ)|^4343 ≤ (14312524821931/100000000000000 : ℝ)^3319
        have hw : |(-452702529/2000000000 : ℝ)|=(452702529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5061149841/10000000000 : ℝ)|^4343 ≤ (20510308382947/50000000000000 : ℝ)^3319
        have hw : |(5061149841/10000000000 : ℝ)|=(5061149841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s1_2 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5401476723/10000000000 : ℝ)*x 0 + (2530574291/5000000000 : ℝ)*x 1 + (-452702659/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5401476723/10000000000 : ℝ)^4343 ≤ (44666866376649/100000000000000 : ℝ)^3319 := by
    have hnat : (5401476723 : ℕ)^4343*100000000000000^3319 ≤ 44666866376649^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401476723 10000000000 44666866376649 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2530574291/5000000000 : ℝ)^4343 ≤ (20510301706717/50000000000000 : ℝ)^3319 := by
    have hnat : (2530574291 : ℕ)^4343*50000000000000^3319 ≤ 20510301706717^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2530574291 5000000000 20510301706717 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452702659/2000000000 : ℝ)^4343 ≤ (3578132550009/25000000000000 : ℝ)^3319 := by
    have hnat : (452702659 : ℕ)^4343*25000000000000^3319 ≤ 3578132550009^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452702659 2000000000 3578132550009 25000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5401476723/10000000000 : ℝ), (2530574291/5000000000 : ℝ), (-452702659/2000000000 : ℝ)] ![(44666866376649/100000000000000 : ℝ), (20510301706717/50000000000000 : ℝ), (3578132550009/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5401476723/10000000000 : ℝ)|^4343 ≤ (44666866376649/100000000000000 : ℝ)^3319
        have hw : |(5401476723/10000000000 : ℝ)|=(5401476723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2530574291/5000000000 : ℝ)|^4343 ≤ (20510301706717/50000000000000 : ℝ)^3319
        have hw : |(2530574291/5000000000 : ℝ)|=(2530574291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-452702659/2000000000 : ℝ)|^4343 ≤ (3578132550009/25000000000000 : ℝ)^3319
        have hw : |(-452702659/2000000000 : ℝ)|=(452702659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s1_3 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1071240821/2500000000 : ℝ)*x 0 + (1862127253/5000000000 : ℝ)*x 1 + (4921855851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071240821/2500000000 : ℝ)^4343 ≤ (32990809565331/100000000000000 : ℝ)^3319 := by
    have hnat : (1071240821 : ℕ)^4343*100000000000000^3319 ≤ 32990809565331^3319*2500000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071240821 2500000000 32990809565331 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1862127253/5000000000 : ℝ)^4343 ≤ (6864889681543/25000000000000 : ℝ)^3319 := by
    have hnat : (1862127253 : ℕ)^4343*25000000000000^3319 ≤ 6864889681543^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862127253 5000000000 6864889681543 25000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4921855851/10000000000 : ℝ)^4343 ≤ (19774815846379/50000000000000 : ℝ)^3319 := by
    have hnat : (4921855851 : ℕ)^4343*50000000000000^3319 ≤ 19774815846379^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4921855851 10000000000 19774815846379 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071240821/2500000000 : ℝ), (1862127253/5000000000 : ℝ), (4921855851/10000000000 : ℝ)] ![(32990809565331/100000000000000 : ℝ), (6864889681543/25000000000000 : ℝ), (19774815846379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071240821/2500000000 : ℝ)|^4343 ≤ (32990809565331/100000000000000 : ℝ)^3319
        have hw : |(1071240821/2500000000 : ℝ)|=(1071240821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1862127253/5000000000 : ℝ)|^4343 ≤ (6864889681543/25000000000000 : ℝ)^3319
        have hw : |(1862127253/5000000000 : ℝ)|=(1862127253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4921855851/10000000000 : ℝ)|^4343 ≤ (19774815846379/50000000000000 : ℝ)^3319
        have hw : |(4921855851/10000000000 : ℝ)|=(4921855851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s1_4 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-982268647/5000000000 : ℝ)*x 0 + (5067993401/10000000000 : ℝ)*x 1 + (1123450243/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (982268647/5000000000 : ℝ)^4343 ≤ (5945415797217/50000000000000 : ℝ)^3319 := by
    have hnat : (982268647 : ℕ)^4343*50000000000000^3319 ≤ 5945415797217^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982268647 5000000000 5945415797217 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5067993401/10000000000 : ℝ)^4343 ≤ (10273303003719/25000000000000 : ℝ)^3319 := by
    have hnat : (5067993401 : ℕ)^4343*25000000000000^3319 ≤ 10273303003719^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5067993401 10000000000 10273303003719 25000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123450243/2000000000 : ℝ)^4343 ≤ (4701595637591/10000000000000 : ℝ)^3319 := by
    have hnat : (1123450243 : ℕ)^4343*10000000000000^3319 ≤ 4701595637591^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123450243 2000000000 4701595637591 10000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-982268647/5000000000 : ℝ), (5067993401/10000000000 : ℝ), (1123450243/2000000000 : ℝ)] ![(5945415797217/50000000000000 : ℝ), (10273303003719/25000000000000 : ℝ), (4701595637591/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-982268647/5000000000 : ℝ)|^4343 ≤ (5945415797217/50000000000000 : ℝ)^3319
        have hw : |(-982268647/5000000000 : ℝ)|=(982268647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5067993401/10000000000 : ℝ)|^4343 ≤ (10273303003719/25000000000000 : ℝ)^3319
        have hw : |(5067993401/10000000000 : ℝ)|=(5067993401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123450243/2000000000 : ℝ)|^4343 ≤ (4701595637591/10000000000000 : ℝ)^3319
        have hw : |(1123450243/2000000000 : ℝ)|=(1123450243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s1_5 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627439667/5000000000 : ℝ)*x 0 + (-1707411057/10000000000 : ℝ)*x 1 + (702156411/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627439667/5000000000 : ℝ)^4343 ≤ (21543631349073/50000000000000 : ℝ)^3319 := by
    have hnat : (2627439667 : ℕ)^4343*50000000000000^3319 ≤ 21543631349073^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627439667 5000000000 21543631349073 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1707411057/10000000000 : ℝ)^4343 ≤ (4948390050959/50000000000000 : ℝ)^3319 := by
    have hnat : (1707411057 : ℕ)^4343*50000000000000^3319 ≤ 4948390050959^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1707411057 10000000000 4948390050959 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (702156411/1250000000 : ℝ)^4343 ≤ (1880638287017/4000000000000 : ℝ)^3319 := by
    have hnat : (702156411 : ℕ)^4343*4000000000000^3319 ≤ 1880638287017^3319*1250000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702156411 1250000000 1880638287017 4000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627439667/5000000000 : ℝ), (-1707411057/10000000000 : ℝ), (702156411/1250000000 : ℝ)] ![(21543631349073/50000000000000 : ℝ), (4948390050959/50000000000000 : ℝ), (1880638287017/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627439667/5000000000 : ℝ)|^4343 ≤ (21543631349073/50000000000000 : ℝ)^3319
        have hw : |(2627439667/5000000000 : ℝ)|=(2627439667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1707411057/10000000000 : ℝ)|^4343 ≤ (4948390050959/50000000000000 : ℝ)^3319
        have hw : |(-1707411057/10000000000 : ℝ)|=(1707411057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(702156411/1250000000 : ℝ)|^4343 ≤ (1880638287017/4000000000000 : ℝ)^3319
        have hw : |(702156411/1250000000 : ℝ)|=(702156411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s1_6 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254879677/10000000000 : ℝ)*x 0 + (1123450321/2000000000 : ℝ)*x 1 + (-341482023/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254879677/10000000000 : ℝ)^4343 ≤ (21543633189137/50000000000000 : ℝ)^3319 := by
    have hnat : (5254879677 : ℕ)^4343*50000000000000^3319 ≤ 21543633189137^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254879677 10000000000 21543633189137 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123450321/2000000000 : ℝ)^4343 ≤ (23507980323647/50000000000000 : ℝ)^3319 := by
    have hnat : (1123450321 : ℕ)^4343*50000000000000^3319 ≤ 23507980323647^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123450321 2000000000 23507980323647 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341482023/2000000000 : ℝ)^4343 ≤ (9896772957131/100000000000000 : ℝ)^3319 := by
    have hnat : (341482023 : ℕ)^4343*100000000000000^3319 ≤ 9896772957131^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341482023 2000000000 9896772957131 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254879677/10000000000 : ℝ), (1123450321/2000000000 : ℝ), (-341482023/2000000000 : ℝ)] ![(21543633189137/50000000000000 : ℝ), (23507980323647/50000000000000 : ℝ), (9896772957131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254879677/10000000000 : ℝ)|^4343 ≤ (21543633189137/50000000000000 : ℝ)^3319
        have hw : |(5254879677/10000000000 : ℝ)|=(5254879677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123450321/2000000000 : ℝ)|^4343 ≤ (23507980323647/50000000000000 : ℝ)^3319
        have hw : |(1123450321/2000000000 : ℝ)|=(1123450321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-341482023/2000000000 : ℝ)|^4343 ≤ (9896772957131/100000000000000 : ℝ)^3319
        have hw : |(-341482023/2000000000 : ℝ)|=(341482023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s1_7 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2142978253/5000000000 : ℝ)*x 0 + (4907298001/10000000000 : ℝ)*x 1 + (3739066607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142978253/5000000000 : ℝ)^4343 ≤ (660016325041/2000000000000 : ℝ)^3319 := by
    have hnat : (2142978253 : ℕ)^4343*2000000000000^3319 ≤ 660016325041^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142978253 5000000000 660016325041 2000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4907298001/10000000000 : ℝ)^4343 ≤ (39396630424693/100000000000000 : ℝ)^3319 := by
    have hnat : (4907298001 : ℕ)^4343*100000000000000^3319 ≤ 39396630424693^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4907298001 10000000000 39396630424693 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3739066607/10000000000 : ℝ)^4343 ≤ (69006383263/250000000000 : ℝ)^3319 := by
    have hnat : (3739066607 : ℕ)^4343*250000000000^3319 ≤ 69006383263^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3739066607 10000000000 69006383263 250000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2142978253/5000000000 : ℝ), (4907298001/10000000000 : ℝ), (3739066607/10000000000 : ℝ)] ![(660016325041/2000000000000 : ℝ), (39396630424693/100000000000000 : ℝ), (69006383263/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2142978253/5000000000 : ℝ)|^4343 ≤ (660016325041/2000000000000 : ℝ)^3319
        have hw : |(2142978253/5000000000 : ℝ)|=(2142978253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4907298001/10000000000 : ℝ)|^4343 ≤ (39396630424693/100000000000000 : ℝ)^3319
        have hw : |(4907298001/10000000000 : ℝ)|=(4907298001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3739066607/10000000000 : ℝ)|^4343 ≤ (69006383263/250000000000 : ℝ)^3319
        have hw : |(3739066607/10000000000 : ℝ)|=(3739066607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1383_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39086603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26579/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (859/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (363/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9581/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26579/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (859/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26579/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (859/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26579/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (859/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26579/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (859/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26579/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (859/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26579/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (859/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (859/50000 : ℝ) ^ (2171/512 : ℝ) ≤ (3281591588403/100000000000000000000 : ℝ) := by
    have hpowers : (859/50000 : ℝ)^2171 ≤ (3281591588403/100000000000000000000 : ℝ)^512 := by
      have hnat : (859 : ℕ)^2171*100000000000000000000^512 ≤ 3281591588403^512*50000^2171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        859 50000 3281591588403 100000000000000000000 2171 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (859/50000 : ℝ)) (X := (3281591588403/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hpowhi : (26579/100000 : ℝ) ^ (2171/512 : ℝ) ≤ (36300194144058413/10000000000000000000 : ℝ) := by
    have hpowers : (26579/100000 : ℝ)^2171 ≤ (36300194144058413/10000000000000000000 : ℝ)^512 := by
      have hnat : (26579 : ℕ)^2171*10000000000000000000^512 ≤ 36300194144058413^512*100000^2171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26579 100000 36300194144058413 10000000000000000000 2171 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26579/100000 : ℝ)) (X := (36300194144058413/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000003281591588403/50000000000000000000 : ℝ) ≤ (10000000154783497/10000000000000000 : ℝ) ^ (2171/512 : ℝ) := by
    have hpowers : (50000003281591588403/50000000000000000000 : ℝ)^512 ≤ (10000000154783497/10000000000000000 : ℝ)^2171 := by
      have hnat : (50000003281591588403 : ℕ)^512*10000000000000000^2171 ≤ 10000000154783497^2171*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000003281591588403 50000000000000000000 10000000154783497 10000000000000000 512 2171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000154783497/10000000000000000 : ℝ)) (X := (50000003281591588403/50000000000000000000 : ℝ)) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100363005223032172533/100000000000000000000 : ℝ) ≤ (2502137280530639/2500000000000000 : ℝ) ^ (2171/512 : ℝ) := by
    have hpowers : (100363005223032172533/100000000000000000000 : ℝ)^512 ≤ (2502137280530639/2500000000000000 : ℝ)^2171 := by
      have hnat : (100363005223032172533 : ℕ)^512*2500000000000000^2171 ≤ 2502137280530639^2171*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100363005223032172533 100000000000000000000 2502137280530639 2500000000000000 512 2171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502137280530639/2500000000000000 : ℝ)) (X := (100363005223032172533/100000000000000000000 : ℝ)) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5036300194144058413/5000000000000000000 : ℝ) ≤ (2003419617892323/2000000000000000 : ℝ) ^ (2171/512 : ℝ) := by
    have hpowers : (5036300194144058413/5000000000000000000 : ℝ)^512 ≤ (2003419617892323/2000000000000000 : ℝ)^2171 := by
      have hnat : (5036300194144058413 : ℕ)^512*2000000000000000^2171 ≤ 2003419617892323^2171*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5036300194144058413 5000000000000000000 2003419617892323 2000000000000000 512 2171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2003419617892323/2000000000000000 : ℝ)) (X := (5036300194144058413/5000000000000000000 : ℝ)) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3281591588403/100000000000000000000 : ℝ) ≤ ((248580629596295512193/248610000000000000000 : ℝ)+2*(8548967339059/2486100000000000 : ℝ)*(859/50000 : ℝ))^(2171/512 : ℝ) := by
    rw [show (248580629596295512193/248610000000000000000 : ℝ)+2*(8548967339059/2486100000000000 : ℝ)*(859/50000 : ℝ)=(10000000154783497/10000000000000000 : ℝ) by norm_num, show 1+2*(3281591588403/100000000000000000000 : ℝ)=(50000003281591588403/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36300194144058413/10000000000000000000 : ℝ)+(3281591588403/100000000000000000000 : ℝ) ≤ ((248580629596295512193/248610000000000000000 : ℝ)+(8548967339059/2486100000000000 : ℝ)*((26579/100000 : ℝ)+(859/50000 : ℝ)))^(2171/512 : ℝ) := by
    rw [show (248580629596295512193/248610000000000000000 : ℝ)+(8548967339059/2486100000000000 : ℝ)*((26579/100000 : ℝ)+(859/50000 : ℝ))=(2502137280530639/2500000000000000 : ℝ) by norm_num, show 1+(36300194144058413/10000000000000000000 : ℝ)+(3281591588403/100000000000000000000 : ℝ)=(100363005223032172533/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36300194144058413/10000000000000000000 : ℝ) ≤ ((248580629596295512193/248610000000000000000 : ℝ)+2*(8548967339059/2486100000000000 : ℝ)*(26579/100000 : ℝ))^(2171/512 : ℝ) := by
    rw [show (248580629596295512193/248610000000000000000 : ℝ)+2*(8548967339059/2486100000000000 : ℝ)*(26579/100000 : ℝ)=(2003419617892323/2000000000000000 : ℝ) by norm_num, show 1+2*(36300194144058413/10000000000000000000 : ℝ)=(5036300194144058413/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (248580629596295512193/248610000000000000000 : ℝ)*(X 1 0+X 2 0)+(8548967339059/2486100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2171/512 : ℝ)) (lo := (859/50000 : ℝ)) (hi := (26579/100000 : ℝ)) (c := (248580629596295512193/248610000000000000000 : ℝ)) (alpha := (8548967339059/2486100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (248580629596295512193/248610000000000000000 : ℝ)*(X 0 1+X 2 1)+(8548967339059/2486100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2171/512 : ℝ)) (lo := (859/50000 : ℝ)) (hi := (26579/100000 : ℝ)) (c := (248580629596295512193/248610000000000000000 : ℝ)) (alpha := (8548967339059/2486100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (248580629596295512193/248610000000000000000 : ℝ)*(X 0 2+X 1 2)+(8548967339059/2486100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2171/512 : ℝ)) (lo := (859/50000 : ℝ)) (hi := (26579/100000 : ℝ)) (c := (248580629596295512193/248610000000000000000 : ℝ)) (alpha := (8548967339059/2486100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-491017757/2500000000 : ℝ)*X 0 0+(281210839/500000000 : ℝ)*X 0 1+(2530574199/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2700737993/5000000000 : ℝ)*X 1 0+(-452702529/2000000000 : ℝ)*X 1 1+(5061149841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5401476723/10000000000 : ℝ)*X 2 0+(2530574291/5000000000 : ℝ)*X 2 1+(-452702659/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1071240821/2500000000 : ℝ)*X 0 0+(1862127253/5000000000 : ℝ)*X 0 1+(4921855851/10000000000 : ℝ)*X 0 2+(1071240821/2500000000 : ℝ)*X 1 0+(1862127253/5000000000 : ℝ)*X 1 1+(4921855851/10000000000 : ℝ)*X 1 2+(1071240821/2500000000 : ℝ)*X 2 0+(1862127253/5000000000 : ℝ)*X 2 1+(4921855851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-982268647/5000000000 : ℝ)*X 0 0+(5067993401/10000000000 : ℝ)*X 0 1+(1123450243/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2627439667/5000000000 : ℝ)*X 1 0+(-1707411057/10000000000 : ℝ)*X 1 1+(702156411/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5254879677/10000000000 : ℝ)*X 2 0+(1123450321/2000000000 : ℝ)*X 2 1+(-341482023/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2142978253/5000000000 : ℝ)*X 0 0+(4907298001/10000000000 : ℝ)*X 0 1+(3739066607/10000000000 : ℝ)*X 0 2+(2142978253/5000000000 : ℝ)*X 1 0+(4907298001/10000000000 : ℝ)*X 1 1+(3739066607/10000000000 : ℝ)*X 1 2+(2142978253/5000000000 : ℝ)*X 2 0+(4907298001/10000000000 : ℝ)*X 2 1+(3739066607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41170630789826266437163783437/4143500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7261281/100000000000000 : ℝ)*(base1) + (216174293/12500000000000 : ℝ)*(base19) + (492930231/25000000000000 : ℝ)*(base23) + (287194489/100000000000000 : ℝ)*(upper3) + (63132723/100000000000000 : ℝ)*(upper5) + (130551438180091/10000000000000 : ℝ)*(major0) + (130551438180091/10000000000000 : ℝ)*(major1) + (1305514381800911/100000000000000 : ℝ)*(major2) + (1775999732605431/100000000000000 : ℝ)*(sp0) + (1776012732996339/100000000000000 : ℝ)*(sp1) + (1776012490669759/100000000000000 : ℝ)*(sp2) + (208751854941069/25000000000000 : ℝ)*(sp3) + (14737046533/100000000000000 : ℝ)*(sp4) + (327148951/5000000000000 : ℝ)*(sp7) + (26094186562643/3125000000000 : ℝ)*(f.failure) + (1776014462390683/100000000000000 : ℝ)*(f.sum) + (87415272387767/82870000000000000000000000000 : ℝ)*base66 + (32749192319565060437/2486100000000000000000000000000000 : ℝ)*base68 + (74897234091579007823/24861000000000000000000000000000000 : ℝ)*base69 + (17404570847115960437/2486100000000000000000000000000000 : ℝ)*base72 + (518809003331457/82870000000000000000000000000 : ℝ)*base74 + (121986579341853007823/24861000000000000000000000000000000 : ℝ)*base75 + (8302947575138283479/828700000000000000000000000000000 : ℝ)*base78 + (3793105950329383479/828700000000000000000000000000000 : ℝ)*base80 + (11991993308833/24861000000000000000000000000 : ℝ)*base82 + (634229/78125000000000000000 : ℝ)*base89 + (634229/78125000000000000000 : ℝ)*base91 + (147021/78125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3821033537922713105517502287/1035875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (182417/125000000000 : ℝ)*(base1) + (856461/80000000000 : ℝ)*(base19) + (633650793/50000000000000 : ℝ)*(base23) + (12917487/12500000000000 : ℝ)*(upper3) + (155786439/100000000000000 : ℝ)*(upper5) + (669158675975359/50000000000000 : ℝ)*(major0) + (669158675975359/50000000000000 : ℝ)*(major1) + (669158675975359/50000000000000 : ℝ)*(major2) + (1068808123/20000000000000 : ℝ)*(sp1) + (508497371/6250000000000 : ℝ)*(sp2) + (455159950499781/25000000000000 : ℝ)*(sp4) + (910316620724329/50000000000000 : ℝ)*(sp5) + (910315126403001/50000000000000 : ℝ)*(sp6) + (213998694736399/25000000000000 : ℝ)*(sp7) + (213998731219799/25000000000000 : ℝ)*(f.failure) + (455159914016381/25000000000000 : ℝ)*(f.sum) + (83804025946381/62152500000000000000000000000 : ℝ)*base65 + (6716295973763282571/4143500000000000000000000000000000 : ℝ)*base68 + (4947908646835282571/4143500000000000000000000000000000 : ℝ)*base70 + (7066151761253717429/4143500000000000000000000000000000 : ℝ)*base71 + (269221386082787/124305000000000000000000000000 : ℝ)*base73 + (2143704109301782571/4143500000000000000000000000000000 : ℝ)*base76 + (23873942497266282571/4143500000000000000000000000000000 : ℝ)*base78 + (25139951216416282571/4143500000000000000000000000000000 : ℝ)*base80 + (45440780480663/31076250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1752797/625000000000000000000 : ℝ)*base89 + (1752797/625000000000000000000 : ℝ)*base91 + (1752797/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1383_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39086603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26579/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (859/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (363/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9581/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1383_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1383_s2_0 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1000390973/5000000000 : ℝ)*x 0 + (5469040291/10000000000 : ℝ)*x 1 + (5192754763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1000390973/5000000000 : ℝ)^4343 ≤ (12178708973639/100000000000000 : ℝ)^3319 := by
    have hnat : (1000390973 : ℕ)^4343*100000000000000^3319 ≤ 12178708973639^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000390973 5000000000 12178708973639 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469040291/10000000000 : ℝ)^4343 ≤ (45399358450479/100000000000000 : ℝ)^3319 := by
    have hnat : (5469040291 : ℕ)^4343*100000000000000^3319 ≤ 45399358450479^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469040291 10000000000 45399358450479 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5192754763/10000000000 : ℝ)^4343 ≤ (21210966278061/50000000000000 : ℝ)^3319 := by
    have hnat : (5192754763 : ℕ)^4343*50000000000000^3319 ≤ 21210966278061^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192754763 10000000000 21210966278061 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1000390973/5000000000 : ℝ), (5469040291/10000000000 : ℝ), (5192754763/10000000000 : ℝ)] ![(12178708973639/100000000000000 : ℝ), (45399358450479/100000000000000 : ℝ), (21210966278061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1000390973/5000000000 : ℝ)|^4343 ≤ (12178708973639/100000000000000 : ℝ)^3319
        have hw : |(-1000390973/5000000000 : ℝ)|=(1000390973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469040291/10000000000 : ℝ)|^4343 ≤ (45399358450479/100000000000000 : ℝ)^3319
        have hw : |(5469040291/10000000000 : ℝ)|=(5469040291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5192754763/10000000000 : ℝ)|^4343 ≤ (21210966278061/50000000000000 : ℝ)^3319
        have hw : |(5192754763/10000000000 : ℝ)|=(5192754763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s2_1 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363136813/10000000000 : ℝ)*x 0 + (-1071617801/5000000000 : ℝ)*x 1 + (5192754709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363136813/10000000000 : ℝ)^4343 ≤ (44252456533409/100000000000000 : ℝ)^3319 := by
    have hnat : (5363136813 : ℕ)^4343*100000000000000^3319 ≤ 44252456533409^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363136813 10000000000 44252456533409 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1071617801/5000000000 : ℝ)^4343 ≤ (2665122295627/20000000000000 : ℝ)^3319 := by
    have hnat : (1071617801 : ℕ)^4343*20000000000000^3319 ≤ 2665122295627^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071617801 5000000000 2665122295627 20000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5192754709/10000000000 : ℝ)^4343 ≤ (8484386395773/20000000000000 : ℝ)^3319 := by
    have hnat : (5192754709 : ℕ)^4343*20000000000000^3319 ≤ 8484386395773^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192754709 10000000000 8484386395773 20000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363136813/10000000000 : ℝ), (-1071617801/5000000000 : ℝ), (5192754709/10000000000 : ℝ)] ![(44252456533409/100000000000000 : ℝ), (2665122295627/20000000000000 : ℝ), (8484386395773/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363136813/10000000000 : ℝ)|^4343 ≤ (44252456533409/100000000000000 : ℝ)^3319
        have hw : |(5363136813/10000000000 : ℝ)|=(5363136813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1071617801/5000000000 : ℝ)|^4343 ≤ (2665122295627/20000000000000 : ℝ)^3319
        have hw : |(-1071617801/5000000000 : ℝ)|=(1071617801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5192754709/10000000000 : ℝ)|^4343 ≤ (8484386395773/20000000000000 : ℝ)^3319
        have hw : |(5192754709/10000000000 : ℝ)|=(5192754709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s2_2 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363136681/10000000000 : ℝ)*x 0 + (5192754837/10000000000 : ℝ)*x 1 + (-267904451/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363136681/10000000000 : ℝ)^4343 ≤ (11063113777053/25000000000000 : ℝ)^3319 := by
    have hnat : (5363136681 : ℕ)^4343*25000000000000^3319 ≤ 11063113777053^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363136681 10000000000 11063113777053 25000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5192754837/10000000000 : ℝ)^4343 ≤ (42421933347177/100000000000000 : ℝ)^3319 := by
    have hnat : (5192754837 : ℕ)^4343*100000000000000^3319 ≤ 42421933347177^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192754837 10000000000 42421933347177 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (267904451/1250000000 : ℝ)^4343 ≤ (13325611526949/100000000000000 : ℝ)^3319 := by
    have hnat : (267904451 : ℕ)^4343*100000000000000^3319 ≤ 13325611526949^3319*1250000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267904451 1250000000 13325611526949 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363136681/10000000000 : ℝ), (5192754837/10000000000 : ℝ), (-267904451/1250000000 : ℝ)] ![(11063113777053/25000000000000 : ℝ), (42421933347177/100000000000000 : ℝ), (13325611526949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363136681/10000000000 : ℝ)|^4343 ≤ (11063113777053/25000000000000 : ℝ)^3319
        have hw : |(5363136681/10000000000 : ℝ)|=(5363136681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5192754837/10000000000 : ℝ)|^4343 ≤ (42421933347177/100000000000000 : ℝ)^3319
        have hw : |(5192754837/10000000000 : ℝ)|=(5192754837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-267904451/1250000000 : ℝ)|^4343 ≤ (13325611526949/100000000000000 : ℝ)^3319
        have hw : |(-267904451/1250000000 : ℝ)|=(267904451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s2_3 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4310751011/10000000000 : ℝ)*x 0 + (4026099807/10000000000 : ℝ)*x 1 + (184549579/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310751011/10000000000 : ℝ)^4343 ≤ (665017036813/2000000000000 : ℝ)^3319 := by
    have hnat : (4310751011 : ℕ)^4343*2000000000000^3319 ≤ 665017036813^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310751011 10000000000 665017036813 2000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4026099807/10000000000 : ℝ)^4343 ≤ (3800938947827/12500000000000 : ℝ)^3319 := by
    have hnat : (4026099807 : ℕ)^4343*12500000000000^3319 ≤ 3800938947827^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026099807 10000000000 3800938947827 12500000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184549579/400000000 : ℝ)^4343 ≤ (7268327312757/20000000000000 : ℝ)^3319 := by
    have hnat : (184549579 : ℕ)^4343*20000000000000^3319 ≤ 7268327312757^3319*400000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184549579 400000000 7268327312757 20000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310751011/10000000000 : ℝ), (4026099807/10000000000 : ℝ), (184549579/400000000 : ℝ)] ![(665017036813/2000000000000 : ℝ), (3800938947827/12500000000000 : ℝ), (7268327312757/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310751011/10000000000 : ℝ)|^4343 ≤ (665017036813/2000000000000 : ℝ)^3319
        have hw : |(4310751011/10000000000 : ℝ)|=(4310751011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4026099807/10000000000 : ℝ)|^4343 ≤ (3800938947827/12500000000000 : ℝ)^3319
        have hw : |(4026099807/10000000000 : ℝ)|=(4026099807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(184549579/400000000 : ℝ)|^4343 ≤ (7268327312757/20000000000000 : ℝ)^3319
        have hw : |(184549579/400000000 : ℝ)|=(184549579/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s2_4 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2000836817/10000000000 : ℝ)*x 0 + (5194412479/10000000000 : ℝ)*x 1 + (2733684241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2000836817/10000000000 : ℝ)^4343 ≤ (12179146021281/100000000000000 : ℝ)^3319 := by
    have hnat : (2000836817 : ℕ)^4343*100000000000000^3319 ≤ 12179146021281^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000836817 10000000000 12179146021281 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5194412479/10000000000 : ℝ)^4343 ≤ (42439654311111/100000000000000 : ℝ)^3319 := by
    have hnat : (5194412479 : ℕ)^4343*100000000000000^3319 ≤ 42439654311111^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194412479 10000000000 42439654311111 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733684241/5000000000 : ℝ)^4343 ≤ (22690599821021/50000000000000 : ℝ)^3319 := by
    have hnat : (2733684241 : ℕ)^4343*50000000000000^3319 ≤ 22690599821021^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733684241 5000000000 22690599821021 50000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2000836817/10000000000 : ℝ), (5194412479/10000000000 : ℝ), (2733684241/5000000000 : ℝ)] ![(12179146021281/100000000000000 : ℝ), (42439654311111/100000000000000 : ℝ), (22690599821021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2000836817/10000000000 : ℝ)|^4343 ≤ (12179146021281/100000000000000 : ℝ)^3319
        have hw : |(-2000836817/10000000000 : ℝ)|=(2000836817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5194412479/10000000000 : ℝ)|^4343 ≤ (42439654311111/100000000000000 : ℝ)^3319
        have hw : |(5194412479/10000000000 : ℝ)|=(5194412479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2733684241/5000000000 : ℝ)|^4343 ≤ (22690599821021/50000000000000 : ℝ)^3319
        have hw : |(2733684241/5000000000 : ℝ)|=(2733684241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s2_5 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5291616307/10000000000 : ℝ)*x 0 + (-373724493/2000000000 : ℝ)*x 1 + (546736817/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291616307/10000000000 : ℝ)^4343 ≤ (10870461673631/25000000000000 : ℝ)^3319 := by
    have hnat : (5291616307 : ℕ)^4343*25000000000000^3319 ≤ 10870461673631^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291616307 10000000000 10870461673631 25000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (373724493/2000000000 : ℝ)^4343 ≤ (11136957032907/100000000000000 : ℝ)^3319 := by
    have hnat : (373724493 : ℕ)^4343*100000000000000^3319 ≤ 11136957032907^3319*2000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373724493 2000000000 11136957032907 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546736817/1000000000 : ℝ)^4343 ≤ (45381196253329/100000000000000 : ℝ)^3319 := by
    have hnat : (546736817 : ℕ)^4343*100000000000000^3319 ≤ 45381196253329^3319*1000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546736817 1000000000 45381196253329 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291616307/10000000000 : ℝ), (-373724493/2000000000 : ℝ), (546736817/1000000000 : ℝ)] ![(10870461673631/25000000000000 : ℝ), (11136957032907/100000000000000 : ℝ), (45381196253329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291616307/10000000000 : ℝ)|^4343 ≤ (10870461673631/25000000000000 : ℝ)^3319
        have hw : |(5291616307/10000000000 : ℝ)|=(5291616307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-373724493/2000000000 : ℝ)|^4343 ≤ (11136957032907/100000000000000 : ℝ)^3319
        have hw : |(-373724493/2000000000 : ℝ)|=(373724493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546736817/1000000000 : ℝ)|^4343 ≤ (45381196253329/100000000000000 : ℝ)^3319
        have hw : |(546736817/1000000000 : ℝ)|=(546736817/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s2_6 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2645808889/5000000000 : ℝ)*x 0 + (546736823/1000000000 : ℝ)*x 1 + (-1868620353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645808889/5000000000 : ℝ)^4343 ≤ (43481862511189/100000000000000 : ℝ)^3319 := by
    have hnat : (2645808889 : ℕ)^4343*100000000000000^3319 ≤ 43481862511189^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645808889 5000000000 43481862511189 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546736823/1000000000 : ℝ)^4343 ≤ (11345299226251/25000000000000 : ℝ)^3319 := by
    have hnat : (546736823 : ℕ)^4343*25000000000000^3319 ≤ 11345299226251^3319*1000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546736823 1000000000 11345299226251 25000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1868620353/10000000000 : ℝ)^4343 ≤ (11136940561853/100000000000000 : ℝ)^3319 := by
    have hnat : (1868620353 : ℕ)^4343*100000000000000^3319 ≤ 11136940561853^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868620353 10000000000 11136940561853 100000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645808889/5000000000 : ℝ), (546736823/1000000000 : ℝ), (-1868620353/10000000000 : ℝ)] ![(43481862511189/100000000000000 : ℝ), (11345299226251/25000000000000 : ℝ), (11136940561853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645808889/5000000000 : ℝ)|^4343 ≤ (43481862511189/100000000000000 : ℝ)^3319
        have hw : |(2645808889/5000000000 : ℝ)|=(2645808889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546736823/1000000000 : ℝ)|^4343 ≤ (11345299226251/25000000000000 : ℝ)^3319
        have hw : |(546736823/1000000000 : ℝ)|=(546736823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1868620353/10000000000 : ℝ)|^4343 ≤ (11136940561853/100000000000000 : ℝ)^3319
        have hw : |(-1868620353/10000000000 : ℝ)|=(1868620353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1383_s2_7 (p : ℝ) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2155434637/5000000000 : ℝ)*x 0 + (4610214213/10000000000 : ℝ)*x 1 + (4029654707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155434637/5000000000 : ℝ)^4343 ≤ (3325204550753/10000000000000 : ℝ)^3319 := by
    have hnat : (2155434637 : ℕ)^4343*10000000000000^3319 ≤ 3325204550753^3319*5000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155434637 5000000000 3325204550753 10000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4610214213/10000000000 : ℝ)^4343 ≤ (7261061165693/20000000000000 : ℝ)^3319 := by
    have hnat : (4610214213 : ℕ)^4343*20000000000000^3319 ≤ 7261061165693^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4610214213 10000000000 7261061165693 20000000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4029654707/10000000000 : ℝ)^4343 ≤ (3805331080609/12500000000000 : ℝ)^3319 := by
    have hnat : (4029654707 : ℕ)^4343*12500000000000^3319 ≤ 3805331080609^3319*10000000000^4343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029654707 10000000000 3805331080609 12500000000000 4343 3319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4343/1024 : ℝ)) 4343 3319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155434637/5000000000 : ℝ), (4610214213/10000000000 : ℝ), (4029654707/10000000000 : ℝ)] ![(3325204550753/10000000000000 : ℝ), (7261061165693/20000000000000 : ℝ), (3805331080609/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155434637/5000000000 : ℝ)|^4343 ≤ (3325204550753/10000000000000 : ℝ)^3319
        have hw : |(2155434637/5000000000 : ℝ)|=(2155434637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4610214213/10000000000 : ℝ)|^4343 ≤ (7261061165693/20000000000000 : ℝ)^3319
        have hw : |(4610214213/10000000000 : ℝ)|=(4610214213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4029654707/10000000000 : ℝ)|^4343 ≤ (3805331080609/12500000000000 : ℝ)^3319
        have hw : |(4029654707/10000000000 : ℝ)|=(4029654707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1383_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39086603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9581/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (363/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (2527/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15951/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9581/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (363/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9581/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (363/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9581/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (363/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9581/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (363/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9581/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (363/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9581/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (363/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (363/5000 : ℝ) ^ (2171/512 : ℝ) ≤ (1479463665849903/100000000000000000000 : ℝ) := by
    have hpowers : (363/5000 : ℝ)^2171 ≤ (1479463665849903/100000000000000000000 : ℝ)^512 := by
      have hnat : (363 : ℕ)^2171*100000000000000000000^512 ≤ 1479463665849903^512*5000^2171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        363 5000 1479463665849903 100000000000000000000 2171 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (363/5000 : ℝ)) (X := (1479463665849903/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hpowhi : (9581/50000 : ℝ) ^ (2171/512 : ℝ) ≤ (45326373204993199/50000000000000000000 : ℝ) := by
    have hpowers : (9581/50000 : ℝ)^2171 ≤ (45326373204993199/50000000000000000000 : ℝ)^512 := by
      have hnat : (9581 : ℕ)^2171*50000000000000000000^512 ≤ 45326373204993199^512*50000^2171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9581 50000 45326373204993199 50000000000000000000 2171 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9581/50000 : ℝ)) (X := (45326373204993199/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001479463665849903/50000000000000000000 : ℝ) ≤ (10000069781375707/10000000000000000 : ℝ) ^ (2171/512 : ℝ) := by
    have hpowers : (50001479463665849903/50000000000000000000 : ℝ)^512 ≤ (10000069781375707/10000000000000000 : ℝ)^2171 := by
      have hnat : (50001479463665849903 : ℕ)^512*10000000000000000^2171 ≤ 10000069781375707^2171*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001479463665849903 50000000000000000000 10000069781375707 10000000000000000 512 2171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000069781375707/10000000000000000 : ℝ)) (X := (50001479463665849903/50000000000000000000 : ℝ)) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100092132210075836301/100000000000000000000 : ℝ) ≤ (5001086022458393/5000000000000000 : ℝ) ^ (2171/512 : ℝ) := by
    have hpowers : (100092132210075836301/100000000000000000000 : ℝ)^512 ≤ (5001086022458393/5000000000000000 : ℝ)^2171 := by
      have hnat : (100092132210075836301 : ℕ)^512*5000000000000000^2171 ≤ 5001086022458393^2171*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100092132210075836301 100000000000000000000 5001086022458393 5000000000000000 512 2171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001086022458393/5000000000000000 : ℝ)) (X := (100092132210075836301/100000000000000000000 : ℝ)) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25045326373204993199/25000000000000000000 : ℝ) ≤ (2000854861691573/2000000000000000 : ℝ) ^ (2171/512 : ℝ) := by
    have hpowers : (25045326373204993199/25000000000000000000 : ℝ)^512 ≤ (2000854861691573/2000000000000000 : ℝ)^2171 := by
      have hnat : (25045326373204993199 : ℕ)^512*2000000000000000^2171 ≤ 2000854861691573^2171*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25045326373204993199 25000000000000000000 2000854861691573 2000000000000000 512 2171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000854861691573/2000000000000000 : ℝ)) (X := (25045326373204993199/25000000000000000000 : ℝ)) (by norm_num) 2171 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1479463665849903/100000000000000000000 : ℝ) ≤ ((5408650257787145347/5410000000000000000 : ℝ)+2*(2102263541079/1190200000000000 : ℝ)*(363/5000 : ℝ))^(2171/512 : ℝ) := by
    rw [show (5408650257787145347/5410000000000000000 : ℝ)+2*(2102263541079/1190200000000000 : ℝ)*(363/5000 : ℝ)=(10000069781375707/10000000000000000 : ℝ) by norm_num, show 1+2*(1479463665849903/100000000000000000000 : ℝ)=(50001479463665849903/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(45326373204993199/50000000000000000000 : ℝ)+(1479463665849903/100000000000000000000 : ℝ) ≤ ((5408650257787145347/5410000000000000000 : ℝ)+(2102263541079/1190200000000000 : ℝ)*((9581/50000 : ℝ)+(363/5000 : ℝ)))^(2171/512 : ℝ) := by
    rw [show (5408650257787145347/5410000000000000000 : ℝ)+(2102263541079/1190200000000000 : ℝ)*((9581/50000 : ℝ)+(363/5000 : ℝ))=(5001086022458393/5000000000000000 : ℝ) by norm_num, show 1+(45326373204993199/50000000000000000000 : ℝ)+(1479463665849903/100000000000000000000 : ℝ)=(100092132210075836301/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(45326373204993199/50000000000000000000 : ℝ) ≤ ((5408650257787145347/5410000000000000000 : ℝ)+2*(2102263541079/1190200000000000 : ℝ)*(9581/50000 : ℝ))^(2171/512 : ℝ) := by
    rw [show (5408650257787145347/5410000000000000000 : ℝ)+2*(2102263541079/1190200000000000 : ℝ)*(9581/50000 : ℝ)=(2000854861691573/2000000000000000 : ℝ) by norm_num, show 1+2*(45326373204993199/50000000000000000000 : ℝ)=(25045326373204993199/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5408650257787145347/5410000000000000000 : ℝ)*(X 1 0+X 2 0)+(2102263541079/1190200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2171/512 : ℝ)) (lo := (363/5000 : ℝ)) (hi := (9581/50000 : ℝ)) (c := (5408650257787145347/5410000000000000000 : ℝ)) (alpha := (2102263541079/1190200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5408650257787145347/5410000000000000000 : ℝ)*(X 0 1+X 2 1)+(2102263541079/1190200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2171/512 : ℝ)) (lo := (363/5000 : ℝ)) (hi := (9581/50000 : ℝ)) (c := (5408650257787145347/5410000000000000000 : ℝ)) (alpha := (2102263541079/1190200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5408650257787145347/5410000000000000000 : ℝ)*(X 0 2+X 1 2)+(2102263541079/1190200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2171/512 : ℝ)) (lo := (363/5000 : ℝ)) (hi := (9581/50000 : ℝ)) (c := (5408650257787145347/5410000000000000000 : ℝ)) (alpha := (2102263541079/1190200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1000390973/5000000000 : ℝ)*X 0 0+(5469040291/10000000000 : ℝ)*X 0 1+(5192754763/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5363136813/10000000000 : ℝ)*X 1 0+(-1071617801/5000000000 : ℝ)*X 1 1+(5192754709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5363136681/10000000000 : ℝ)*X 2 0+(5192754837/10000000000 : ℝ)*X 2 1+(-267904451/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4310751011/10000000000 : ℝ)*X 0 0+(4026099807/10000000000 : ℝ)*X 0 1+(184549579/400000000 : ℝ)*X 0 2+(4310751011/10000000000 : ℝ)*X 1 0+(4026099807/10000000000 : ℝ)*X 1 1+(184549579/400000000 : ℝ)*X 1 2+(4310751011/10000000000 : ℝ)*X 2 0+(4026099807/10000000000 : ℝ)*X 2 1+(184549579/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2000836817/10000000000 : ℝ)*X 0 0+(5194412479/10000000000 : ℝ)*X 0 1+(2733684241/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5291616307/10000000000 : ℝ)*X 1 0+(-373724493/2000000000 : ℝ)*X 1 1+(546736817/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2645808889/5000000000 : ℝ)*X 2 0+(546736823/1000000000 : ℝ)*X 2 1+(-1868620353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2155434637/5000000000 : ℝ)*X 0 0+(4610214213/10000000000 : ℝ)*X 0 1+(4029654707/10000000000 : ℝ)*X 0 2+(2155434637/5000000000 : ℝ)*X 1 0+(4610214213/10000000000 : ℝ)*X 1 1+(4029654707/10000000000 : ℝ)*X 1 2+(2155434637/5000000000 : ℝ)*X 2 0+(4610214213/10000000000 : ℝ)*X 2 1+(4029654707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1383_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8387733236243660914576273959/1487750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50677313/5000000000000 : ℝ)*(base19) + (3206379/390625000000 : ℝ)*(base23) + (5557779/10000000000000 : ℝ)*(lower2) + (88821681/50000000000000 : ℝ)*(upper3) + (35781941/50000000000000 : ℝ)*(upper5) + (1330300487999697/50000000000000 : ℝ)*(major0) + (1330300487999697/50000000000000 : ℝ)*(major1) + (1330300487999697/50000000000000 : ℝ)*(major2) + (3619456610258913/100000000000000 : ℝ)*(sp0) + (3619466158751039/100000000000000 : ℝ)*(sp1) + (904866587866069/25000000000000 : ℝ)*(sp2) + (850864138641529/50000000000000 : ℝ)*(sp3) + (5281019193/50000000000000 : ℝ)*(sp4) + (6314489597/100000000000000 : ℝ)*(sp7) + (340346918354531/20000000000000 : ℝ)*(f.failure) + (3619467172297299/100000000000000 : ℝ)*(f.sum) + (49659604551283/29755000000000000000000000000 : ℝ)*base65 + (27698766755121708449/2975500000000000000000000000000000 : ℝ)*base67 + (32206929678143708449/2975500000000000000000000000000000 : ℝ)*base69 + (15465241368407208449/2975500000000000000000000000000000 : ℝ)*base71 + (4423085036967/7438750000000000000000000000 : ℝ)*base73 + (41456598792653708449/2975500000000000000000000000000000 : ℝ)*base75 + (23458001948007708449/2975500000000000000000000000000000 : ℝ)*base77 + (9317852250779208449/2975500000000000000000000000000000 : ℝ)*base79 + (7995779386151/3719375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3551807/500000000000000000000 : ℝ)*base90 + (3551807/500000000000000000000 : ℝ)*base92 + (3551807/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1050250560269126434979344641/148775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74524489/6250000000000 : ℝ)*(base19) + (3427957177/100000000000000 : ℝ)*(base23) + (73224279/25000000000000 : ℝ)*(upper3) + (33333453/10000000000000 : ℝ)*(lower4) + (3285183/5000000000000 : ℝ)*(upper5) + (134651799727309/5000000000000 : ℝ)*(major0) + (134651799727309/5000000000000 : ℝ)*(major1) + (134651799727309/5000000000000 : ℝ)*(major2) + (2426431339/50000000000000 : ℝ)*(sp1) + (24149907931/50000000000000 : ℝ)*(sp2) + (1831795775472251/50000000000000 : ℝ)*(sp4) + (1831792752845001/50000000000000 : ℝ)*(sp5) + (3663539823171463/100000000000000 : ℝ)*(sp6) + (1722480202837133/100000000000000 : ℝ)*(sp7) + (1722480202837133/100000000000000 : ℝ)*(f.failure) + (1831795775472251/50000000000000 : ℝ)*(f.sum) + (285045924457/2975500000000000000000000000 : ℝ)*base65 + (2481286475728693453/297550000000000000000000000000000 : ℝ)*base67 + (822442485888293453/297550000000000000000000000000000 : ℝ)*base69 + (1010393588837956547/297550000000000000000000000000000 : ℝ)*base72 + (37701993492729/5951000000000000000000000000 : ℝ)*base73 + (1132729129870606547/297550000000000000000000000000000 : ℝ)*base76 + (1279171713511643453/297550000000000000000000000000000 : ℝ)*base77 + (1638206959017393453/297550000000000000000000000000000 : ℝ)*base79 + (6097440816437/2975500000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base85 + (8770801/2500000000000000000000 : ℝ)*base90 + (8770801/2500000000000000000000 : ℝ)*base92 + (8770801/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1383_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39086603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9581/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (363/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2527/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15951/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1383_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1383_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39086603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2527/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15951/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1383_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1383_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1383_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2171/512 : ℝ) ≤ p) (hpb : p ≤ (4343/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39086603/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2527/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15951/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1383_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1093_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:57:21.92033+00:00
-- url     : https://prove2.me/submissions/8ee98297-1af9-47e8-a173-dd100caf2952

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
theorem support_rectangle_w1093_s6_0 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2190500487/10000000000 : ℝ)*x 0 + (1348592169/2500000000 : ℝ)*x 1 + (658059997/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2190500487/10000000000 : ℝ)^4143 ≤ (13305674897239/100000000000000 : ℝ)^3119 := by
    have hnat : (2190500487 : ℕ)^4143*100000000000000^3119 ≤ 13305674897239^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190500487 10000000000 13305674897239 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348592169/2500000000 : ℝ)^4143 ≤ (11012196813083/25000000000000 : ℝ)^3119 := by
    have hnat : (1348592169 : ℕ)^4143*25000000000000^3119 ≤ 11012196813083^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348592169 2500000000 11012196813083 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658059997/1250000000 : ℝ)^4143 ≤ (8529107567181/20000000000000 : ℝ)^3119 := by
    have hnat : (658059997 : ℕ)^4143*20000000000000^3119 ≤ 8529107567181^3119*1250000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658059997 1250000000 8529107567181 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2190500487/10000000000 : ℝ), (1348592169/2500000000 : ℝ), (658059997/1250000000 : ℝ)] ![(13305674897239/100000000000000 : ℝ), (11012196813083/25000000000000 : ℝ), (8529107567181/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2190500487/10000000000 : ℝ)|^4143 ≤ (13305674897239/100000000000000 : ℝ)^3119
        have hw : |(-2190500487/10000000000 : ℝ)|=(2190500487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348592169/2500000000 : ℝ)|^4143 ≤ (11012196813083/25000000000000 : ℝ)^3119
        have hw : |(1348592169/2500000000 : ℝ)|=(1348592169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658059997/1250000000 : ℝ)|^4143 ≤ (8529107567181/20000000000000 : ℝ)^3119
        have hw : |(658059997/1250000000 : ℝ)|=(658059997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s6_1 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534503183/1000000000 : ℝ)*x 0 + (-2256401513/10000000000 : ℝ)*x 1 + (329029997/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534503183/1000000000 : ℝ)^4143 ≤ (43514456208513/100000000000000 : ℝ)^3119 := by
    have hnat : (534503183 : ℕ)^4143*100000000000000^3119 ≤ 43514456208513^3119*1000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534503183 1000000000 43514456208513 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2256401513/10000000000 : ℝ)^4143 ≤ (1730000774769/12500000000000 : ℝ)^3119 := by
    have hnat : (2256401513 : ℕ)^4143*12500000000000^3119 ≤ 1730000774769^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256401513 10000000000 1730000774769 12500000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329029997/625000000 : ℝ)^4143 ≤ (21322768788831/50000000000000 : ℝ)^3119 := by
    have hnat : (329029997 : ℕ)^4143*50000000000000^3119 ≤ 21322768788831^3119*625000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329029997 625000000 21322768788831 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534503183/1000000000 : ℝ), (-2256401513/10000000000 : ℝ), (329029997/625000000 : ℝ)] ![(43514456208513/100000000000000 : ℝ), (1730000774769/12500000000000 : ℝ), (21322768788831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534503183/1000000000 : ℝ)|^4143 ≤ (43514456208513/100000000000000 : ℝ)^3119
        have hw : |(534503183/1000000000 : ℝ)|=(534503183/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2256401513/10000000000 : ℝ)|^4143 ≤ (1730000774769/12500000000000 : ℝ)^3119
        have hw : |(-2256401513/10000000000 : ℝ)|=(2256401513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329029997/625000000 : ℝ)|^4143 ≤ (21322768788831/50000000000000 : ℝ)^3119
        have hw : |(329029997/625000000 : ℝ)|=(329029997/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s6_2 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672515887/5000000000 : ℝ)*x 0 + (526448001/1000000000 : ℝ)*x 1 + (-2256401511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672515887/5000000000 : ℝ)^4143 ≤ (43514455602933/100000000000000 : ℝ)^3119 := by
    have hnat : (2672515887 : ℕ)^4143*100000000000000^3119 ≤ 43514455602933^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672515887 5000000000 43514455602933 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526448001/1000000000 : ℝ)^4143 ≤ (170582152807/400000000000 : ℝ)^3119 := by
    have hnat : (526448001 : ℕ)^4143*400000000000^3119 ≤ 170582152807^3119*1000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526448001 1000000000 170582152807 400000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2256401511/10000000000 : ℝ)^4143 ≤ (13840006181857/100000000000000 : ℝ)^3119 := by
    have hnat : (2256401511 : ℕ)^4143*100000000000000^3119 ≤ 13840006181857^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256401511 10000000000 13840006181857 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672515887/5000000000 : ℝ), (526448001/1000000000 : ℝ), (-2256401511/10000000000 : ℝ)] ![(43514455602933/100000000000000 : ℝ), (170582152807/400000000000 : ℝ), (13840006181857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672515887/5000000000 : ℝ)|^4143 ≤ (43514455602933/100000000000000 : ℝ)^3119
        have hw : |(2672515887/5000000000 : ℝ)|=(2672515887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526448001/1000000000 : ℝ)|^4143 ≤ (170582152807/400000000000 : ℝ)^3119
        have hw : |(526448001/1000000000 : ℝ)|=(526448001/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2256401511/10000000000 : ℝ)|^4143 ≤ (13840006181857/100000000000000 : ℝ)^3119
        have hw : |(-2256401511/10000000000 : ℝ)|=(2256401511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s6_3 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4371599397/10000000000 : ℝ)*x 0 + (4245519993/10000000000 : ℝ)*x 1 + (2250724531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371599397/10000000000 : ℝ)^4143 ≤ (333164611871/1000000000000 : ℝ)^3119 := by
    have hnat : (4371599397 : ℕ)^4143*1000000000000^3119 ≤ 333164611871^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371599397 10000000000 333164611871 1000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4245519993/10000000000 : ℝ)^4143 ≤ (32046215482931/100000000000000 : ℝ)^3119 := by
    have hnat : (4245519993 : ℕ)^4143*100000000000000^3119 ≤ 32046215482931^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245519993 10000000000 32046215482931 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250724531/5000000000 : ℝ)^4143 ≤ (17318661658023/50000000000000 : ℝ)^3119 := by
    have hnat : (2250724531 : ℕ)^4143*50000000000000^3119 ≤ 17318661658023^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250724531 5000000000 17318661658023 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371599397/10000000000 : ℝ), (4245519993/10000000000 : ℝ), (2250724531/5000000000 : ℝ)] ![(333164611871/1000000000000 : ℝ), (32046215482931/100000000000000 : ℝ), (17318661658023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371599397/10000000000 : ℝ)|^4143 ≤ (333164611871/1000000000000 : ℝ)^3119
        have hw : |(4371599397/10000000000 : ℝ)|=(4371599397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4245519993/10000000000 : ℝ)|^4143 ≤ (32046215482931/100000000000000 : ℝ)^3119
        have hw : |(4245519993/10000000000 : ℝ)|=(4245519993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2250724531/5000000000 : ℝ)|^4143 ≤ (17318661658023/50000000000000 : ℝ)^3119
        have hw : |(2250724531/5000000000 : ℝ)|=(2250724531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s6_4 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-438101127/2000000000 : ℝ)*x 0 + (658100997/1250000000 : ℝ)*x 1 + (2697019727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438101127/2000000000 : ℝ)^4143 ≤ (6652858216961/50000000000000 : ℝ)^3119 := by
    have hnat : (438101127 : ℕ)^4143*50000000000000^3119 ≤ 6652858216961^3119*2000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438101127 2000000000 6652858216961 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658100997/1250000000 : ℝ)^4143 ≤ (1705962687837/4000000000000 : ℝ)^3119 := by
    have hnat : (658100997 : ℕ)^4143*4000000000000^3119 ≤ 1705962687837^3119*1250000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658100997 1250000000 1705962687837 4000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697019727/5000000000 : ℝ)^4143 ≤ (22022608177403/50000000000000 : ℝ)^3119 := by
    have hnat : (2697019727 : ℕ)^4143*50000000000000^3119 ≤ 22022608177403^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697019727 5000000000 22022608177403 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-438101127/2000000000 : ℝ), (658100997/1250000000 : ℝ), (2697019727/5000000000 : ℝ)] ![(6652858216961/50000000000000 : ℝ), (1705962687837/4000000000000 : ℝ), (22022608177403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-438101127/2000000000 : ℝ)|^4143 ≤ (6652858216961/50000000000000 : ℝ)^3119
        have hw : |(-438101127/2000000000 : ℝ)|=(438101127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658100997/1250000000 : ℝ)|^4143 ≤ (1705962687837/4000000000000 : ℝ)^3119
        have hw : |(658100997/1250000000 : ℝ)|=(658100997/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697019727/5000000000 : ℝ)|^4143 ≤ (22022608177403/50000000000000 : ℝ)^3119
        have hw : |(2697019727/5000000000 : ℝ)|=(2697019727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s6_5 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265612299/500000000 : ℝ)*x 0 + (-2126842117/10000000000 : ℝ)*x 1 + (5394039439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265612299/500000000 : ℝ)^4143 ≤ (21580135201453/50000000000000 : ℝ)^3119 := by
    have hnat : (265612299 : ℕ)^4143*50000000000000^3119 ≤ 21580135201453^3119*500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265612299 500000000 21580135201453 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126842117/10000000000 : ℝ)^4143 ≤ (1599314173911/12500000000000 : ℝ)^3119 := by
    have hnat : (2126842117 : ℕ)^4143*12500000000000^3119 ≤ 1599314173911^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126842117 10000000000 1599314173911 12500000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394039439/10000000000 : ℝ)^4143 ≤ (4404521619211/10000000000000 : ℝ)^3119 := by
    have hnat : (5394039439 : ℕ)^4143*10000000000000^3119 ≤ 4404521619211^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394039439 10000000000 4404521619211 10000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265612299/500000000 : ℝ), (-2126842117/10000000000 : ℝ), (5394039439/10000000000 : ℝ)] ![(21580135201453/50000000000000 : ℝ), (1599314173911/12500000000000 : ℝ), (4404521619211/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265612299/500000000 : ℝ)|^4143 ≤ (21580135201453/50000000000000 : ℝ)^3119
        have hw : |(265612299/500000000 : ℝ)|=(265612299/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2126842117/10000000000 : ℝ)|^4143 ≤ (1599314173911/12500000000000 : ℝ)^3119
        have hw : |(-2126842117/10000000000 : ℝ)|=(2126842117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394039439/10000000000 : ℝ)|^4143 ≤ (4404521619211/10000000000000 : ℝ)^3119
        have hw : |(5394039439/10000000000 : ℝ)|=(5394039439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s6_6 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312245969/10000000000 : ℝ)*x 0 + (674254929/1250000000 : ℝ)*x 1 + (-2126842141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312245969/10000000000 : ℝ)^4143 ≤ (43160270284193/100000000000000 : ℝ)^3119 := by
    have hnat : (5312245969 : ℕ)^4143*100000000000000^3119 ≤ 43160270284193^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312245969 10000000000 43160270284193 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674254929/1250000000 : ℝ)^4143 ≤ (22022608058093/50000000000000 : ℝ)^3119 := by
    have hnat : (674254929 : ℕ)^4143*50000000000000^3119 ≤ 22022608058093^3119*1250000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674254929 1250000000 22022608058093 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2126842141/10000000000 : ℝ)^4143 ≤ (6397256791533/50000000000000 : ℝ)^3119 := by
    have hnat : (2126842141 : ℕ)^4143*50000000000000^3119 ≤ 6397256791533^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126842141 10000000000 6397256791533 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312245969/10000000000 : ℝ), (674254929/1250000000 : ℝ), (-2126842141/10000000000 : ℝ)] ![(43160270284193/100000000000000 : ℝ), (22022608058093/50000000000000 : ℝ), (6397256791533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312245969/10000000000 : ℝ)|^4143 ≤ (43160270284193/100000000000000 : ℝ)^3119
        have hw : |(5312245969/10000000000 : ℝ)|=(5312245969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674254929/1250000000 : ℝ)|^4143 ≤ (22022608058093/50000000000000 : ℝ)^3119
        have hw : |(674254929/1250000000 : ℝ)|=(674254929/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2126842141/10000000000 : ℝ)|^4143 ≤ (6397256791533/50000000000000 : ℝ)^3119
        have hw : |(-2126842141/10000000000 : ℝ)|=(2126842141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s6_7 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2185804697/5000000000 : ℝ)*x 0 + (35162521/78125000 : ℝ)*x 1 + (265385549/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185804697/5000000000 : ℝ)^4143 ≤ (33316562388827/100000000000000 : ℝ)^3119 := by
    have hnat : (2185804697 : ℕ)^4143*100000000000000^3119 ≤ 33316562388827^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185804697 5000000000 33316562388827 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35162521/78125000 : ℝ)^4143 ≤ (3463071691121/10000000000000 : ℝ)^3119 := by
    have hnat : (35162521 : ℕ)^4143*10000000000000^3119 ≤ 3463071691121^3119*78125000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35162521 78125000 3463071691121 10000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265385549/625000000 : ℝ)^4143 ≤ (8013180172509/25000000000000 : ℝ)^3119 := by
    have hnat : (265385549 : ℕ)^4143*25000000000000^3119 ≤ 8013180172509^3119*625000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265385549 625000000 8013180172509 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185804697/5000000000 : ℝ), (35162521/78125000 : ℝ), (265385549/625000000 : ℝ)] ![(33316562388827/100000000000000 : ℝ), (3463071691121/10000000000000 : ℝ), (8013180172509/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185804697/5000000000 : ℝ)|^4143 ≤ (33316562388827/100000000000000 : ℝ)^3119
        have hw : |(2185804697/5000000000 : ℝ)|=(2185804697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35162521/78125000 : ℝ)|^4143 ≤ (3463071691121/10000000000000 : ℝ)^3119
        have hw : |(35162521/78125000 : ℝ)|=(35162521/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(265385549/625000000 : ℝ)|^4143 ≤ (8013180172509/25000000000000 : ℝ)^3119
        have hw : |(265385549/625000000 : ℝ)|=(265385549/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1093_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11279/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1403/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11241/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14069/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11241/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11241/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14069/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11241/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11241/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14069/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11241/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11241/100000 : ℝ) ^ (8285/2048 : ℝ) ≤ (14458282149110281/100000000000000000000 : ℝ) := by
    have hpowers : (11241/100000 : ℝ)^8285 ≤ (14458282149110281/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11241 : ℕ)^8285*100000000000000000000^2048 ≤ 14458282149110281^2048*100000^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11241 100000 14458282149110281 100000000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11241/100000 : ℝ)) (X := (14458282149110281/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14069/100000 : ℝ) ^ (8285/2048 : ℝ) ≤ (17920306075455373/50000000000000000000 : ℝ) := by
    have hpowers : (14069/100000 : ℝ)^8285 ≤ (17920306075455373/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14069 : ℕ)^8285*50000000000000000000^2048 ≤ 17920306075455373^2048*100000^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14069 100000 17920306075455373 50000000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14069/100000 : ℝ)) (X := (17920306075455373/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014458282149110281/50000000000000000000 : ℝ) ≤ (5000357360766297/5000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (50014458282149110281/50000000000000000000 : ℝ)^2048 ≤ (5000357360766297/5000000000000000 : ℝ)^8285 := by
      have hnat : (50014458282149110281 : ℕ)^2048*5000000000000000^8285 ≤ 5000357360766297^8285*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014458282149110281 50000000000000000000 5000357360766297 5000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000357360766297/5000000000000000 : ℝ)) (X := (50014458282149110281/50000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050298894300021027/100000000000000000000 : ℝ) ≤ (5000621560883023/5000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (100050298894300021027/100000000000000000000 : ℝ)^2048 ≤ (5000621560883023/5000000000000000 : ℝ)^8285 := by
      have hnat : (100050298894300021027 : ℕ)^2048*5000000000000000^8285 ≤ 5000621560883023^8285*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050298894300021027 100000000000000000000 5000621560883023 5000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000621560883023/5000000000000000 : ℝ)) (X := (100050298894300021027/100000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017920306075455373/25000000000000000000 : ℝ) ≤ (5000885760999749/5000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (25017920306075455373/25000000000000000000 : ℝ)^2048 ≤ (5000885760999749/5000000000000000 : ℝ)^8285 := by
      have hnat : (25017920306075455373 : ℕ)^2048*5000000000000000^8285 ≤ 5000885760999749^8285*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017920306075455373 25000000000000000000 5000885760999749 5000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000885760999749/5000000000000000 : ℝ)) (X := (25017920306075455373/25000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14458282149110281/100000000000000000000 : ℝ) ≤ ((63102994951887741/63125000000000000 : ℝ)+2*(18871436909/10100000000000 : ℝ)*(11241/100000 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (63102994951887741/63125000000000000 : ℝ)+2*(18871436909/10100000000000 : ℝ)*(11241/100000 : ℝ)=(5000357360766297/5000000000000000 : ℝ) by norm_num, show 1+2*(14458282149110281/100000000000000000000 : ℝ)=(50014458282149110281/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17920306075455373/50000000000000000000 : ℝ)+(14458282149110281/100000000000000000000 : ℝ) ≤ ((63102994951887741/63125000000000000 : ℝ)+(18871436909/10100000000000 : ℝ)*((14069/100000 : ℝ)+(11241/100000 : ℝ)))^(8285/2048 : ℝ) := by
    rw [show (63102994951887741/63125000000000000 : ℝ)+(18871436909/10100000000000 : ℝ)*((14069/100000 : ℝ)+(11241/100000 : ℝ))=(5000621560883023/5000000000000000 : ℝ) by norm_num, show 1+(17920306075455373/50000000000000000000 : ℝ)+(14458282149110281/100000000000000000000 : ℝ)=(100050298894300021027/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17920306075455373/50000000000000000000 : ℝ) ≤ ((63102994951887741/63125000000000000 : ℝ)+2*(18871436909/10100000000000 : ℝ)*(14069/100000 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (63102994951887741/63125000000000000 : ℝ)+2*(18871436909/10100000000000 : ℝ)*(14069/100000 : ℝ)=(5000885760999749/5000000000000000 : ℝ) by norm_num, show 1+2*(17920306075455373/50000000000000000000 : ℝ)=(25017920306075455373/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (63102994951887741/63125000000000000 : ℝ)*(X 1 0+X 2 0)+(18871436909/10100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (11241/100000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (63102994951887741/63125000000000000 : ℝ)) (alpha := (18871436909/10100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (63102994951887741/63125000000000000 : ℝ)*(X 0 1+X 2 1)+(18871436909/10100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (11241/100000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (63102994951887741/63125000000000000 : ℝ)) (alpha := (18871436909/10100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (63102994951887741/63125000000000000 : ℝ)*(X 0 2+X 1 2)+(18871436909/10100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (11241/100000 : ℝ)) (hi := (14069/100000 : ℝ)) (c := (63102994951887741/63125000000000000 : ℝ)) (alpha := (18871436909/10100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2190500487/10000000000 : ℝ)*X 0 0+(1348592169/2500000000 : ℝ)*X 0 1+(658059997/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534503183/1000000000 : ℝ)*X 1 0+(-2256401513/10000000000 : ℝ)*X 1 1+(329029997/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672515887/5000000000 : ℝ)*X 2 0+(526448001/1000000000 : ℝ)*X 2 1+(-2256401511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371599397/10000000000 : ℝ)*X 0 0+(4245519993/10000000000 : ℝ)*X 0 1+(2250724531/5000000000 : ℝ)*X 0 2+(4371599397/10000000000 : ℝ)*X 1 0+(4245519993/10000000000 : ℝ)*X 1 1+(2250724531/5000000000 : ℝ)*X 1 2+(4371599397/10000000000 : ℝ)*X 2 0+(4245519993/10000000000 : ℝ)*X 2 1+(2250724531/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-438101127/2000000000 : ℝ)*X 0 0+(658100997/1250000000 : ℝ)*X 0 1+(2697019727/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265612299/500000000 : ℝ)*X 1 0+(-2126842117/10000000000 : ℝ)*X 1 1+(5394039439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312245969/10000000000 : ℝ)*X 2 0+(674254929/1250000000 : ℝ)*X 2 1+(-2126842141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2185804697/5000000000 : ℝ)*X 0 0+(35162521/78125000 : ℝ)*X 0 1+(265385549/625000000 : ℝ)*X 0 2+(2185804697/5000000000 : ℝ)*X 1 0+(35162521/78125000 : ℝ)*X 1 1+(265385549/625000000 : ℝ)*X 1 2+(2185804697/5000000000 : ℝ)*X 2 0+(35162521/78125000 : ℝ)*X 2 1+(265385549/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1183419197920081443836277/631250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (232514563/25000000000000 : ℝ)*(base19) + (776649723/100000000000000 : ℝ)*(base23) + (1944161/5000000000000 : ℝ)*(lower2) + (48356189/50000000000000 : ℝ)*(upper3) + (30732149/100000000000000 : ℝ)*(upper5) + (1160631343668999/20000000000000 : ℝ)*(major0) + (1160631343668999/20000000000000 : ℝ)*(major1) + (1160631343668999/20000000000000 : ℝ)*(major2) + (7698927035602043/100000000000000 : ℝ)*(sp0) + (3849475604578029/50000000000000 : ℝ)*(sp1) + (7698951362564587/100000000000000 : ℝ)*(sp2) + (9768365618209/250000000000 : ℝ)*(sp3) + (6275903067/25000000000000 : ℝ)*(sp4) + (14987701287/100000000000000 : ℝ)*(sp7) + (3907361234984887/100000000000000 : ℝ)*(f.failure) + (769895213921431/10000000000000 : ℝ)*(f.sum) + (23570992883/50500000000000000000000000 : ℝ)*base66 + (13002530590739991/1262500000000000000000000000000 : ℝ)*base68 + (19138775435189991/1262500000000000000000000000000 : ℝ)*base70 + (20661204704814991/1262500000000000000000000000000 : ℝ)*base72 + (104015524611/101000000000000000000000000 : ℝ)*base74 + (31119157137610009/1262500000000000000000000000000 : ℝ)*base75 + (13332216967289991/1262500000000000000000000000000 : ℝ)*base78 + (14700820976335009/1262500000000000000000000000000 : ℝ)*base79 + (8305307913/5050000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (4486247/5000000000000000000000 : ℝ)*base89 + (4486247/5000000000000000000000 : ℝ)*base91 + (4486247/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11248070102051907814797711/1578125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1658385571/100000000000000 : ℝ)*(base19) + (1669514729/100000000000000 : ℝ)*(base23) + (157581/100000000000 : ℝ)*(upper3) + (4960239/25000000000000 : ℝ)*(lower4) + (9280541/5000000000000 : ℝ)*(upper5) + (1458157434678091/25000000000000 : ℝ)*(major0) + (1458157434678091/25000000000000 : ℝ)*(major1) + (1458157434678091/25000000000000 : ℝ)*(major2) + (22949217511/50000000000000 : ℝ)*(sp1) + (5530781707/12500000000000 : ℝ)*(sp2) + (7738053333611379/100000000000000 : ℝ)*(sp4) + (3869002888395393/50000000000000 : ℝ)*(sp5) + (483625463615187/6250000000000 : ℝ)*(sp6) + (61362592284849/1562500000000 : ℝ)*(sp7) + (61362592284849/1562500000000 : ℝ)*(f.failure) + (7738053333611379/100000000000000 : ℝ)*(f.sum) + (2842317604781/505000000000000000000000000 : ℝ)*base65 + (6475857973698819/1578125000000000000000000000000 : ℝ)*base68 + (9771734820855069/1578125000000000000000000000000 : ℝ)*base70 + (9885881869238681/1578125000000000000000000000000 : ℝ)*base71 + (698602669569/126250000000000000000000000 : ℝ)*base73 + (71950082229167569/1578125000000000000000000000000 : ℝ)*base76 + (18243198749676181/1578125000000000000000000000000 : ℝ)*base77 + (8986210133073819/1578125000000000000000000000000 : ℝ)*base80 + (331800645451/126250000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base88 + (441431/78125000000000000000 : ℝ)*base90 + (441431/78125000000000000000 : ℝ)*base92 + (441431/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1093_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1093_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1093_s7_0 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-219053359/1000000000 : ℝ)*x 0 + (215758433/400000000 : ℝ)*x 1 + (164527071/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219053359/1000000000 : ℝ)^4143 ≤ (13305941989647/100000000000000 : ℝ)^3119 := by
    have hnat : (219053359 : ℕ)^4143*100000000000000^3119 ≤ 13305941989647^3119*1000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219053359 1000000000 13305941989647 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215758433/400000000 : ℝ)^4143 ≤ (44044363518067/100000000000000 : ℝ)^3119 := by
    have hnat : (215758433 : ℕ)^4143*100000000000000^3119 ≤ 44044363518067^3119*400000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215758433 400000000 44044363518067 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164527071/312500000 : ℝ)^4143 ≤ (42649694482663/100000000000000 : ℝ)^3119 := by
    have hnat : (164527071 : ℕ)^4143*100000000000000^3119 ≤ 42649694482663^3119*312500000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164527071 312500000 42649694482663 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219053359/1000000000 : ℝ), (215758433/400000000 : ℝ), (164527071/312500000 : ℝ)] ![(13305941989647/100000000000000 : ℝ), (44044363518067/100000000000000 : ℝ), (42649694482663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219053359/1000000000 : ℝ)|^4143 ≤ (13305941989647/100000000000000 : ℝ)^3119
        have hw : |(-219053359/1000000000 : ℝ)|=(219053359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215758433/400000000 : ℝ)|^4143 ≤ (44044363518067/100000000000000 : ℝ)^3119
        have hw : |(215758433/400000000 : ℝ)|=(215758433/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164527071/312500000 : ℝ)|^4143 ≤ (42649694482663/100000000000000 : ℝ)^3119
        have hw : |(164527071/312500000 : ℝ)|=(164527071/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s7_1 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336232647/2500000000 : ℝ)*x 0 + (-1128012989/5000000000 : ℝ)*x 1 + (1316216509/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336232647/2500000000 : ℝ)^4143 ≤ (21756680694929/50000000000000 : ℝ)^3119 := by
    have hnat : (1336232647 : ℕ)^4143*50000000000000^3119 ≤ 21756680694929^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336232647 2500000000 21756680694929 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128012989/5000000000 : ℝ)^4143 ≤ (864809165307/6250000000000 : ℝ)^3119 := by
    have hnat : (1128012989 : ℕ)^4143*6250000000000^3119 ≤ 864809165307^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128012989 5000000000 864809165307 6250000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316216509/2500000000 : ℝ)^4143 ≤ (4264969194321/10000000000000 : ℝ)^3119 := by
    have hnat : (1316216509 : ℕ)^4143*10000000000000^3119 ≤ 4264969194321^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316216509 2500000000 4264969194321 10000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336232647/2500000000 : ℝ), (-1128012989/5000000000 : ℝ), (1316216509/2500000000 : ℝ)] ![(21756680694929/50000000000000 : ℝ), (864809165307/6250000000000 : ℝ), (4264969194321/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336232647/2500000000 : ℝ)|^4143 ≤ (21756680694929/50000000000000 : ℝ)^3119
        have hw : |(1336232647/2500000000 : ℝ)|=(1336232647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1128012989/5000000000 : ℝ)|^4143 ≤ (864809165307/6250000000000 : ℝ)^3119
        have hw : |(-1128012989/5000000000 : ℝ)|=(1128012989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316216509/2500000000 : ℝ)|^4143 ≤ (4264969194321/10000000000000 : ℝ)^3119
        have hw : |(1316216509/2500000000 : ℝ)|=(1316216509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s7_2 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672465159/5000000000 : ℝ)*x 0 + (65810829/125000000 : ℝ)*x 1 + (-1128012981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672465159/5000000000 : ℝ)^4143 ≤ (1087833961753/2500000000000 : ℝ)^3119 := by
    have hnat : (2672465159 : ℕ)^4143*2500000000000^3119 ≤ 1087833961753^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672465159 5000000000 1087833961753 2500000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65810829/125000000 : ℝ)^4143 ≤ (21324847499581/50000000000000 : ℝ)^3119 := by
    have hnat : (65810829 : ℕ)^4143*50000000000000^3119 ≤ 21324847499581^3119*125000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65810829 125000000 21324847499581 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1128012981/5000000000 : ℝ)^4143 ≤ (13836946514561/100000000000000 : ℝ)^3119 := by
    have hnat : (1128012981 : ℕ)^4143*100000000000000^3119 ≤ 13836946514561^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128012981 5000000000 13836946514561 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672465159/5000000000 : ℝ), (65810829/125000000 : ℝ), (-1128012981/5000000000 : ℝ)] ![(1087833961753/2500000000000 : ℝ), (21324847499581/50000000000000 : ℝ), (13836946514561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672465159/5000000000 : ℝ)|^4143 ≤ (1087833961753/2500000000000 : ℝ)^3119
        have hw : |(2672465159/5000000000 : ℝ)|=(2672465159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65810829/125000000 : ℝ)|^4143 ≤ (21324847499581/50000000000000 : ℝ)^3119
        have hw : |(65810829/125000000 : ℝ)|=(65810829/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1128012981/5000000000 : ℝ)|^4143 ≤ (13836946514561/100000000000000 : ℝ)^3119
        have hw : |(-1128012981/5000000000 : ℝ)|=(1128012981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s7_3 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2185809777/5000000000 : ℝ)*x 0 + (4246299703/10000000000 : ℝ)*x 1 + (562583023/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185809777/5000000000 : ℝ)^4143 ≤ (16658332620357/50000000000000 : ℝ)^3119 := by
    have hnat : (2185809777 : ℕ)^4143*50000000000000^3119 ≤ 16658332620357^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185809777 5000000000 16658332620357 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4246299703/10000000000 : ℝ)^4143 ≤ (16027016704987/50000000000000 : ℝ)^3119 := by
    have hnat : (4246299703 : ℕ)^4143*50000000000000^3119 ≤ 16027016704987^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246299703 10000000000 16027016704987 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562583023/1250000000 : ℝ)^4143 ≤ (4328662667717/12500000000000 : ℝ)^3119 := by
    have hnat : (562583023 : ℕ)^4143*12500000000000^3119 ≤ 4328662667717^3119*1250000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562583023 1250000000 4328662667717 12500000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185809777/5000000000 : ℝ), (4246299703/10000000000 : ℝ), (562583023/1250000000 : ℝ)] ![(16658332620357/50000000000000 : ℝ), (16027016704987/50000000000000 : ℝ), (4328662667717/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185809777/5000000000 : ℝ)|^4143 ≤ (16658332620357/50000000000000 : ℝ)^3119
        have hw : |(2185809777/5000000000 : ℝ)|=(2185809777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4246299703/10000000000 : ℝ)|^4143 ≤ (16027016704987/50000000000000 : ℝ)^3119
        have hw : |(4246299703/10000000000 : ℝ)|=(4246299703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562583023/1250000000 : ℝ)|^4143 ≤ (4328662667717/12500000000000 : ℝ)^3119
        have hw : |(562583023/1250000000 : ℝ)|=(562583023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s7_4 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-219053853/1000000000 : ℝ)*x 0 + (5265190267/10000000000 : ℝ)*x 1 + (1078727143/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219053853/1000000000 : ℝ)^4143 ≤ (6652990924139/50000000000000 : ℝ)^3119 := by
    have hnat : (219053853 : ℕ)^4143*50000000000000^3119 ≤ 6652990924139^3119*1000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219053853 1000000000 6652990924139 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265190267/10000000000 : ℝ)^4143 ≤ (42653180831453/100000000000000 : ℝ)^3119 := by
    have hnat : (5265190267 : ℕ)^4143*100000000000000^3119 ≤ 42653180831453^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265190267 10000000000 42653180831453 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078727143/2000000000 : ℝ)^4143 ≤ (11010209327083/25000000000000 : ℝ)^3119 := by
    have hnat : (1078727143 : ℕ)^4143*25000000000000^3119 ≤ 11010209327083^3119*2000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078727143 2000000000 11010209327083 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219053853/1000000000 : ℝ), (5265190267/10000000000 : ℝ), (1078727143/2000000000 : ℝ)] ![(6652990924139/50000000000000 : ℝ), (42653180831453/100000000000000 : ℝ), (11010209327083/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219053853/1000000000 : ℝ)|^4143 ≤ (6652990924139/50000000000000 : ℝ)^3119
        have hw : |(-219053853/1000000000 : ℝ)|=(219053853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265190267/10000000000 : ℝ)|^4143 ≤ (42653180831453/100000000000000 : ℝ)^3119
        have hw : |(5265190267/10000000000 : ℝ)|=(5265190267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078727143/2000000000 : ℝ)|^4143 ≤ (11010209327083/25000000000000 : ℝ)^3119
        have hw : |(1078727143/2000000000 : ℝ)|=(1078727143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s7_5 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664043109/1250000000 : ℝ)*x 0 + (-265907067/1250000000 : ℝ)*x 1 + (1078727143/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664043109/1250000000 : ℝ)^4143 ≤ (10790334414371/25000000000000 : ℝ)^3119 := by
    have hnat : (664043109 : ℕ)^4143*25000000000000^3119 ≤ 10790334414371^3119*1250000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664043109 1250000000 10790334414371 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265907067/1250000000 : ℝ)^4143 ≤ (12797825019919/100000000000000 : ℝ)^3119 := by
    have hnat : (265907067 : ℕ)^4143*100000000000000^3119 ≤ 12797825019919^3119*1250000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265907067 1250000000 12797825019919 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078727143/2000000000 : ℝ)^4143 ≤ (11010209327083/25000000000000 : ℝ)^3119 := by
    have hnat : (1078727143 : ℕ)^4143*25000000000000^3119 ≤ 11010209327083^3119*2000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078727143 2000000000 11010209327083 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664043109/1250000000 : ℝ), (-265907067/1250000000 : ℝ), (1078727143/2000000000 : ℝ)] ![(10790334414371/25000000000000 : ℝ), (12797825019919/100000000000000 : ℝ), (11010209327083/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664043109/1250000000 : ℝ)|^4143 ≤ (10790334414371/25000000000000 : ℝ)^3119
        have hw : |(664043109/1250000000 : ℝ)|=(664043109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-265907067/1250000000 : ℝ)|^4143 ≤ (12797825019919/100000000000000 : ℝ)^3119
        have hw : |(-265907067/1250000000 : ℝ)|=(265907067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078727143/2000000000 : ℝ)|^4143 ≤ (11010209327083/25000000000000 : ℝ)^3119
        have hw : |(1078727143/2000000000 : ℝ)|=(1078727143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s7_6 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664043109/1250000000 : ℝ)*x 0 + (1078727143/2000000000 : ℝ)*x 1 + (-265907067/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664043109/1250000000 : ℝ)^4143 ≤ (10790334414371/25000000000000 : ℝ)^3119 := by
    have hnat : (664043109 : ℕ)^4143*25000000000000^3119 ≤ 10790334414371^3119*1250000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664043109 1250000000 10790334414371 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078727143/2000000000 : ℝ)^4143 ≤ (11010209327083/25000000000000 : ℝ)^3119 := by
    have hnat : (1078727143 : ℕ)^4143*25000000000000^3119 ≤ 11010209327083^3119*2000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078727143 2000000000 11010209327083 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265907067/1250000000 : ℝ)^4143 ≤ (12797825019919/100000000000000 : ℝ)^3119 := by
    have hnat : (265907067 : ℕ)^4143*100000000000000^3119 ≤ 12797825019919^3119*1250000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265907067 1250000000 12797825019919 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664043109/1250000000 : ℝ), (1078727143/2000000000 : ℝ), (-265907067/1250000000 : ℝ)] ![(10790334414371/25000000000000 : ℝ), (11010209327083/25000000000000 : ℝ), (12797825019919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664043109/1250000000 : ℝ)|^4143 ≤ (10790334414371/25000000000000 : ℝ)^3119
        have hw : |(664043109/1250000000 : ℝ)|=(664043109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078727143/2000000000 : ℝ)|^4143 ≤ (11010209327083/25000000000000 : ℝ)^3119
        have hw : |(1078727143/2000000000 : ℝ)|=(1078727143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-265907067/1250000000 : ℝ)|^4143 ≤ (12797825019919/100000000000000 : ℝ)^3119
        have hw : |(-265907067/1250000000 : ℝ)|=(265907067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s7_7 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (874325897/2000000000 : ℝ)*x 0 + (4500025679/10000000000 : ℝ)*x 1 + (4246940463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874325897/2000000000 : ℝ)^4143 ≤ (33316765774461/100000000000000 : ℝ)^3119 := by
    have hnat : (874325897 : ℕ)^4143*100000000000000^3119 ≤ 33316765774461^3119*2000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874325897 2000000000 33316765774461 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500025679/10000000000 : ℝ)^4143 ≤ (4327846966933/12500000000000 : ℝ)^3119 := by
    have hnat : (4500025679 : ℕ)^4143*12500000000000^3119 ≤ 4327846966933^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500025679 10000000000 4327846966933 12500000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4246940463/10000000000 : ℝ)^4143 ≤ (32060458478301/100000000000000 : ℝ)^3119 := by
    have hnat : (4246940463 : ℕ)^4143*100000000000000^3119 ≤ 32060458478301^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246940463 10000000000 32060458478301 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874325897/2000000000 : ℝ), (4500025679/10000000000 : ℝ), (4246940463/10000000000 : ℝ)] ![(33316765774461/100000000000000 : ℝ), (4327846966933/12500000000000 : ℝ), (32060458478301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874325897/2000000000 : ℝ)|^4143 ≤ (33316765774461/100000000000000 : ℝ)^3119
        have hw : |(874325897/2000000000 : ℝ)|=(874325897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500025679/10000000000 : ℝ)|^4143 ≤ (4327846966933/12500000000000 : ℝ)^3119
        have hw : |(4500025679/10000000000 : ℝ)|=(4500025679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4246940463/10000000000 : ℝ)|^4143 ≤ (32060458478301/100000000000000 : ℝ)^3119
        have hw : |(4246940463/10000000000 : ℝ)|=(4246940463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1093_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11287/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14021/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1403/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1403/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11279/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1403/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1403/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11279/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1403/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1403/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11279/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11279/100000 : ℝ) ^ (8285/2048 : ℝ) ≤ (1465702559820019/10000000000000000000 : ℝ) := by
    have hpowers : (11279/100000 : ℝ)^8285 ≤ (1465702559820019/10000000000000000000 : ℝ)^2048 := by
      have hnat : (11279 : ℕ)^8285*10000000000000000000^2048 ≤ 1465702559820019^2048*100000^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11279 100000 1465702559820019 10000000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11279/100000 : ℝ)) (X := (1465702559820019/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1403/10000 : ℝ) ^ (8285/2048 : ℝ) ≤ (7088077139788647/20000000000000000000 : ℝ) := by
    have hpowers : (1403/10000 : ℝ)^8285 ≤ (7088077139788647/20000000000000000000 : ℝ)^2048 := by
      have hnat : (1403 : ℕ)^8285*20000000000000000000^2048 ≤ 7088077139788647^2048*10000^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1403 10000 7088077139788647 20000000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1403/10000 : ℝ)) (X := (7088077139788647/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001465702559820019/5000000000000000000 : ℝ) ≤ (2500181136251547/2500000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (5001465702559820019/5000000000000000000 : ℝ)^2048 ≤ (2500181136251547/2500000000000000 : ℝ)^8285 := by
      have hnat : (5001465702559820019 : ℕ)^2048*2500000000000000^8285 ≤ 2500181136251547^8285*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001465702559820019 5000000000000000000 2500181136251547 2500000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500181136251547/2500000000000000 : ℝ)) (X := (5001465702559820019/5000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4002003896451885737/4000000000000000000 : ℝ) ≤ (2500309535778491/2500000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (4002003896451885737/4000000000000000000 : ℝ)^2048 ≤ (2500309535778491/2500000000000000 : ℝ)^8285 := by
      have hnat : (4002003896451885737 : ℕ)^2048*2500000000000000^8285 ≤ 2500309535778491^8285*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4002003896451885737 4000000000000000000 2500309535778491 2500000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500309535778491/2500000000000000 : ℝ)) (X := (4002003896451885737/4000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007088077139788647/10000000000000000000 : ℝ) ≤ (500087587061087/500000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (10007088077139788647/10000000000000000000 : ℝ)^2048 ≤ (500087587061087/500000000000000 : ℝ)^8285 := by
      have hnat : (10007088077139788647 : ℕ)^2048*500000000000000^8285 ≤ 500087587061087^8285*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007088077139788647 10000000000000000000 500087587061087 500000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500087587061087/500000000000000 : ℝ)) (X := (10007088077139788647/10000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1465702559820019/10000000000000000000 : ℝ) ≤ ((1375020373859840609/1375500000000000000 : ℝ)+2*(4012485217/2149218750000 : ℝ)*(11279/100000 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (1375020373859840609/1375500000000000000 : ℝ)+2*(4012485217/2149218750000 : ℝ)*(11279/100000 : ℝ)=(2500181136251547/2500000000000000 : ℝ) by norm_num, show 1+2*(1465702559820019/10000000000000000000 : ℝ)=(5001465702559820019/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7088077139788647/20000000000000000000 : ℝ)+(1465702559820019/10000000000000000000 : ℝ) ≤ ((1375020373859840609/1375500000000000000 : ℝ)+(4012485217/2149218750000 : ℝ)*((1403/10000 : ℝ)+(11279/100000 : ℝ)))^(8285/2048 : ℝ) := by
    rw [show (1375020373859840609/1375500000000000000 : ℝ)+(4012485217/2149218750000 : ℝ)*((1403/10000 : ℝ)+(11279/100000 : ℝ))=(2500309535778491/2500000000000000 : ℝ) by norm_num, show 1+(7088077139788647/20000000000000000000 : ℝ)+(1465702559820019/10000000000000000000 : ℝ)=(4002003896451885737/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7088077139788647/20000000000000000000 : ℝ) ≤ ((1375020373859840609/1375500000000000000 : ℝ)+2*(4012485217/2149218750000 : ℝ)*(1403/10000 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (1375020373859840609/1375500000000000000 : ℝ)+2*(4012485217/2149218750000 : ℝ)*(1403/10000 : ℝ)=(500087587061087/500000000000000 : ℝ) by norm_num, show 1+2*(7088077139788647/20000000000000000000 : ℝ)=(10007088077139788647/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1375020373859840609/1375500000000000000 : ℝ)*(X 1 0+X 2 0)+(4012485217/2149218750000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (1403/10000 : ℝ)) (c := (1375020373859840609/1375500000000000000 : ℝ)) (alpha := (4012485217/2149218750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1375020373859840609/1375500000000000000 : ℝ)*(X 0 1+X 2 1)+(4012485217/2149218750000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (1403/10000 : ℝ)) (c := (1375020373859840609/1375500000000000000 : ℝ)) (alpha := (4012485217/2149218750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1375020373859840609/1375500000000000000 : ℝ)*(X 0 2+X 1 2)+(4012485217/2149218750000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (11279/100000 : ℝ)) (hi := (1403/10000 : ℝ)) (c := (1375020373859840609/1375500000000000000 : ℝ)) (alpha := (4012485217/2149218750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-219053359/1000000000 : ℝ)*X 0 0+(215758433/400000000 : ℝ)*X 0 1+(164527071/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336232647/2500000000 : ℝ)*X 1 0+(-1128012989/5000000000 : ℝ)*X 1 1+(1316216509/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672465159/5000000000 : ℝ)*X 2 0+(65810829/125000000 : ℝ)*X 2 1+(-1128012981/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2185809777/5000000000 : ℝ)*X 0 0+(4246299703/10000000000 : ℝ)*X 0 1+(562583023/1250000000 : ℝ)*X 0 2+(2185809777/5000000000 : ℝ)*X 1 0+(4246299703/10000000000 : ℝ)*X 1 1+(562583023/1250000000 : ℝ)*X 1 2+(2185809777/5000000000 : ℝ)*X 2 0+(4246299703/10000000000 : ℝ)*X 2 1+(562583023/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-219053853/1000000000 : ℝ)*X 0 0+(5265190267/10000000000 : ℝ)*X 0 1+(1078727143/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664043109/1250000000 : ℝ)*X 1 0+(-265907067/1250000000 : ℝ)*X 1 1+(1078727143/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664043109/1250000000 : ℝ)*X 2 0+(1078727143/2000000000 : ℝ)*X 2 1+(-265907067/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((874325897/2000000000 : ℝ)*X 0 0+(4500025679/10000000000 : ℝ)*X 0 1+(4246940463/10000000000 : ℝ)*X 0 2+(874325897/2000000000 : ℝ)*X 1 0+(4500025679/10000000000 : ℝ)*X 1 1+(4246940463/10000000000 : ℝ)*X 1 2+(874325897/2000000000 : ℝ)*X 2 0+(4500025679/10000000000 : ℝ)*X 2 1+(4246940463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (538325879612473610901/131000000000000000000000000 : ℝ) := by norm_num
    linear_combination (731134943/50000000000000 : ℝ)*(base19) + (983363961/100000000000000 : ℝ)*(base23) + (158005439/100000000000000 : ℝ)*(upper3) + (23410601/50000000000000 : ℝ)*(upper4) + (46510589/100000000000000 : ℝ)*(upper5) + (583886284824563/10000000000000 : ℝ)*(major0) + (583886284824563/10000000000000 : ℝ)*(major1) + (583886284824563/10000000000000 : ℝ)*(major2) + (968286936776521/12500000000000 : ℝ)*(sp0) + (774632133544817/10000000000000 : ℝ)*(sp1) + (3873160907177047/50000000000000 : ℝ)*(sp2) + (982846068526839/25000000000000 : ℝ)*(sp3) + (27303505887/100000000000000 : ℝ)*(sp4) + (18487687247/100000000000000 : ℝ)*(sp7) + (3931402761794603/100000000000000 : ℝ)*(f.failure) + (1549264559543611/20000000000000 : ℝ)*(f.sum) + (1742483330891/393000000000000000000000000 : ℝ)*base65 + (2421743377477673/655000000000000000000000000000 : ℝ)*base68 + (1737277125657673/655000000000000000000000000000 : ℝ)*base70 + (2534320954827327/655000000000000000000000000000 : ℝ)*base71 + (213406615723/78600000000000000000000000 : ℝ)*base73 + (3685990420897327/655000000000000000000000000000 : ℝ)*base75 + (5382269690632673/655000000000000000000000000000 : ℝ)*base78 + (9096566781117327/655000000000000000000000000000 : ℝ)*base79 + (58063068227/393000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (11539557/5000000000000000000000 : ℝ)*base90 + (11539557/5000000000000000000000 : ℝ)*base92 + (11539557/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10199986306896629999784711/2865625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (328862089/50000000000000 : ℝ)*(base19) + (71647669/10000000000000 : ℝ)*(base23) + (71283481/100000000000000 : ℝ)*(upper3) + (26754911/100000000000000 : ℝ)*(lower4) + (72817989/100000000000000 : ℝ)*(upper5) + (1467080480562479/25000000000000 : ℝ)*(major0) + (1467080480562479/25000000000000 : ℝ)*(major1) + (1467080480562479/25000000000000 : ℝ)*(major2) + (17992452591/100000000000000 : ℝ)*(sp1) + (3872044239/20000000000000 : ℝ)*(sp2) + (7785405683128701/100000000000000 : ℝ)*(sp4) + (1946346758237983/25000000000000 : ℝ)*(sp5) + (243293300200963/3125000000000 : ℝ)*(sp6) + (12347618883511/312500000000 : ℝ)*(sp7) + (12347618883511/312500000000 : ℝ)*(f.failure) + (7785405683128701/100000000000000 : ℝ)*(f.sum) + (26461785602017/6877500000000000000000000000 : ℝ)*base66 + (173416177205594263/11462500000000000000000000000000 : ℝ)*base68 + (31223574774705737/11462500000000000000000000000000 : ℝ)*base69 + (54499733721906763/11462500000000000000000000000000 : ℝ)*base72 + (39538635629167/6877500000000000000000000000 : ℝ)*base74 + (64538671505256763/11462500000000000000000000000000 : ℝ)*base76 + (10754470521281763/11462500000000000000000000000000 : ℝ)*base78 + (30665556969856763/11462500000000000000000000000000 : ℝ)*base80 + (10049829389827/6877500000000000000000000000 : ℝ)*base82 + (240591/15625000000000000000 : ℝ)*base89 + (240591/15625000000000000000 : ℝ)*base91 + (240591/15625000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1093_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11279/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11287/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1093_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1093_s8_0 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1095271653/5000000000 : ℝ)*x 0 + (5393870837/10000000000 : ℝ)*x 1 + (5264949693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095271653/5000000000 : ℝ)^4143 ≤ (2661204076739/20000000000000 : ℝ)^3119 := by
    have hnat : (1095271653 : ℕ)^4143*20000000000000^3119 ≤ 2661204076739^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095271653 5000000000 2661204076739 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393870837/10000000000 : ℝ)^4143 ≤ (2202169374139/5000000000000 : ℝ)^3119 := by
    have hnat : (5393870837 : ℕ)^4143*5000000000000^3119 ≤ 2202169374139^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393870837 10000000000 2202169374139 5000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264949693/10000000000 : ℝ)^4143 ≤ (42650592127753/100000000000000 : ℝ)^3119 := by
    have hnat : (5264949693 : ℕ)^4143*100000000000000^3119 ≤ 42650592127753^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264949693 10000000000 42650592127753 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1095271653/5000000000 : ℝ), (5393870837/10000000000 : ℝ), (5264949693/10000000000 : ℝ)] ![(2661204076739/20000000000000 : ℝ), (2202169374139/5000000000000 : ℝ), (42650592127753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1095271653/5000000000 : ℝ)|^4143 ≤ (2661204076739/20000000000000 : ℝ)^3119
        have hw : |(-1095271653/5000000000 : ℝ)|=(1095271653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393870837/10000000000 : ℝ)|^4143 ≤ (2202169374139/5000000000000 : ℝ)^3119
        have hw : |(5393870837/10000000000 : ℝ)|=(5393870837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264949693/10000000000 : ℝ)|^4143 ≤ (42650592127753/100000000000000 : ℝ)^3119
        have hw : |(5264949693/10000000000 : ℝ)|=(5264949693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s8_1 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344907223/10000000000 : ℝ)*x 0 + (-2255946559/10000000000 : ℝ)*x 1 + (5264949647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344907223/10000000000 : ℝ)^4143 ≤ (43513108724561/100000000000000 : ℝ)^3119 := by
    have hnat : (5344907223 : ℕ)^4143*100000000000000^3119 ≤ 43513108724561^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344907223 10000000000 43513108724561 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255946559/10000000000 : ℝ)^4143 ≤ (691814981251/5000000000000 : ℝ)^3119 := by
    have hnat : (2255946559 : ℕ)^4143*5000000000000^3119 ≤ 691814981251^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255946559 10000000000 691814981251 5000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264949647/10000000000 : ℝ)^4143 ≤ (10662647908193/25000000000000 : ℝ)^3119 := by
    have hnat : (5264949647 : ℕ)^4143*25000000000000^3119 ≤ 10662647908193^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264949647 10000000000 10662647908193 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344907223/10000000000 : ℝ), (-2255946559/10000000000 : ℝ), (5264949647/10000000000 : ℝ)] ![(43513108724561/100000000000000 : ℝ), (691814981251/5000000000000 : ℝ), (10662647908193/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344907223/10000000000 : ℝ)|^4143 ≤ (43513108724561/100000000000000 : ℝ)^3119
        have hw : |(5344907223/10000000000 : ℝ)|=(5344907223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2255946559/10000000000 : ℝ)|^4143 ≤ (691814981251/5000000000000 : ℝ)^3119
        have hw : |(-2255946559/10000000000 : ℝ)|=(2255946559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264949647/10000000000 : ℝ)|^4143 ≤ (10662647908193/25000000000000 : ℝ)^3119
        have hw : |(5264949647/10000000000 : ℝ)|=(5264949647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s8_2 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672453603/5000000000 : ℝ)*x 0 + (526494969/1000000000 : ℝ)*x 1 + (-90237861/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672453603/5000000000 : ℝ)^4143 ≤ (21756554270363/50000000000000 : ℝ)^3119 := by
    have hnat : (2672453603 : ℕ)^4143*50000000000000^3119 ≤ 21756554270363^3119*5000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672453603 5000000000 21756554270363 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526494969/1000000000 : ℝ)^4143 ≤ (2665662005967/6250000000000 : ℝ)^3119 := by
    have hnat : (526494969 : ℕ)^4143*6250000000000^3119 ≤ 2665662005967^3119*1000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526494969 1000000000 2665662005967 6250000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90237861/400000000 : ℝ)^4143 ≤ (6918149674013/50000000000000 : ℝ)^3119 := by
    have hnat : (90237861 : ℕ)^4143*50000000000000^3119 ≤ 6918149674013^3119*400000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90237861 400000000 6918149674013 50000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672453603/5000000000 : ℝ), (526494969/1000000000 : ℝ), (-90237861/400000000 : ℝ)] ![(21756554270363/50000000000000 : ℝ), (2665662005967/6250000000000 : ℝ), (6918149674013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672453603/5000000000 : ℝ)|^4143 ≤ (21756554270363/50000000000000 : ℝ)^3119
        have hw : |(2672453603/5000000000 : ℝ)|=(2672453603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526494969/1000000000 : ℝ)|^4143 ≤ (2665662005967/6250000000000 : ℝ)^3119
        have hw : |(526494969/1000000000 : ℝ)|=(526494969/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90237861/400000000 : ℝ)|^4143 ≤ (6918149674013/50000000000000 : ℝ)^3119
        have hw : |(-90237861/400000000 : ℝ)|=(90237861/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s8_3 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4371624043/10000000000 : ℝ)*x 0 + (1061617503/2500000000 : ℝ)*x 1 + (4500492647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371624043/10000000000 : ℝ)^4143 ≤ (33316710683861/100000000000000 : ℝ)^3119 := by
    have hnat : (4371624043 : ℕ)^4143*100000000000000^3119 ≤ 33316710683861^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371624043 10000000000 33316710683861 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061617503/2500000000 : ℝ)^4143 ≤ (32055741111863/100000000000000 : ℝ)^3119 := by
    have hnat : (1061617503 : ℕ)^4143*100000000000000^3119 ≤ 32055741111863^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061617503 2500000000 32055741111863 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500492647/10000000000 : ℝ)^4143 ≤ (34627548180853/100000000000000 : ℝ)^3119 := by
    have hnat : (4500492647 : ℕ)^4143*100000000000000^3119 ≤ 34627548180853^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500492647 10000000000 34627548180853 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371624043/10000000000 : ℝ), (1061617503/2500000000 : ℝ), (4500492647/10000000000 : ℝ)] ![(33316710683861/100000000000000 : ℝ), (32055741111863/100000000000000 : ℝ), (34627548180853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371624043/10000000000 : ℝ)|^4143 ≤ (33316710683861/100000000000000 : ℝ)^3119
        have hw : |(4371624043/10000000000 : ℝ)|=(4371624043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061617503/2500000000 : ℝ)|^4143 ≤ (32055741111863/100000000000000 : ℝ)^3119
        have hw : |(1061617503/2500000000 : ℝ)|=(1061617503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500492647/10000000000 : ℝ)|^4143 ≤ (34627548180853/100000000000000 : ℝ)^3119
        have hw : |(4500492647/10000000000 : ℝ)|=(4500492647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s8_4 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-547636913/2500000000 : ℝ)*x 0 + (526527267/1000000000 : ℝ)*x 1 + (215741887/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547636913/2500000000 : ℝ)^4143 ≤ (13306055449657/100000000000000 : ℝ)^3119 := by
    have hnat : (547636913 : ℕ)^4143*100000000000000^3119 ≤ 13306055449657^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547636913 2500000000 13306055449657 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526527267/1000000000 : ℝ)^4143 ≤ (266587922127/625000000000 : ℝ)^3119 := by
    have hnat : (526527267 : ℕ)^4143*625000000000^3119 ≤ 266587922127^3119*1000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526527267 1000000000 266587922127 625000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215741887/400000000 : ℝ)^4143 ≤ (2752492312339/6250000000000 : ℝ)^3119 := by
    have hnat : (215741887 : ℕ)^4143*6250000000000^3119 ≤ 2752492312339^3119*400000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215741887 400000000 2752492312339 6250000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-547636913/2500000000 : ℝ), (526527267/1000000000 : ℝ), (215741887/400000000 : ℝ)] ![(13306055449657/100000000000000 : ℝ), (266587922127/625000000000 : ℝ), (2752492312339/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-547636913/2500000000 : ℝ)|^4143 ≤ (13306055449657/100000000000000 : ℝ)^3119
        have hw : |(-547636913/2500000000 : ℝ)|=(547636913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526527267/1000000000 : ℝ)|^4143 ≤ (266587922127/625000000000 : ℝ)^3119
        have hw : |(526527267/1000000000 : ℝ)|=(526527267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215741887/400000000 : ℝ)|^4143 ≤ (2752492312339/6250000000000 : ℝ)^3119
        have hw : |(215741887/400000000 : ℝ)|=(215741887/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s8_5 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312364863/10000000000 : ℝ)*x 0 + (-531837419/2500000000 : ℝ)*x 1 + (5393547199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312364863/10000000000 : ℝ)^4143 ≤ (43161553403597/100000000000000 : ℝ)^3119 := by
    have hnat : (5312364863 : ℕ)^4143*100000000000000^3119 ≤ 43161553403597^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312364863 10000000000 43161553403597 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (531837419/2500000000 : ℝ)^4143 ≤ (3199642333063/25000000000000 : ℝ)^3119 := by
    have hnat : (531837419 : ℕ)^4143*25000000000000^3119 ≤ 3199642333063^3119*2500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531837419 2500000000 3199642333063 25000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393547199/10000000000 : ℝ)^4143 ≤ (44039877257729/100000000000000 : ℝ)^3119 := by
    have hnat : (5393547199 : ℕ)^4143*100000000000000^3119 ≤ 44039877257729^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393547199 10000000000 44039877257729 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312364863/10000000000 : ℝ), (-531837419/2500000000 : ℝ), (5393547199/10000000000 : ℝ)] ![(43161553403597/100000000000000 : ℝ), (3199642333063/25000000000000 : ℝ), (44039877257729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312364863/10000000000 : ℝ)|^4143 ≤ (43161553403597/100000000000000 : ℝ)^3119
        have hw : |(5312364863/10000000000 : ℝ)|=(5312364863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-531837419/2500000000 : ℝ)|^4143 ≤ (3199642333063/25000000000000 : ℝ)^3119
        have hw : |(-531837419/2500000000 : ℝ)|=(531837419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393547199/10000000000 : ℝ)|^4143 ≤ (44039877257729/100000000000000 : ℝ)^3119
        have hw : |(5393547199/10000000000 : ℝ)|=(5393547199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s8_6 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062473171/2000000000 : ℝ)*x 0 + (269677301/500000000 : ℝ)*x 1 + (-425469987/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062473171/2000000000 : ℝ)^4143 ≤ (43161564109429/100000000000000 : ℝ)^3119 := by
    have hnat : (1062473171 : ℕ)^4143*100000000000000^3119 ≤ 43161564109429^3119*2000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062473171 2000000000 43161564109429 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269677301/500000000 : ℝ)^4143 ≤ (44039864470249/100000000000000 : ℝ)^3119 := by
    have hnat : (269677301 : ℕ)^4143*100000000000000^3119 ≤ 44039864470249^3119*500000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269677301 500000000 44039864470249 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425469987/2000000000 : ℝ)^4143 ≤ (12798571402021/100000000000000 : ℝ)^3119 := by
    have hnat : (425469987 : ℕ)^4143*100000000000000^3119 ≤ 12798571402021^3119*2000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425469987 2000000000 12798571402021 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062473171/2000000000 : ℝ), (269677301/500000000 : ℝ), (-425469987/2000000000 : ℝ)] ![(43161564109429/100000000000000 : ℝ), (44039864470249/100000000000000 : ℝ), (12798571402021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062473171/2000000000 : ℝ)|^4143 ≤ (43161564109429/100000000000000 : ℝ)^3119
        have hw : |(1062473171/2000000000 : ℝ)|=(1062473171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269677301/500000000 : ℝ)|^4143 ≤ (44039864470249/100000000000000 : ℝ)^3119
        have hw : |(269677301/500000000 : ℝ)|=(269677301/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-425469987/2000000000 : ℝ)|^4143 ≤ (12798571402021/100000000000000 : ℝ)^3119
        have hw : |(-425469987/2000000000 : ℝ)|=(425469987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1093_s8_7 (p : ℝ) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4371634241/10000000000 : ℝ)*x 0 + (112496387/250000000 : ℝ)*x 1 + (4247109123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4371634241/10000000000 : ℝ)^4143 ≤ (6663362784109/20000000000000 : ℝ)^3119 := by
    have hnat : (4371634241 : ℕ)^4143*20000000000000^3119 ≤ 6663362784109^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4371634241 10000000000 6663362784109 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112496387/250000000 : ℝ)^4143 ≤ (34621036330293/100000000000000 : ℝ)^3119 := by
    have hnat : (112496387 : ℕ)^4143*100000000000000^3119 ≤ 34621036330293^3119*250000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112496387 250000000 34621036330293 100000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4247109123/10000000000 : ℝ)^4143 ≤ (6412429945841/20000000000000 : ℝ)^3119 := by
    have hnat : (4247109123 : ℕ)^4143*20000000000000^3119 ≤ 6412429945841^3119*10000000000^4143 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247109123 10000000000 6412429945841 20000000000000 4143 3119 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4143/1024 : ℝ)) 4143 3119 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4371634241/10000000000 : ℝ), (112496387/250000000 : ℝ), (4247109123/10000000000 : ℝ)] ![(6663362784109/20000000000000 : ℝ), (34621036330293/100000000000000 : ℝ), (6412429945841/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4371634241/10000000000 : ℝ)|^4143 ≤ (6663362784109/20000000000000 : ℝ)^3119
        have hw : |(4371634241/10000000000 : ℝ)|=(4371634241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112496387/250000000 : ℝ)|^4143 ≤ (34621036330293/100000000000000 : ℝ)^3119
        have hw : |(112496387/250000000 : ℝ)|=(112496387/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4247109123/10000000000 : ℝ)|^4143 ≤ (6412429945841/20000000000000 : ℝ)^3119
        have hw : |(4247109123/10000000000 : ℝ)|=(4247109123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1093_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11287/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11289/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14019/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14021/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11287/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14021/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11287/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14021/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11287/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14021/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11287/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14021/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11287/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14021/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11287/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (11287/100000 : ℝ) ^ (8285/2048 : ℝ) ≤ (14699127025667103/100000000000000000000 : ℝ) := by
    have hpowers : (11287/100000 : ℝ)^8285 ≤ (14699127025667103/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11287 : ℕ)^8285*100000000000000000000^2048 ≤ 14699127025667103^2048*100000^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11287 100000 14699127025667103 100000000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11287/100000 : ℝ)) (X := (14699127025667103/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14021/100000 : ℝ) ^ (8285/2048 : ℝ) ≤ (35348505568528143/100000000000000000000 : ℝ) := by
    have hpowers : (14021/100000 : ℝ)^8285 ≤ (35348505568528143/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14021 : ℕ)^8285*100000000000000000000^2048 ≤ 35348505568528143^2048*100000^8285 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14021 100000 35348505568528143 100000000000000000000 8285 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14021/100000 : ℝ)) (X := (35348505568528143/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014699127025667103/50000000000000000000 : ℝ) ≤ (10000726625988043/10000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (50014699127025667103/50000000000000000000 : ℝ)^2048 ≤ (10000726625988043/10000000000000000 : ℝ)^8285 := by
      have hnat : (50014699127025667103 : ℕ)^2048*10000000000000000^8285 ≤ 10000726625988043^8285*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014699127025667103 50000000000000000000 10000726625988043 10000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000726625988043/10000000000000000 : ℝ)) (X := (50014699127025667103/50000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025023816297097623/50000000000000000000 : ℝ) ≤ (5000618456539651/5000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (50025023816297097623/50000000000000000000 : ℝ)^2048 ≤ (5000618456539651/5000000000000000 : ℝ)^8285 := by
      have hnat : (50025023816297097623 : ℕ)^2048*5000000000000000^8285 ≤ 5000618456539651^8285*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025023816297097623 50000000000000000000 5000618456539651 5000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000618456539651/5000000000000000 : ℝ)) (X := (50025023816297097623/50000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035348505568528143/50000000000000000000 : ℝ) ≤ (10001747200170561/10000000000000000 : ℝ) ^ (8285/2048 : ℝ) := by
    have hpowers : (50035348505568528143/50000000000000000000 : ℝ)^2048 ≤ (10001747200170561/10000000000000000 : ℝ)^8285 := by
      have hnat : (50035348505568528143 : ℕ)^2048*10000000000000000^8285 ≤ 10001747200170561^8285*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035348505568528143 50000000000000000000 10001747200170561 10000000000000000 2048 8285 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001747200170561/10000000000000000 : ℝ)) (X := (50035348505568528143/50000000000000000000 : ℝ)) (by norm_num) 8285 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14699127025667103/100000000000000000000 : ℝ) ≤ ((854077105457913403/854375000000000000 : ℝ)+2*(510287091259/273400000000000 : ℝ)*(11287/100000 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (854077105457913403/854375000000000000 : ℝ)+2*(510287091259/273400000000000 : ℝ)*(11287/100000 : ℝ)=(10000726625988043/10000000000000000 : ℝ) by norm_num, show 1+2*(14699127025667103/100000000000000000000 : ℝ)=(50014699127025667103/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35348505568528143/100000000000000000000 : ℝ)+(14699127025667103/100000000000000000000 : ℝ) ≤ ((854077105457913403/854375000000000000 : ℝ)+(510287091259/273400000000000 : ℝ)*((14021/100000 : ℝ)+(11287/100000 : ℝ)))^(8285/2048 : ℝ) := by
    rw [show (854077105457913403/854375000000000000 : ℝ)+(510287091259/273400000000000 : ℝ)*((14021/100000 : ℝ)+(11287/100000 : ℝ))=(5000618456539651/5000000000000000 : ℝ) by norm_num, show 1+(35348505568528143/100000000000000000000 : ℝ)+(14699127025667103/100000000000000000000 : ℝ)=(50025023816297097623/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35348505568528143/100000000000000000000 : ℝ) ≤ ((854077105457913403/854375000000000000 : ℝ)+2*(510287091259/273400000000000 : ℝ)*(14021/100000 : ℝ))^(8285/2048 : ℝ) := by
    rw [show (854077105457913403/854375000000000000 : ℝ)+2*(510287091259/273400000000000 : ℝ)*(14021/100000 : ℝ)=(10001747200170561/10000000000000000 : ℝ) by norm_num, show 1+2*(35348505568528143/100000000000000000000 : ℝ)=(50035348505568528143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (854077105457913403/854375000000000000 : ℝ)*(X 1 0+X 2 0)+(510287091259/273400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (11287/100000 : ℝ)) (hi := (14021/100000 : ℝ)) (c := (854077105457913403/854375000000000000 : ℝ)) (alpha := (510287091259/273400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (854077105457913403/854375000000000000 : ℝ)*(X 0 1+X 2 1)+(510287091259/273400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (11287/100000 : ℝ)) (hi := (14021/100000 : ℝ)) (c := (854077105457913403/854375000000000000 : ℝ)) (alpha := (510287091259/273400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (854077105457913403/854375000000000000 : ℝ)*(X 0 2+X 1 2)+(510287091259/273400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8285/2048 : ℝ)) (lo := (11287/100000 : ℝ)) (hi := (14021/100000 : ℝ)) (c := (854077105457913403/854375000000000000 : ℝ)) (alpha := (510287091259/273400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1095271653/5000000000 : ℝ)*X 0 0+(5393870837/10000000000 : ℝ)*X 0 1+(5264949693/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344907223/10000000000 : ℝ)*X 1 0+(-2255946559/10000000000 : ℝ)*X 1 1+(5264949647/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672453603/5000000000 : ℝ)*X 2 0+(526494969/1000000000 : ℝ)*X 2 1+(-90237861/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4371624043/10000000000 : ℝ)*X 0 0+(1061617503/2500000000 : ℝ)*X 0 1+(4500492647/10000000000 : ℝ)*X 0 2+(4371624043/10000000000 : ℝ)*X 1 0+(1061617503/2500000000 : ℝ)*X 1 1+(4500492647/10000000000 : ℝ)*X 1 2+(4371624043/10000000000 : ℝ)*X 2 0+(1061617503/2500000000 : ℝ)*X 2 1+(4500492647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-547636913/2500000000 : ℝ)*X 0 0+(526527267/1000000000 : ℝ)*X 0 1+(215741887/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312364863/10000000000 : ℝ)*X 1 0+(-531837419/2500000000 : ℝ)*X 1 1+(5393547199/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062473171/2000000000 : ℝ)*X 2 0+(269677301/500000000 : ℝ)*X 2 1+(-425469987/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4371634241/10000000000 : ℝ)*X 0 0+(112496387/250000000 : ℝ)*X 0 1+(4247109123/10000000000 : ℝ)*X 0 2+(4371634241/10000000000 : ℝ)*X 1 0+(112496387/250000000 : ℝ)*X 1 1+(4247109123/10000000000 : ℝ)*X 1 2+(4371634241/10000000000 : ℝ)*X 2 0+(112496387/250000000 : ℝ)*X 2 1+(4247109123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1093_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33413131948250502678520437/10679687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (155130921/25000000000000 : ℝ)*(base19) + (51209923/10000000000000 : ℝ)*(base23) + (44765461/100000000000000 : ℝ)*(lower2) + (66671071/100000000000000 : ℝ)*(upper3) + (53853791/100000000000000 : ℝ)*(upper5) + (2923345700828407/50000000000000 : ℝ)*(major0) + (2923345700828407/50000000000000 : ℝ)*(major1) + (2923345700828407/50000000000000 : ℝ)*(major2) + (1939173488482983/25000000000000 : ℝ)*(sp0) + (969588527804599/12500000000000 : ℝ)*(sp1) + (7756708330861247/100000000000000 : ℝ)*(sp2) + (1968332573627867/50000000000000 : ℝ)*(sp3) + (232641071/1562500000000 : ℝ)*(sp4) + (4354404339/50000000000000 : ℝ)*(sp7) + (984168464016103/25000000000000 : ℝ)*(f.failure) + (7756708842960477/100000000000000 : ℝ)*(f.sum) + (34474287502387/6835000000000000000000000000 : ℝ)*base66 + (113640508328552323/21359375000000000000000000000000 : ℝ)*base67 + (63498204344135177/21359375000000000000000000000000 : ℝ)*base70 + (54687762634989823/21359375000000000000000000000000 : ℝ)*base71 + (24688273365213/6835000000000000000000000000 : ℝ)*base73 + (107198394722802323/21359375000000000000000000000000 : ℝ)*base75 + (32160088219021073/21359375000000000000000000000000 : ℝ)*base77 + (439270505440708573/21359375000000000000000000000000 : ℝ)*base79 + (2951346261391/3417500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (6201943/1250000000000000000000 : ℝ)*base89 + (6201943/1250000000000000000000 : ℝ)*base91 + (6201943/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (113416655424437696122241271/42718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (107845733/50000000000000 : ℝ)*(base8) + (287002391/100000000000000 : ℝ)*(base15) + (132091097/100000000000000 : ℝ)*(upper1) + (129947129/25000000000000 : ℝ)*(lower2) + (4060811/12500000000000 : ℝ)*(upper3) + (5876211874765281/100000000000000 : ℝ)*(major0) + (5876211874765281/100000000000000 : ℝ)*(major1) + (5876211874765281/100000000000000 : ℝ)*(major2) + (30366171247/100000000000000 : ℝ)*(sp0) + (7315133607/20000000000000 : ℝ)*(sp1) + (7795842601145171/100000000000000 : ℝ)*(sp4) + (7795836320337459/100000000000000 : ℝ)*(sp5) + (1559174636601577/20000000000000 : ℝ)*(sp6) + (197827523901197/5000000000000 : ℝ)*(sp7) + (197827523901197/5000000000000 : ℝ)*(f.failure) + (1559174636601577/20000000000000 : ℝ)*(f.sum) + (35736770651441/13670000000000000000000000000 : ℝ)*base66 + (161559517203729059/42718750000000000000000000000000 : ℝ)*base67 + (135849997610947809/42718750000000000000000000000000 : ℝ)*base69 + (417683577225989691/42718750000000000000000000000000 : ℝ)*base72 + (40799016139391/13670000000000000000000000000 : ℝ)*base74 + (345315326872510309/42718750000000000000000000000000 : ℝ)*base75 + (67014178669291559/42718750000000000000000000000000 : ℝ)*base77 + (251119302280552191/42718750000000000000000000000000 : ℝ)*base80 + (18722476906629/13670000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1759357/250000000000000000000 : ℝ)*base89 + (1759357/250000000000000000000 : ℝ)*base91 + (1759357/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1093_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14021/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11287/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11289/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14019/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1093_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1093_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11289/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14019/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1093_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1093_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1093_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8285/2048 : ℝ) ≤ p) (hpb : p ≤ (4143/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74259281/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11289/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14019/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1093_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

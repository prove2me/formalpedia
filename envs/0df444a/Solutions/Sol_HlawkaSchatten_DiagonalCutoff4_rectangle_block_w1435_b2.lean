-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1435_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:55:50.490994+00:00
-- url     : https://prove2.me/submissions/3f159a84-3a5b-405d-8a52-a7a24b16fcf6

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
theorem support_rectangle_w1435_s6_0 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-196627047/1000000000 : ℝ)*x 0 + (1081582689/2000000000 : ℝ)*x 1 + (81984949/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196627047/1000000000 : ℝ)^4395 ≤ (11997067041477/100000000000000 : ℝ)^3371 := by
    have hnat : (196627047 : ℕ)^4395*100000000000000^3371 ≤ 11997067041477^3371*1000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196627047 1000000000 11997067041477 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081582689/2000000000 : ℝ)^4395 ≤ (44867602157733/100000000000000 : ℝ)^3371 := by
    have hnat : (1081582689 : ℕ)^4395*100000000000000^3371 ≤ 44867602157733^3371*2000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081582689 2000000000 44867602157733 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81984949/156250000 : ℝ)^4395 ≤ (43135330787417/100000000000000 : ℝ)^3371 := by
    have hnat : (81984949 : ℕ)^4395*100000000000000^3371 ≤ 43135330787417^3371*156250000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81984949 156250000 43135330787417 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-196627047/1000000000 : ℝ), (1081582689/2000000000 : ℝ), (81984949/156250000 : ℝ)] ![(11997067041477/100000000000000 : ℝ), (44867602157733/100000000000000 : ℝ), (43135330787417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-196627047/1000000000 : ℝ)|^4395 ≤ (11997067041477/100000000000000 : ℝ)^3371
        have hw : |(-196627047/1000000000 : ℝ)|=(196627047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081582689/2000000000 : ℝ)|^4395 ≤ (44867602157733/100000000000000 : ℝ)^3371
        have hw : |(1081582689/2000000000 : ℝ)|=(1081582689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81984949/156250000 : ℝ)|^4395 ≤ (43135330787417/100000000000000 : ℝ)^3371
        have hw : |(81984949/156250000 : ℝ)|=(81984949/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s6_1 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668400209/1250000000 : ℝ)*x 0 + (-1024085639/5000000000 : ℝ)*x 1 + (81984949/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668400209/1250000000 : ℝ)^4395 ≤ (44212011020277/100000000000000 : ℝ)^3371 := by
    have hnat : (668400209 : ℕ)^4395*100000000000000^3371 ≤ 44212011020277^3371*1250000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668400209 1250000000 44212011020277 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024085639/5000000000 : ℝ)^4395 ≤ (2530531633917/20000000000000 : ℝ)^3371 := by
    have hnat : (1024085639 : ℕ)^4395*20000000000000^3371 ≤ 2530531633917^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024085639 5000000000 2530531633917 20000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81984949/156250000 : ℝ)^4395 ≤ (43135330787417/100000000000000 : ℝ)^3371 := by
    have hnat : (81984949 : ℕ)^4395*100000000000000^3371 ≤ 43135330787417^3371*156250000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81984949 156250000 43135330787417 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668400209/1250000000 : ℝ), (-1024085639/5000000000 : ℝ), (81984949/156250000 : ℝ)] ![(44212011020277/100000000000000 : ℝ), (2530531633917/20000000000000 : ℝ), (43135330787417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668400209/1250000000 : ℝ)|^4395 ≤ (44212011020277/100000000000000 : ℝ)^3371
        have hw : |(668400209/1250000000 : ℝ)|=(668400209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1024085639/5000000000 : ℝ)|^4395 ≤ (2530531633917/20000000000000 : ℝ)^3371
        have hw : |(-1024085639/5000000000 : ℝ)|=(1024085639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81984949/156250000 : ℝ)|^4395 ≤ (43135330787417/100000000000000 : ℝ)^3371
        have hw : |(81984949/156250000 : ℝ)|=(81984949/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s6_2 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668400209/1250000000 : ℝ)*x 0 + (81984949/156250000 : ℝ)*x 1 + (-1024085639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668400209/1250000000 : ℝ)^4395 ≤ (44212011020277/100000000000000 : ℝ)^3371 := by
    have hnat : (668400209 : ℕ)^4395*100000000000000^3371 ≤ 44212011020277^3371*1250000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668400209 1250000000 44212011020277 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81984949/156250000 : ℝ)^4395 ≤ (43135330787417/100000000000000 : ℝ)^3371 := by
    have hnat : (81984949 : ℕ)^4395*100000000000000^3371 ≤ 43135330787417^3371*156250000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81984949 156250000 43135330787417 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1024085639/5000000000 : ℝ)^4395 ≤ (2530531633917/20000000000000 : ℝ)^3371 := by
    have hnat : (1024085639 : ℕ)^4395*20000000000000^3371 ≤ 2530531633917^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024085639 5000000000 2530531633917 20000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668400209/1250000000 : ℝ), (81984949/156250000 : ℝ), (-1024085639/5000000000 : ℝ)] ![(44212011020277/100000000000000 : ℝ), (43135330787417/100000000000000 : ℝ), (2530531633917/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668400209/1250000000 : ℝ)|^4395 ≤ (44212011020277/100000000000000 : ℝ)^3371
        have hw : |(668400209/1250000000 : ℝ)|=(668400209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81984949/156250000 : ℝ)|^4395 ≤ (43135330787417/100000000000000 : ℝ)^3371
        have hw : |(81984949/156250000 : ℝ)|=(81984949/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1024085639/5000000000 : ℝ)|^4395 ≤ (2530531633917/20000000000000 : ℝ)^3371
        have hw : |(-1024085639/5000000000 : ℝ)|=(1024085639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s6_3 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075718757/2500000000 : ℝ)*x 0 + (1032912021/2500000000 : ℝ)*x 1 + (56005543/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075718757/2500000000 : ℝ)^4395 ≤ (33304779667513/100000000000000 : ℝ)^3371 := by
    have hnat : (1075718757 : ℕ)^4395*100000000000000^3371 ≤ 33304779667513^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075718757 2500000000 33304779667513 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032912021/2500000000 : ℝ)^4395 ≤ (31587415435123/100000000000000 : ℝ)^3371 := by
    have hnat : (1032912021 : ℕ)^4395*100000000000000^3371 ≤ 31587415435123^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032912021 2500000000 31587415435123 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56005543/125000000 : ℝ)^4395 ≤ (35107804880133/100000000000000 : ℝ)^3371 := by
    have hnat : (56005543 : ℕ)^4395*100000000000000^3371 ≤ 35107804880133^3371*125000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56005543 125000000 35107804880133 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075718757/2500000000 : ℝ), (1032912021/2500000000 : ℝ), (56005543/125000000 : ℝ)] ![(33304779667513/100000000000000 : ℝ), (31587415435123/100000000000000 : ℝ), (35107804880133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075718757/2500000000 : ℝ)|^4395 ≤ (33304779667513/100000000000000 : ℝ)^3371
        have hw : |(1075718757/2500000000 : ℝ)|=(1075718757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1032912021/2500000000 : ℝ)|^4395 ≤ (31587415435123/100000000000000 : ℝ)^3371
        have hw : |(1032912021/2500000000 : ℝ)|=(1032912021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56005543/125000000 : ℝ)|^4395 ≤ (35107804880133/100000000000000 : ℝ)^3371
        have hw : |(56005543/125000000 : ℝ)|=(56005543/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s6_4 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1966281683/10000000000 : ℝ)*x 0 + (5247617391/10000000000 : ℝ)*x 1 + (2703664913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1966281683/10000000000 : ℝ)^4395 ≤ (149964452991/1250000000000 : ℝ)^3371 := by
    have hnat : (1966281683 : ℕ)^4395*1250000000000^3371 ≤ 149964452991^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966281683 10000000000 149964452991 1250000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247617391/10000000000 : ℝ)^4395 ≤ (43141554429723/100000000000000 : ℝ)^3371 := by
    have hnat : (5247617391 : ℕ)^4395*100000000000000^3371 ≤ 43141554429723^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247617391 10000000000 43141554429723 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703664913/5000000000 : ℝ)^4395 ≤ (44861289306449/100000000000000 : ℝ)^3371 := by
    have hnat : (2703664913 : ℕ)^4395*100000000000000^3371 ≤ 44861289306449^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703664913 5000000000 44861289306449 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1966281683/10000000000 : ℝ), (5247617391/10000000000 : ℝ), (2703664913/5000000000 : ℝ)] ![(149964452991/1250000000000 : ℝ), (43141554429723/100000000000000 : ℝ), (44861289306449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1966281683/10000000000 : ℝ)|^4395 ≤ (149964452991/1250000000000 : ℝ)^3371
        have hw : |(-1966281683/10000000000 : ℝ)|=(1966281683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247617391/10000000000 : ℝ)|^4395 ≤ (43141554429723/100000000000000 : ℝ)^3371
        have hw : |(5247617391/10000000000 : ℝ)|=(5247617391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703664913/5000000000 : ℝ)|^4395 ≤ (44861289306449/100000000000000 : ℝ)^3371
        have hw : |(2703664913/5000000000 : ℝ)|=(2703664913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s6_5 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652676749/5000000000 : ℝ)*x 0 + (-1843631/9765625 : ℝ)*x 1 + (2703664963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652676749/5000000000 : ℝ)^4395 ≤ (43761430031551/100000000000000 : ℝ)^3371 := by
    have hnat : (2652676749 : ℕ)^4395*100000000000000^3371 ≤ 43761430031551^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652676749 5000000000 43761430031551 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1843631/9765625 : ℝ)^4395 ≤ (11377279576437/100000000000000 : ℝ)^3371 := by
    have hnat : (1843631 : ℕ)^4395*100000000000000^3371 ≤ 11377279576437^3371*9765625^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1843631 9765625 11377279576437 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703664963/5000000000 : ℝ)^4395 ≤ (8972258077621/20000000000000 : ℝ)^3371 := by
    have hnat : (2703664963 : ℕ)^4395*20000000000000^3371 ≤ 8972258077621^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703664963 5000000000 8972258077621 20000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652676749/5000000000 : ℝ), (-1843631/9765625 : ℝ), (2703664963/5000000000 : ℝ)] ![(43761430031551/100000000000000 : ℝ), (11377279576437/100000000000000 : ℝ), (8972258077621/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652676749/5000000000 : ℝ)|^4395 ≤ (43761430031551/100000000000000 : ℝ)^3371
        have hw : |(2652676749/5000000000 : ℝ)|=(2652676749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1843631/9765625 : ℝ)|^4395 ≤ (11377279576437/100000000000000 : ℝ)^3371
        have hw : |(-1843631/9765625 : ℝ)|=(1843631/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703664963/5000000000 : ℝ)|^4395 ≤ (8972258077621/20000000000000 : ℝ)^3371
        have hw : |(2703664963/5000000000 : ℝ)|=(2703664963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s6_6 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305353859/10000000000 : ℝ)*x 0 + (1081465923/2000000000 : ℝ)*x 1 + (-1887878077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305353859/10000000000 : ℝ)^4395 ≤ (4376143391381/10000000000000 : ℝ)^3371 := by
    have hnat : (5305353859 : ℕ)^4395*10000000000000^3371 ≤ 4376143391381^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305353859 10000000000 4376143391381 10000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081465923/2000000000 : ℝ)^4395 ≤ (11215321756039/25000000000000 : ℝ)^3371 := by
    have hnat : (1081465923 : ℕ)^4395*25000000000000^3371 ≤ 11215321756039^3371*2000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081465923 2000000000 11215321756039 25000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1887878077/10000000000 : ℝ)^4395 ≤ (1422159881251/12500000000000 : ℝ)^3371 := by
    have hnat : (1887878077 : ℕ)^4395*12500000000000^3371 ≤ 1422159881251^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887878077 10000000000 1422159881251 12500000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305353859/10000000000 : ℝ), (1081465923/2000000000 : ℝ), (-1887878077/10000000000 : ℝ)] ![(4376143391381/10000000000000 : ℝ), (11215321756039/25000000000000 : ℝ), (1422159881251/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305353859/10000000000 : ℝ)|^4395 ≤ (4376143391381/10000000000000 : ℝ)^3371
        have hw : |(5305353859/10000000000 : ℝ)|=(5305353859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081465923/2000000000 : ℝ)|^4395 ≤ (11215321756039/25000000000000 : ℝ)^3371
        have hw : |(1081465923/2000000000 : ℝ)|=(1081465923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1887878077/10000000000 : ℝ)|^4395 ≤ (1422159881251/12500000000000 : ℝ)^3371
        have hw : |(-1887878077/10000000000 : ℝ)|=(1887878077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s6_7 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4302899243/10000000000 : ℝ)*x 0 + (895836991/2000000000 : ℝ)*x 1 + (4132913307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302899243/10000000000 : ℝ)^4395 ≤ (1332200961161/4000000000000 : ℝ)^3371 := by
    have hnat : (4302899243 : ℕ)^4395*4000000000000^3371 ≤ 1332200961161^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302899243 10000000000 1332200961161 4000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895836991/2000000000 : ℝ)^4395 ≤ (35094948689079/100000000000000 : ℝ)^3371 := by
    have hnat : (895836991 : ℕ)^4395*100000000000000^3371 ≤ 35094948689079^3371*2000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895836991 2000000000 35094948689079 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4132913307/10000000000 : ℝ)^4395 ≤ (31600027266973/100000000000000 : ℝ)^3371 := by
    have hnat : (4132913307 : ℕ)^4395*100000000000000^3371 ≤ 31600027266973^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132913307 10000000000 31600027266973 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302899243/10000000000 : ℝ), (895836991/2000000000 : ℝ), (4132913307/10000000000 : ℝ)] ![(1332200961161/4000000000000 : ℝ), (35094948689079/100000000000000 : ℝ), (31600027266973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302899243/10000000000 : ℝ)|^4395 ≤ (1332200961161/4000000000000 : ℝ)^3371
        have hw : |(4302899243/10000000000 : ℝ)|=(4302899243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895836991/2000000000 : ℝ)|^4395 ≤ (35094948689079/100000000000000 : ℝ)^3371
        have hw : |(895836991/2000000000 : ℝ)|=(895836991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4132913307/10000000000 : ℝ)|^4395 ≤ (31600027266973/100000000000000 : ℝ)^3371
        have hw : |(4132913307/10000000000 : ℝ)|=(4132913307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1435_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79202277/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1419/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (369/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11349/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11349/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11349/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11349/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11349/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11349/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11349/100000 : ℝ) ^ (2197/512 : ℝ) ≤ (8806600147509133/100000000000000000000 : ℝ) := by
    have hpowers : (11349/100000 : ℝ)^2197 ≤ (8806600147509133/100000000000000000000 : ℝ)^512 := by
      have hnat : (11349 : ℕ)^2197*100000000000000000000^512 ≤ 8806600147509133^512*100000^2197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11349 100000 8806600147509133 100000000000000000000 2197 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11349/100000 : ℝ)) (X := (8806600147509133/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3691/25000 : ℝ) ^ (2197/512 : ℝ) ≤ (13614808711641767/50000000000000000000 : ℝ) := by
    have hpowers : (3691/25000 : ℝ)^2197 ≤ (13614808711641767/50000000000000000000 : ℝ)^512 := by
      have hnat : (3691 : ℕ)^2197*50000000000000000000^512 ≤ 13614808711641767^512*25000^2197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3691 25000 13614808711641767 50000000000000000000 2197 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3691/25000 : ℝ)) (X := (13614808711641767/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008806600147509133/50000000000000000000 : ℝ) ≤ (5000205219606677/5000000000000000 : ℝ) ^ (2197/512 : ℝ) := by
    have hpowers : (50008806600147509133/50000000000000000000 : ℝ)^512 ≤ (5000205219606677/5000000000000000 : ℝ)^2197 := by
      have hnat : (50008806600147509133 : ℕ)^512*5000000000000000^2197 ≤ 5000205219606677^2197*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008806600147509133 50000000000000000000 5000205219606677 5000000000000000 512 2197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000205219606677/5000000000000000 : ℝ)) (X := (50008806600147509133/50000000000000000000 : ℝ)) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036036217570792667/100000000000000000000 : ℝ) ≤ (10000839690224961/10000000000000000 : ℝ) ^ (2197/512 : ℝ) := by
    have hpowers : (100036036217570792667/100000000000000000000 : ℝ)^512 ≤ (10000839690224961/10000000000000000 : ℝ)^2197 := by
      have hnat : (100036036217570792667 : ℕ)^512*10000000000000000^2197 ≤ 10000839690224961^2197*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036036217570792667 100000000000000000000 10000839690224961 10000000000000000 512 2197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000839690224961/10000000000000000 : ℝ)) (X := (100036036217570792667/100000000000000000000 : ℝ)) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013614808711641767/25000000000000000000 : ℝ) ≤ (1250158617654571/1250000000000000 : ℝ) ^ (2197/512 : ℝ) := by
    have hpowers : (25013614808711641767/25000000000000000000 : ℝ)^512 ≤ (1250158617654571/1250000000000000 : ℝ)^2197 := by
      have hnat : (25013614808711641767 : ℕ)^512*1250000000000000^2197 ≤ 1250158617654571^2197*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013614808711641767 25000000000000000000 1250158617654571 1250000000000000 512 2197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250158617654571/1250000000000000 : ℝ)) (X := (25013614808711641767/25000000000000000000 : ℝ)) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8806600147509133/100000000000000000000 : ℝ) ≤ ((16670731694556713/16674804687500000 : ℝ)+2*(429251011607/341500000000000 : ℝ)*(11349/100000 : ℝ))^(2197/512 : ℝ) := by
    rw [show (16670731694556713/16674804687500000 : ℝ)+2*(429251011607/341500000000000 : ℝ)*(11349/100000 : ℝ)=(5000205219606677/5000000000000000 : ℝ) by norm_num, show 1+2*(8806600147509133/100000000000000000000 : ℝ)=(50008806600147509133/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13614808711641767/50000000000000000000 : ℝ)+(8806600147509133/100000000000000000000 : ℝ) ≤ ((16670731694556713/16674804687500000 : ℝ)+(429251011607/341500000000000 : ℝ)*((3691/25000 : ℝ)+(11349/100000 : ℝ)))^(2197/512 : ℝ) := by
    rw [show (16670731694556713/16674804687500000 : ℝ)+(429251011607/341500000000000 : ℝ)*((3691/25000 : ℝ)+(11349/100000 : ℝ))=(10000839690224961/10000000000000000 : ℝ) by norm_num, show 1+(13614808711641767/50000000000000000000 : ℝ)+(8806600147509133/100000000000000000000 : ℝ)=(100036036217570792667/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13614808711641767/50000000000000000000 : ℝ) ≤ ((16670731694556713/16674804687500000 : ℝ)+2*(429251011607/341500000000000 : ℝ)*(3691/25000 : ℝ))^(2197/512 : ℝ) := by
    rw [show (16670731694556713/16674804687500000 : ℝ)+2*(429251011607/341500000000000 : ℝ)*(3691/25000 : ℝ)=(1250158617654571/1250000000000000 : ℝ) by norm_num, show 1+2*(13614808711641767/50000000000000000000 : ℝ)=(25013614808711641767/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16670731694556713/16674804687500000 : ℝ)*(X 1 0+X 2 0)+(429251011607/341500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2197/512 : ℝ)) (lo := (11349/100000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (16670731694556713/16674804687500000 : ℝ)) (alpha := (429251011607/341500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16670731694556713/16674804687500000 : ℝ)*(X 0 1+X 2 1)+(429251011607/341500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2197/512 : ℝ)) (lo := (11349/100000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (16670731694556713/16674804687500000 : ℝ)) (alpha := (429251011607/341500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16670731694556713/16674804687500000 : ℝ)*(X 0 2+X 1 2)+(429251011607/341500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2197/512 : ℝ)) (lo := (11349/100000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (16670731694556713/16674804687500000 : ℝ)) (alpha := (429251011607/341500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-196627047/1000000000 : ℝ)*X 0 0+(1081582689/2000000000 : ℝ)*X 0 1+(81984949/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668400209/1250000000 : ℝ)*X 1 0+(-1024085639/5000000000 : ℝ)*X 1 1+(81984949/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668400209/1250000000 : ℝ)*X 2 0+(81984949/156250000 : ℝ)*X 2 1+(-1024085639/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1075718757/2500000000 : ℝ)*X 0 0+(1032912021/2500000000 : ℝ)*X 0 1+(56005543/125000000 : ℝ)*X 0 2+(1075718757/2500000000 : ℝ)*X 1 0+(1032912021/2500000000 : ℝ)*X 1 1+(56005543/125000000 : ℝ)*X 1 2+(1075718757/2500000000 : ℝ)*X 2 0+(1032912021/2500000000 : ℝ)*X 2 1+(56005543/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1966281683/10000000000 : ℝ)*X 0 0+(5247617391/10000000000 : ℝ)*X 0 1+(2703664913/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652676749/5000000000 : ℝ)*X 1 0+(-1843631/9765625 : ℝ)*X 1 1+(2703664963/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305353859/10000000000 : ℝ)*X 2 0+(1081465923/2000000000 : ℝ)*X 2 1+(-1887878077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4302899243/10000000000 : ℝ)*X 0 0+(895836991/2000000000 : ℝ)*X 0 1+(4132913307/10000000000 : ℝ)*X 0 2+(4302899243/10000000000 : ℝ)*X 1 0+(895836991/2000000000 : ℝ)*X 1 1+(4132913307/10000000000 : ℝ)*X 1 2+(4302899243/10000000000 : ℝ)*X 2 0+(895836991/2000000000 : ℝ)*X 2 1+(4132913307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (147905702367962741264757/17075000000000000000000000000 : ℝ) := by norm_num
    linear_combination (787398663/50000000000000 : ℝ)*(base19) + (1468437279/100000000000000 : ℝ)*(base23) + (56872863/100000000000000 : ℝ)*(lower2) + (53935619/25000000000000 : ℝ)*(upper3) + (69224189/50000000000000 : ℝ)*(upper5) + (2270762612199771/50000000000000 : ℝ)*(major0) + (2270762612199771/50000000000000 : ℝ)*(major1) + (2270762612199771/50000000000000 : ℝ)*(major2) + (124319496819881/2000000000000 : ℝ)*(sp0) + (1554001625592763/25000000000000 : ℝ)*(sp1) + (6216006608731099/100000000000000 : ℝ)*(sp2) + (716756377573439/25000000000000 : ℝ)*(sp3) + (4154521791/12500000000000 : ℝ)*(sp4) + (16572599607/100000000000000 : ℝ)*(sp7) + (2867042082893363/100000000000000 : ℝ)*(f.failure) + (3108004038584189/50000000000000 : ℝ)*(f.sum) + (32472711133119/17075000000000000000000000000 : ℝ)*base65 + (2059391468089733/3334960937500000000000000000000 : ℝ)*base68 + (9907714029483489/26679687500000000000000000000000 : ℝ)*base70 + (162071653793858489/26679687500000000000000000000000 : ℝ)*base72 + (27727704356981/17075000000000000000000000000 : ℝ)*base74 + (99221851378641511/26679687500000000000000000000000 : ℝ)*base75 + (73979587109579011/26679687500000000000000000000000 : ℝ)*base77 + (231162729740516511/26679687500000000000000000000000 : ℝ)*base79 + (50547156690031/17075000000000000000000000000 : ℝ)*base82 + (2212449/5000000000000000000000 : ℝ)*base90 + (2212449/5000000000000000000000 : ℝ)*base92 + (2212449/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (278538680395858771250692911/53359375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (764066593/100000000000000 : ℝ)*(base19) + (634391599/50000000000000 : ℝ)*(base23) + (15084797/5000000000000 : ℝ)*(lower1) + (111826971/100000000000000 : ℝ)*(upper3) + (6642093/100000000000000 : ℝ)*(lower4) + (4574567585482841/100000000000000 : ℝ)*(major0) + (4574567585482841/100000000000000 : ℝ)*(major1) + (4574567585482841/100000000000000 : ℝ)*(major2) + (262091261/3125000000000 : ℝ)*(sp2) + (435962397/100000000000000 : ℝ)*(sp3) + (6261233437339077/100000000000000 : ℝ)*(sp4) + (6261232673272483/100000000000000 : ℝ)*(sp5) + (6261223781635527/100000000000000 : ℝ)*(sp6) + (1443950561831243/50000000000000 : ℝ)*(sp7) + (721975389906221/25000000000000 : ℝ)*(f.failure) + (6261233437339077/100000000000000 : ℝ)*(f.sum) + (43034824611381/8537500000000000000000000000 : ℝ)*base65 + (396519454234822637/106718750000000000000000000000000 : ℝ)*base67 + (17512360299083613/106718750000000000000000000000000 : ℝ)*base70 + (606373431285333613/106718750000000000000000000000000 : ℝ)*base72 + (14219922299037/17075000000000000000000000000 : ℝ)*base73 + (502102531087833613/106718750000000000000000000000000 : ℝ)*base76 + (2405116009902364863/106718750000000000000000000000000 : ℝ)*base78 + (620181136608260137/106718750000000000000000000000000 : ℝ)*base79 + (8938253788981/8537500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (7165217/1250000000000000000000 : ℝ)*base89 + (7165217/1250000000000000000000 : ℝ)*base91 + (7165217/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1435_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79202277/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (369/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1435_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1435_s7_0 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-98313791/500000000 : ℝ)*x 0 + (1351971811/2500000000 : ℝ)*x 1 + (5247059207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98313791/500000000 : ℝ)^4395 ≤ (11997109599939/100000000000000 : ℝ)^3371 := by
    have hnat : (98313791 : ℕ)^4395*100000000000000^3371 ≤ 11997109599939^3371*500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98313791 500000000 11997109599939 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351971811/2500000000 : ℝ)^4395 ≤ (44867318744057/100000000000000 : ℝ)^3371 := by
    have hnat : (1351971811 : ℕ)^4395*100000000000000^3371 ≤ 44867318744057^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351971811 2500000000 44867318744057 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247059207/10000000000 : ℝ)^4395 ≤ (43135571634747/100000000000000 : ℝ)^3371 := by
    have hnat : (5247059207 : ℕ)^4395*100000000000000^3371 ≤ 43135571634747^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247059207 10000000000 43135571634747 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98313791/500000000 : ℝ), (1351971811/2500000000 : ℝ), (5247059207/10000000000 : ℝ)] ![(11997109599939/100000000000000 : ℝ), (44867318744057/100000000000000 : ℝ), (43135571634747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98313791/500000000 : ℝ)|^4395 ≤ (11997109599939/100000000000000 : ℝ)^3371
        have hw : |(-98313791/500000000 : ℝ)|=(98313791/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351971811/2500000000 : ℝ)|^4395 ≤ (44867318744057/100000000000000 : ℝ)^3371
        have hw : |(1351971811/2500000000 : ℝ)|=(1351971811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247059207/10000000000 : ℝ)|^4395 ≤ (43135571634747/100000000000000 : ℝ)^3371
        have hw : |(5247059207/10000000000 : ℝ)|=(5247059207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s7_1 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534719457/1000000000 : ℝ)*x 0 + (-409630147/2000000000 : ℝ)*x 1 + (1311764829/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534719457/1000000000 : ℝ)^4395 ≤ (44211934461601/100000000000000 : ℝ)^3371 := by
    have hnat : (534719457 : ℕ)^4395*100000000000000^3371 ≤ 44211934461601^3371*1000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534719457 1000000000 44211934461601 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (409630147/2000000000 : ℝ)^4395 ≤ (12652492714989/100000000000000 : ℝ)^3371 := by
    have hnat : (409630147 : ℕ)^4395*100000000000000^3371 ≤ 12652492714989^3371*2000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409630147 2000000000 12652492714989 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311764829/2500000000 : ℝ)^4395 ≤ (1725422912121/4000000000000 : ℝ)^3371 := by
    have hnat : (1311764829 : ℕ)^4395*4000000000000^3371 ≤ 1725422912121^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311764829 2500000000 1725422912121 4000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534719457/1000000000 : ℝ), (-409630147/2000000000 : ℝ), (1311764829/2500000000 : ℝ)] ![(44211934461601/100000000000000 : ℝ), (12652492714989/100000000000000 : ℝ), (1725422912121/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534719457/1000000000 : ℝ)|^4395 ≤ (44211934461601/100000000000000 : ℝ)^3371
        have hw : |(534719457/1000000000 : ℝ)|=(534719457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-409630147/2000000000 : ℝ)|^4395 ≤ (12652492714989/100000000000000 : ℝ)^3371
        have hw : |(-409630147/2000000000 : ℝ)|=(409630147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311764829/2500000000 : ℝ)|^4395 ≤ (1725422912121/4000000000000 : ℝ)^3371
        have hw : |(1311764829/2500000000 : ℝ)|=(1311764829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s7_2 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534719471/1000000000 : ℝ)*x 0 + (5247059181/10000000000 : ℝ)*x 1 + (-256018841/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534719471/1000000000 : ℝ)^4395 ≤ (1381622999087/3125000000000 : ℝ)^3371 := by
    have hnat : (534719471 : ℕ)^4395*3125000000000^3371 ≤ 1381622999087^3371*1000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534719471 1000000000 1381622999087 3125000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247059181/10000000000 : ℝ)^4395 ≤ (10783892839019/25000000000000 : ℝ)^3371 := by
    have hnat : (5247059181 : ℕ)^4395*25000000000000^3371 ≤ 10783892839019^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247059181 10000000000 10783892839019 25000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256018841/1250000000 : ℝ)^4395 ≤ (12652492658611/100000000000000 : ℝ)^3371 := by
    have hnat : (256018841 : ℕ)^4395*100000000000000^3371 ≤ 12652492658611^3371*1250000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256018841 1250000000 12652492658611 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534719471/1000000000 : ℝ), (5247059181/10000000000 : ℝ), (-256018841/1250000000 : ℝ)] ![(1381622999087/3125000000000 : ℝ), (10783892839019/25000000000000 : ℝ), (12652492658611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534719471/1000000000 : ℝ)|^4395 ≤ (1381622999087/3125000000000 : ℝ)^3371
        have hw : |(534719471/1000000000 : ℝ)|=(534719471/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247059181/10000000000 : ℝ)|^4395 ≤ (10783892839019/25000000000000 : ℝ)^3371
        have hw : |(5247059181/10000000000 : ℝ)|=(5247059181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256018841/1250000000 : ℝ)|^4395 ≤ (12652492658611/100000000000000 : ℝ)^3371
        have hw : |(-256018841/1250000000 : ℝ)|=(256018841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s7_3 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4302876367/10000000000 : ℝ)*x 0 + (4131701819/10000000000 : ℝ)*x 1 + (4480389689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302876367/10000000000 : ℝ)^4395 ≤ (33304793179791/100000000000000 : ℝ)^3371 := by
    have hnat : (4302876367 : ℕ)^4395*100000000000000^3371 ≤ 33304793179791^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302876367 10000000000 33304793179791 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4131701819/10000000000 : ℝ)^4395 ≤ (3158795104553/10000000000000 : ℝ)^3371 := by
    have hnat : (4131701819 : ℕ)^4395*10000000000000^3371 ≤ 3158795104553^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131701819 10000000000 3158795104553 10000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4480389689/10000000000 : ℝ)^4395 ≤ (35107255758491/100000000000000 : ℝ)^3371 := by
    have hnat : (4480389689 : ℕ)^4395*100000000000000^3371 ≤ 35107255758491^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480389689 10000000000 35107255758491 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302876367/10000000000 : ℝ), (4131701819/10000000000 : ℝ), (4480389689/10000000000 : ℝ)] ![(33304793179791/100000000000000 : ℝ), (3158795104553/10000000000000 : ℝ), (35107255758491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302876367/10000000000 : ℝ)|^4395 ≤ (33304793179791/100000000000000 : ℝ)^3371
        have hw : |(4302876367/10000000000 : ℝ)|=(4302876367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4131701819/10000000000 : ℝ)|^4395 ≤ (3158795104553/10000000000000 : ℝ)^3371
        have hw : |(4131701819/10000000000 : ℝ)|=(4131701819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4480389689/10000000000 : ℝ)|^4395 ≤ (35107255758491/100000000000000 : ℝ)^3371
        have hw : |(4480389689/10000000000 : ℝ)|=(4480389689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s7_4 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1966286989/10000000000 : ℝ)*x 0 + (5247639319/10000000000 : ℝ)*x 1 + (1081460839/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1966286989/10000000000 : ℝ)^4395 ≤ (59985992239/500000000000 : ℝ)^3371 := by
    have hnat : (1966286989 : ℕ)^4395*500000000000^3371 ≤ 59985992239^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966286989 10000000000 59985992239 500000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247639319/10000000000 : ℝ)^4395 ≤ (8628357893/20000000000 : ℝ)^3371 := by
    have hnat : (5247639319 : ℕ)^4395*20000000000^3371 ≤ 8628357893^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247639319 10000000000 8628357893 20000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081460839/2000000000 : ℝ)^4395 ≤ (44861012067493/100000000000000 : ℝ)^3371 := by
    have hnat : (1081460839 : ℕ)^4395*100000000000000^3371 ≤ 44861012067493^3371*2000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081460839 2000000000 44861012067493 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1966286989/10000000000 : ℝ), (5247639319/10000000000 : ℝ), (1081460839/2000000000 : ℝ)] ![(59985992239/500000000000 : ℝ), (8628357893/20000000000 : ℝ), (44861012067493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1966286989/10000000000 : ℝ)|^4395 ≤ (59985992239/500000000000 : ℝ)^3371
        have hw : |(-1966286989/10000000000 : ℝ)|=(1966286989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247639319/10000000000 : ℝ)|^4395 ≤ (8628357893/20000000000 : ℝ)^3371
        have hw : |(5247639319/10000000000 : ℝ)|=(5247639319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081460839/2000000000 : ℝ)|^4395 ≤ (44861012067493/100000000000000 : ℝ)^3371
        have hw : |(1081460839/2000000000 : ℝ)|=(1081460839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_s7_5 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2151450949/5000000000 : ℝ)*x 0 + (4479131413/10000000000 : ℝ)*x 1 + (2066482743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151450949/5000000000 : ℝ)^4395 ≤ (33305050821527/100000000000000 : ℝ)^3371 := by
    have hnat : (2151450949 : ℕ)^4395*100000000000000^3371 ≤ 33305050821527^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151450949 5000000000 33305050821527 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4479131413/10000000000 : ℝ)^4395 ≤ (17547200874629/50000000000000 : ℝ)^3371 := by
    have hnat : (4479131413 : ℕ)^4395*50000000000000^3371 ≤ 17547200874629^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479131413 10000000000 17547200874629 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2066482743/5000000000 : ℝ)^4395 ≤ (31600547416099/100000000000000 : ℝ)^3371 := by
    have hnat : (2066482743 : ℕ)^4395*100000000000000^3371 ≤ 31600547416099^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066482743 5000000000 31600547416099 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2151450949/5000000000 : ℝ), (4479131413/10000000000 : ℝ), (2066482743/5000000000 : ℝ)] ![(33305050821527/100000000000000 : ℝ), (17547200874629/50000000000000 : ℝ), (31600547416099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2151450949/5000000000 : ℝ)|^4395 ≤ (33305050821527/100000000000000 : ℝ)^3371
        have hw : |(2151450949/5000000000 : ℝ)|=(2151450949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4479131413/10000000000 : ℝ)|^4395 ≤ (17547200874629/50000000000000 : ℝ)^3371
        have hw : |(4479131413/10000000000 : ℝ)|=(4479131413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2066482743/5000000000 : ℝ)|^4395 ≤ (31600547416099/100000000000000 : ℝ)^3371
        have hw : |(2066482743/5000000000 : ℝ)|=(2066482743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1435_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79202277/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11353/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (369/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1419/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1419/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1419/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1419/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1419/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1419/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1419/12500 : ℝ) ^ (2197/512 : ℝ) ≤ (4408296861953263/50000000000000000000 : ℝ) := by
    have hpowers : (1419/12500 : ℝ)^2197 ≤ (4408296861953263/50000000000000000000 : ℝ)^512 := by
      have hnat : (1419 : ℕ)^2197*50000000000000000000^512 ≤ 4408296861953263^512*12500^2197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1419 12500 4408296861953263 50000000000000000000 2197 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1419/12500 : ℝ)) (X := (4408296861953263/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hpowhi : (369/2500 : ℝ) ^ (2197/512 : ℝ) ≤ (27197975419972477/100000000000000000000 : ℝ) := by
    have hpowers : (369/2500 : ℝ)^2197 ≤ (27197975419972477/100000000000000000000 : ℝ)^512 := by
      have hnat : (369 : ℕ)^2197*100000000000000000000^512 ≤ 27197975419972477^512*2500^2197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        369 2500 27197975419972477 100000000000000000000 2197 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (369/2500 : ℝ)) (X := (27197975419972477/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004408296861953263/25000000000000000000 : ℝ) ≤ (10000410904941131/10000000000000000 : ℝ) ^ (2197/512 : ℝ) := by
    have hpowers : (25004408296861953263/25000000000000000000 : ℝ)^512 ≤ (10000410904941131/10000000000000000 : ℝ)^2197 := by
      have hnat : (25004408296861953263 : ℕ)^512*10000000000000000^2197 ≤ 10000410904941131^2197*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004408296861953263 25000000000000000000 10000410904941131 10000000000000000 512 2197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000410904941131/10000000000000000 : ℝ)) (X := (25004408296861953263/25000000000000000000 : ℝ)) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036014569143879003/100000000000000000000 : ℝ) ≤ (10000839185858413/10000000000000000 : ℝ) ^ (2197/512 : ℝ) := by
    have hpowers : (100036014569143879003/100000000000000000000 : ℝ)^512 ≤ (10000839185858413/10000000000000000 : ℝ)^2197 := by
      have hnat : (100036014569143879003 : ℕ)^512*10000000000000000^2197 ≤ 10000839185858413^2197*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036014569143879003 100000000000000000000 10000839185858413 10000000000000000 512 2197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000839185858413/10000000000000000 : ℝ)) (X := (100036014569143879003/100000000000000000000 : ℝ)) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027197975419972477/50000000000000000000 : ℝ) ≤ (2000253493355139/2000000000000000 : ℝ) ^ (2197/512 : ℝ) := by
    have hpowers : (50027197975419972477/50000000000000000000 : ℝ)^512 ≤ (2000253493355139/2000000000000000 : ℝ)^2197 := by
      have hnat : (50027197975419972477 : ℕ)^512*2000000000000000^2197 ≤ 2000253493355139^2197*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027197975419972477 50000000000000000000 2000253493355139 2000000000000000 512 2197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000253493355139/2000000000000000 : ℝ)) (X := (50027197975419972477/50000000000000000000 : ℝ)) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4408296861953263/50000000000000000000 : ℝ) ≤ ((141965319475389183/142000000000000000 : ℝ)+2*(214140458641/170400000000000 : ℝ)*(1419/12500 : ℝ))^(2197/512 : ℝ) := by
    rw [show (141965319475389183/142000000000000000 : ℝ)+2*(214140458641/170400000000000 : ℝ)*(1419/12500 : ℝ)=(10000410904941131/10000000000000000 : ℝ) by norm_num, show 1+2*(4408296861953263/50000000000000000000 : ℝ)=(25004408296861953263/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27197975419972477/100000000000000000000 : ℝ)+(4408296861953263/50000000000000000000 : ℝ) ≤ ((141965319475389183/142000000000000000 : ℝ)+(214140458641/170400000000000 : ℝ)*((369/2500 : ℝ)+(1419/12500 : ℝ)))^(2197/512 : ℝ) := by
    rw [show (141965319475389183/142000000000000000 : ℝ)+(214140458641/170400000000000 : ℝ)*((369/2500 : ℝ)+(1419/12500 : ℝ))=(10000839185858413/10000000000000000 : ℝ) by norm_num, show 1+(27197975419972477/100000000000000000000 : ℝ)+(4408296861953263/50000000000000000000 : ℝ)=(100036014569143879003/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27197975419972477/100000000000000000000 : ℝ) ≤ ((141965319475389183/142000000000000000 : ℝ)+2*(214140458641/170400000000000 : ℝ)*(369/2500 : ℝ))^(2197/512 : ℝ) := by
    rw [show (141965319475389183/142000000000000000 : ℝ)+2*(214140458641/170400000000000 : ℝ)*(369/2500 : ℝ)=(2000253493355139/2000000000000000 : ℝ) by norm_num, show 1+2*(27197975419972477/100000000000000000000 : ℝ)=(50027197975419972477/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (141965319475389183/142000000000000000 : ℝ)*(X 1 0+X 2 0)+(214140458641/170400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2197/512 : ℝ)) (lo := (1419/12500 : ℝ)) (hi := (369/2500 : ℝ)) (c := (141965319475389183/142000000000000000 : ℝ)) (alpha := (214140458641/170400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (141965319475389183/142000000000000000 : ℝ)*(X 0 1+X 2 1)+(214140458641/170400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2197/512 : ℝ)) (lo := (1419/12500 : ℝ)) (hi := (369/2500 : ℝ)) (c := (141965319475389183/142000000000000000 : ℝ)) (alpha := (214140458641/170400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (141965319475389183/142000000000000000 : ℝ)*(X 0 2+X 1 2)+(214140458641/170400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2197/512 : ℝ)) (lo := (1419/12500 : ℝ)) (hi := (369/2500 : ℝ)) (c := (141965319475389183/142000000000000000 : ℝ)) (alpha := (214140458641/170400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-98313791/500000000 : ℝ)*X 0 0+(1351971811/2500000000 : ℝ)*X 0 1+(5247059207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534719457/1000000000 : ℝ)*X 1 0+(-409630147/2000000000 : ℝ)*X 1 1+(1311764829/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534719471/1000000000 : ℝ)*X 2 0+(5247059181/10000000000 : ℝ)*X 2 1+(-256018841/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4302876367/10000000000 : ℝ)*X 0 0+(4131701819/10000000000 : ℝ)*X 0 1+(4480389689/10000000000 : ℝ)*X 0 2+(4302876367/10000000000 : ℝ)*X 1 0+(4131701819/10000000000 : ℝ)*X 1 1+(4480389689/10000000000 : ℝ)*X 1 2+(4302876367/10000000000 : ℝ)*X 2 0+(4131701819/10000000000 : ℝ)*X 2 1+(4480389689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1966286989/10000000000 : ℝ)*X 0 0+(5247639319/10000000000 : ℝ)*X 0 1+(1081460839/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2151450949/5000000000 : ℝ)*X 0 0+(4479131413/10000000000 : ℝ)*X 0 1+(2066482743/5000000000 : ℝ)*X 0 2+(2151450949/5000000000 : ℝ)*X 1 0+(4479131413/10000000000 : ℝ)*X 1 1+(2066482743/5000000000 : ℝ)*X 1 2+(2151450949/5000000000 : ℝ)*X 2 0+(4479131413/10000000000 : ℝ)*X 2 1+(2066482743/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1061428076667751435304767/1775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100362063/6250000000000 : ℝ)*(base19) + (60627313/5000000000000 : ℝ)*(base23) + (58957181/50000000000000 : ℝ)*(upper2) + (88911941/25000000000000 : ℝ)*(upper3) + (415241433/100000000000000 : ℝ)*(upper4) + (2271448434504367/50000000000000 : ℝ)*(major0) + (2271448434504367/50000000000000 : ℝ)*(major1) + (2271448434504367/50000000000000 : ℝ)*(major2) + (6217856058811037/100000000000000 : ℝ)*(sp0) + (3108942058519933/50000000000000 : ℝ)*(sp1) + (6217884510286613/100000000000000 : ℝ)*(sp2) + (1433948582965567/50000000000000 : ℝ)*(sp3) + (29664021837/100000000000000 : ℝ)*(sp4) + (10829320527/100000000000000 : ℝ)*(sp5) + (143395399762583/5000000000000 : ℝ)*(f.failure) + (3108942861416437/50000000000000 : ℝ)*(f.sum) + (2866144985587/4260000000000000000000000000 : ℝ)*base65 + (186948665060903983/21300000000000000000000000000000 : ℝ)*base67 + (183299679118703983/21300000000000000000000000000000 : ℝ)*base69 + (30716665759896017/21300000000000000000000000000000 : ℝ)*base72 + (11303380093373/4260000000000000000000000000 : ℝ)*base74 + (219660530362103983/21300000000000000000000000000000 : ℝ)*base75 + (146740245547103983/21300000000000000000000000000000 : ℝ)*base77 + (413399126822303983/21300000000000000000000000000000 : ℝ)*base79 + (21270324438593/4260000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1998509/250000000000000000000 : ℝ)*base90 + (1998509/250000000000000000000 : ℝ)*base92 + (1998509/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1435_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79202277/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1419/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11353/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (369/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1435_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1435_box_0 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-903022101/5000000000 : ℝ)*x 0 + (538599959/1000000000 : ℝ)*x 1 + (1346500101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (903022101/5000000000 : ℝ)^4395 ≤ (5369287633109/50000000000000 : ℝ)^3371 := by
    have hnat : (903022101 : ℕ)^4395*50000000000000^3371 ≤ 5369287633109^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903022101 5000000000 5369287633109 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538599959/1000000000 : ℝ)^4395 ≤ (1394709623923/3125000000000 : ℝ)^3371 := by
    have hnat : (538599959 : ℕ)^4395*3125000000000^3371 ≤ 1394709623923^3371*1000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538599959 1000000000 1394709623923 3125000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346500101/2500000000 : ℝ)^4395 ≤ (1394709898739/3125000000000 : ℝ)^3371 := by
    have hnat : (1346500101 : ℕ)^4395*3125000000000^3371 ≤ 1394709898739^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346500101 2500000000 1394709898739 3125000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-903022101/5000000000 : ℝ), (538599959/1000000000 : ℝ), (1346500101/2500000000 : ℝ)] ![(5369287633109/50000000000000 : ℝ), (1394709623923/3125000000000 : ℝ), (1394709898739/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-903022101/5000000000 : ℝ)|^4395 ≤ (5369287633109/50000000000000 : ℝ)^3371
        have hw : |(-903022101/5000000000 : ℝ)|=(903022101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(538599959/1000000000 : ℝ)|^4395 ≤ (1394709623923/3125000000000 : ℝ)^3371
        have hw : |(538599959/1000000000 : ℝ)|=(538599959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346500101/2500000000 : ℝ)|^4395 ≤ (1394709898739/3125000000000 : ℝ)^3371
        have hw : |(1346500101/2500000000 : ℝ)|=(1346500101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_box_1 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66076333/125000000 : ℝ)*x 0 + (-971653979/5000000000 : ℝ)*x 1 + (5385999907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66076333/125000000 : ℝ)^4395 ≤ (680539999997/1562500000000 : ℝ)^3371 := by
    have hnat : (66076333 : ℕ)^4395*1562500000000^3371 ≤ 680539999997^3371*125000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66076333 125000000 680539999997 1562500000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (971653979/5000000000 : ℝ)^4395 ≤ (2362945719421/20000000000000 : ℝ)^3371 := by
    have hnat : (971653979 : ℕ)^4395*20000000000000^3371 ≤ 2362945719421^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971653979 5000000000 2362945719421 20000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385999907/10000000000 : ℝ)^4395 ≤ (4463071139027/10000000000000 : ℝ)^3371 := by
    have hnat : (5385999907 : ℕ)^4395*10000000000000^3371 ≤ 4463071139027^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385999907 10000000000 4463071139027 10000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66076333/125000000 : ℝ), (-971653979/5000000000 : ℝ), (5385999907/10000000000 : ℝ)] ![(680539999997/1562500000000 : ℝ), (2362945719421/20000000000000 : ℝ), (4463071139027/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66076333/125000000 : ℝ)|^4395 ≤ (680539999997/1562500000000 : ℝ)^3371
        have hw : |(66076333/125000000 : ℝ)|=(66076333/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-971653979/5000000000 : ℝ)|^4395 ≤ (2362945719421/20000000000000 : ℝ)^3371
        have hw : |(-971653979/5000000000 : ℝ)|=(971653979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385999907/10000000000 : ℝ)|^4395 ≤ (4463071139027/10000000000000 : ℝ)^3371
        have hw : |(5385999907/10000000000 : ℝ)|=(5385999907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_box_2 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286106631/10000000000 : ℝ)*x 0 + (2692999919/5000000000 : ℝ)*x 1 + (-60728377/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286106631/10000000000 : ℝ)^4395 ≤ (5444319987891/12500000000000 : ℝ)^3371 := by
    have hnat : (5286106631 : ℕ)^4395*12500000000000^3371 ≤ 5444319987891^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286106631 10000000000 5444319987891 12500000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692999919/5000000000 : ℝ)^4395 ≤ (44630710644823/100000000000000 : ℝ)^3371 := by
    have hnat : (2692999919 : ℕ)^4395*100000000000000^3371 ≤ 44630710644823^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692999919 5000000000 44630710644823 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60728377/312500000 : ℝ)^4395 ≤ (2953682359329/25000000000000 : ℝ)^3371 := by
    have hnat : (60728377 : ℕ)^4395*25000000000000^3371 ≤ 2953682359329^3371*312500000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60728377 312500000 2953682359329 25000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286106631/10000000000 : ℝ), (2692999919/5000000000 : ℝ), (-60728377/312500000 : ℝ)] ![(5444319987891/12500000000000 : ℝ), (44630710644823/100000000000000 : ℝ), (2953682359329/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286106631/10000000000 : ℝ)|^4395 ≤ (5444319987891/12500000000000 : ℝ)^3371
        have hw : |(5286106631/10000000000 : ℝ)|=(5286106631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692999919/5000000000 : ℝ)|^4395 ≤ (44630710644823/100000000000000 : ℝ)^3371
        have hw : |(2692999919/5000000000 : ℝ)|=(2692999919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-60728377/312500000 : ℝ)|^4395 ≤ (2953682359329/25000000000000 : ℝ)^3371
        have hw : |(-60728377/312500000 : ℝ)|=(60728377/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_box_3 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1112263691/2500000000 : ℝ)*x 0 + (4233484489/10000000000 : ℝ)*x 1 + (330741/781250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1112263691/2500000000 : ℝ)^4395 ≤ (34787478513187/100000000000000 : ℝ)^3371 := by
    have hnat : (1112263691 : ℕ)^4395*100000000000000^3371 ≤ 34787478513187^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112263691 2500000000 34787478513187 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4233484489/10000000000 : ℝ)^4395 ≤ (32606259172963/100000000000000 : ℝ)^3371 := by
    have hnat : (4233484489 : ℕ)^4395*100000000000000^3371 ≤ 32606259172963^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233484489 10000000000 32606259172963 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (330741/781250 : ℝ)^4395 ≤ (16303131147951/50000000000000 : ℝ)^3371 := by
    have hnat : (330741 : ℕ)^4395*50000000000000^3371 ≤ 16303131147951^3371*781250^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330741 781250 16303131147951 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1112263691/2500000000 : ℝ), (4233484489/10000000000 : ℝ), (330741/781250 : ℝ)] ![(34787478513187/100000000000000 : ℝ), (32606259172963/100000000000000 : ℝ), (16303131147951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1112263691/2500000000 : ℝ)|^4395 ≤ (34787478513187/100000000000000 : ℝ)^3371
        have hw : |(1112263691/2500000000 : ℝ)|=(1112263691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4233484489/10000000000 : ℝ)|^4395 ≤ (32606259172963/100000000000000 : ℝ)^3371
        have hw : |(4233484489/10000000000 : ℝ)|=(4233484489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(330741/781250 : ℝ)|^4395 ≤ (16303131147951/50000000000000 : ℝ)^3371
        have hw : |(330741/781250 : ℝ)|=(330741/781250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_box_4 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2129235073/10000000000 : ℝ)*x 0 + (5266613743/10000000000 : ℝ)*x 1 + (5266613887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129235073/10000000000 : ℝ)^4395 ≤ (13309441309671/100000000000000 : ℝ)^3371 := by
    have hnat : (2129235073 : ℕ)^4395*100000000000000^3371 ≤ 13309441309671^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129235073 10000000000 13309441309671 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266613743/10000000000 : ℝ)^4395 ≤ (169317494387/390625000000 : ℝ)^3371 := by
    have hnat : (5266613743 : ℕ)^4395*390625000000^3371 ≤ 169317494387^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266613743 10000000000 169317494387 390625000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266613887/10000000000 : ℝ)^4395 ≤ (4334528010823/10000000000000 : ℝ)^3371 := by
    have hnat : (5266613887 : ℕ)^4395*10000000000000^3371 ≤ 4334528010823^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266613887 10000000000 4334528010823 10000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2129235073/10000000000 : ℝ), (5266613743/10000000000 : ℝ), (5266613887/10000000000 : ℝ)] ![(13309441309671/100000000000000 : ℝ), (169317494387/390625000000 : ℝ), (4334528010823/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2129235073/10000000000 : ℝ)|^4395 ≤ (13309441309671/100000000000000 : ℝ)^3371
        have hw : |(-2129235073/10000000000 : ℝ)|=(2129235073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266613743/10000000000 : ℝ)|^4395 ≤ (169317494387/390625000000 : ℝ)^3371
        have hw : |(5266613743/10000000000 : ℝ)|=(5266613743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266613887/10000000000 : ℝ)|^4395 ≤ (4334528010823/10000000000000 : ℝ)^3371
        have hw : |(5266613887/10000000000 : ℝ)|=(5266613887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_box_5 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369638537/10000000000 : ℝ)*x 0 + (-1991817431/10000000000 : ℝ)*x 1 + (1316653451/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369638537/10000000000 : ℝ)^4395 ≤ (1778161266923/4000000000000 : ℝ)^3371 := by
    have hnat : (5369638537 : ℕ)^4395*4000000000000^3371 ≤ 1778161266923^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369638537 10000000000 1778161266923 4000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1991817431/10000000000 : ℝ)^4395 ≤ (12200689094711/100000000000000 : ℝ)^3371 := by
    have hnat : (1991817431 : ℕ)^4395*100000000000000^3371 ≤ 12200689094711^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991817431 10000000000 12200689094711 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316653451/2500000000 : ℝ)^4395 ≤ (21672639608809/50000000000000 : ℝ)^3371 := by
    have hnat : (1316653451 : ℕ)^4395*50000000000000^3371 ≤ 21672639608809^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316653451 2500000000 21672639608809 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369638537/10000000000 : ℝ), (-1991817431/10000000000 : ℝ), (1316653451/2500000000 : ℝ)] ![(1778161266923/4000000000000 : ℝ), (12200689094711/100000000000000 : ℝ), (21672639608809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369638537/10000000000 : ℝ)|^4395 ≤ (1778161266923/4000000000000 : ℝ)^3371
        have hw : |(5369638537/10000000000 : ℝ)|=(5369638537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1991817431/10000000000 : ℝ)|^4395 ≤ (12200689094711/100000000000000 : ℝ)^3371
        have hw : |(-1991817431/10000000000 : ℝ)|=(1991817431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316653451/2500000000 : ℝ)|^4395 ≤ (21672639608809/50000000000000 : ℝ)^3371
        have hw : |(1316653451/2500000000 : ℝ)|=(1316653451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_box_6 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684819179/5000000000 : ℝ)*x 0 + (5266613809/10000000000 : ℝ)*x 1 + (-995908833/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684819179/5000000000 : ℝ)^4395 ≤ (44454029741021/100000000000000 : ℝ)^3371 := by
    have hnat : (2684819179 : ℕ)^4395*100000000000000^3371 ≤ 44454029741021^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684819179 5000000000 44454029741021 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266613809/10000000000 : ℝ)^4395 ≤ (43345279271269/100000000000000 : ℝ)^3371 := by
    have hnat : (5266613809 : ℕ)^4395*100000000000000^3371 ≤ 43345279271269^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266613809 10000000000 43345279271269 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995908833/5000000000 : ℝ)^4395 ≤ (6100345485723/50000000000000 : ℝ)^3371 := by
    have hnat : (995908833 : ℕ)^4395*50000000000000^3371 ≤ 6100345485723^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995908833 5000000000 6100345485723 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684819179/5000000000 : ℝ), (5266613809/10000000000 : ℝ), (-995908833/5000000000 : ℝ)] ![(44454029741021/100000000000000 : ℝ), (43345279271269/100000000000000 : ℝ), (6100345485723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684819179/5000000000 : ℝ)|^4395 ≤ (44454029741021/100000000000000 : ℝ)^3371
        have hw : |(2684819179/5000000000 : ℝ)|=(2684819179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266613809/10000000000 : ℝ)|^4395 ≤ (43345279271269/100000000000000 : ℝ)^3371
        have hw : |(5266613809/10000000000 : ℝ)|=(5266613809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-995908833/5000000000 : ℝ)|^4395 ≤ (6100345485723/50000000000000 : ℝ)^3371
        have hw : |(-995908833/5000000000 : ℝ)|=(995908833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_box_7 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4155641847/10000000000 : ℝ)*x 0 + (2190070093/5000000000 : ℝ)*x 1 + (1095035143/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4155641847/10000000000 : ℝ)^4395 ≤ (31826786493893/100000000000000 : ℝ)^3371 := by
    have hnat : (4155641847 : ℕ)^4395*100000000000000^3371 ≤ 31826786493893^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155641847 10000000000 31826786493893 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2190070093/5000000000 : ℝ)^4395 ≤ (17043302392283/50000000000000 : ℝ)^3371 := by
    have hnat : (2190070093 : ℕ)^4395*50000000000000^3371 ≤ 17043302392283^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190070093 5000000000 17043302392283 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095035143/2500000000 : ℝ)^4395 ≤ (34086608700931/100000000000000 : ℝ)^3371 := by
    have hnat : (1095035143 : ℕ)^4395*100000000000000^3371 ≤ 34086608700931^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095035143 2500000000 34086608700931 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4155641847/10000000000 : ℝ), (2190070093/5000000000 : ℝ), (1095035143/2500000000 : ℝ)] ![(31826786493893/100000000000000 : ℝ), (17043302392283/50000000000000 : ℝ), (34086608700931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4155641847/10000000000 : ℝ)|^4395 ≤ (31826786493893/100000000000000 : ℝ)^3371
        have hw : |(4155641847/10000000000 : ℝ)|=(4155641847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2190070093/5000000000 : ℝ)|^4395 ≤ (17043302392283/50000000000000 : ℝ)^3371
        have hw : |(2190070093/5000000000 : ℝ)|=(2190070093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1095035143/2500000000 : ℝ)|^4395 ≤ (34086608700931/100000000000000 : ℝ)^3371
        have hw : |(1095035143/2500000000 : ℝ)|=(1095035143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_box_8 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2061148681/10000000000 : ℝ)*x 0 + (5184007841/10000000000 : ℝ)*x 1 + (337498171/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2061148681/10000000000 : ℝ)^4395 ≤ (3189319893851/25000000000000 : ℝ)^3371 := by
    have hnat : (2061148681 : ℕ)^4395*25000000000000^3371 ≤ 3189319893851^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061148681 10000000000 3189319893851 25000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184007841/10000000000 : ℝ)^4395 ≤ (2653813416629/6250000000000 : ℝ)^3371 := by
    have hnat : (5184007841 : ℕ)^4395*6250000000000^3371 ≤ 2653813416629^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184007841 10000000000 2653813416629 6250000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337498171/625000000 : ℝ)^4395 ≤ (22390852876869/50000000000000 : ℝ)^3371 := by
    have hnat : (337498171 : ℕ)^4395*50000000000000^3371 ≤ 22390852876869^3371*625000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337498171 625000000 22390852876869 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2061148681/10000000000 : ℝ), (5184007841/10000000000 : ℝ), (337498171/625000000 : ℝ)] ![(3189319893851/25000000000000 : ℝ), (2653813416629/6250000000000 : ℝ), (22390852876869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2061148681/10000000000 : ℝ)|^4395 ≤ (3189319893851/25000000000000 : ℝ)^3371
        have hw : |(-2061148681/10000000000 : ℝ)|=(2061148681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184007841/10000000000 : ℝ)|^4395 ≤ (2653813416629/6250000000000 : ℝ)^3371
        have hw : |(5184007841/10000000000 : ℝ)|=(5184007841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337498171/625000000 : ℝ)|^4395 ≤ (22390852876869/50000000000000 : ℝ)^3371
        have hw : |(337498171/625000000 : ℝ)|=(337498171/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_box_9 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276328127/10000000000 : ℝ)*x 0 + (-484376357/2500000000 : ℝ)*x 1 + (2699985041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276328127/10000000000 : ℝ)^4395 ≤ (43449545670039/100000000000000 : ℝ)^3371 := by
    have hnat : (5276328127 : ℕ)^4395*100000000000000^3371 ≤ 43449545670039^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276328127 10000000000 43449545670039 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (484376357/2500000000 : ℝ)^4395 ≤ (11768755633233/100000000000000 : ℝ)^3371 := by
    have hnat : (484376357 : ℕ)^4395*100000000000000^3371 ≤ 11768755633233^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484376357 2500000000 11768755633233 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699985041/5000000000 : ℝ)^4395 ≤ (44781698682637/100000000000000 : ℝ)^3371 := by
    have hnat : (2699985041 : ℕ)^4395*100000000000000^3371 ≤ 44781698682637^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699985041 5000000000 44781698682637 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276328127/10000000000 : ℝ), (-484376357/2500000000 : ℝ), (2699985041/5000000000 : ℝ)] ![(43449545670039/100000000000000 : ℝ), (11768755633233/100000000000000 : ℝ), (44781698682637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276328127/10000000000 : ℝ)|^4395 ≤ (43449545670039/100000000000000 : ℝ)^3371
        have hw : |(5276328127/10000000000 : ℝ)|=(5276328127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-484376357/2500000000 : ℝ)|^4395 ≤ (11768755633233/100000000000000 : ℝ)^3371
        have hw : |(-484376357/2500000000 : ℝ)|=(484376357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699985041/5000000000 : ℝ)|^4395 ≤ (44781698682637/100000000000000 : ℝ)^3371
        have hw : |(2699985041/5000000000 : ℝ)|=(2699985041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_box_10 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319082019/2500000000 : ℝ)*x 0 + (5399969623/10000000000 : ℝ)*x 1 + (-484376531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319082019/2500000000 : ℝ)^4395 ≤ (43449545122489/100000000000000 : ℝ)^3371 := by
    have hnat : (1319082019 : ℕ)^4395*100000000000000^3371 ≤ 43449545122489^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319082019 2500000000 43449545122489 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399969623/10000000000 : ℝ)^4395 ≤ (44781693719891/100000000000000 : ℝ)^3371 := by
    have hnat : (5399969623 : ℕ)^4395*100000000000000^3371 ≤ 44781693719891^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399969623 10000000000 44781693719891 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (484376531/2500000000 : ℝ)^4395 ≤ (5884380572539/50000000000000 : ℝ)^3371 := by
    have hnat : (484376531 : ℕ)^4395*50000000000000^3371 ≤ 5884380572539^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      484376531 2500000000 5884380572539 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319082019/2500000000 : ℝ), (5399969623/10000000000 : ℝ), (-484376531/2500000000 : ℝ)] ![(43449545122489/100000000000000 : ℝ), (44781693719891/100000000000000 : ℝ), (5884380572539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319082019/2500000000 : ℝ)|^4395 ≤ (43449545122489/100000000000000 : ℝ)^3371
        have hw : |(1319082019/2500000000 : ℝ)|=(1319082019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399969623/10000000000 : ℝ)|^4395 ≤ (44781693719891/100000000000000 : ℝ)^3371
        have hw : |(5399969623/10000000000 : ℝ)|=(5399969623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-484376531/2500000000 : ℝ)|^4395 ≤ (5884380572539/50000000000000 : ℝ)^3371
        have hw : |(-484376531/2500000000 : ℝ)|=(484376531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_box_11 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4482832783/10000000000 : ℝ)*x 0 + (1054076997/2500000000 : ℝ)*x 1 + (1054077287/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4482832783/10000000000 : ℝ)^4395 ≤ (35132216492961/100000000000000 : ℝ)^3371 := by
    have hnat : (4482832783 : ℕ)^4395*100000000000000^3371 ≤ 35132216492961^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482832783 10000000000 35132216492961 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054076997/2500000000 : ℝ)^4395 ≤ (32433885924693/100000000000000 : ℝ)^3371 := by
    have hnat : (1054076997 : ℕ)^4395*100000000000000^3371 ≤ 32433885924693^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054076997 2500000000 32433885924693 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054077287/2500000000 : ℝ)^4395 ≤ (32433897558579/100000000000000 : ℝ)^3371 := by
    have hnat : (1054077287 : ℕ)^4395*100000000000000^3371 ≤ 32433897558579^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054077287 2500000000 32433897558579 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4482832783/10000000000 : ℝ), (1054076997/2500000000 : ℝ), (1054077287/2500000000 : ℝ)] ![(35132216492961/100000000000000 : ℝ), (32433885924693/100000000000000 : ℝ), (32433897558579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4482832783/10000000000 : ℝ)|^4395 ≤ (35132216492961/100000000000000 : ℝ)^3371
        have hw : |(4482832783/10000000000 : ℝ)|=(4482832783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054076997/2500000000 : ℝ)|^4395 ≤ (32433885924693/100000000000000 : ℝ)^3371
        have hw : |(1054076997/2500000000 : ℝ)|=(1054076997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054077287/2500000000 : ℝ)|^4395 ≤ (32433897558579/100000000000000 : ℝ)^3371
        have hw : |(1054077287/2500000000 : ℝ)|=(1054077287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_box_12 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-374860301/2000000000 : ℝ)*x 0 + (68332421/125000000 : ℝ)*x 1 + (5255484089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (374860301/2000000000 : ℝ)^4395 ≤ (2254144541621/20000000000000 : ℝ)^3371 := by
    have hnat : (374860301 : ℕ)^4395*20000000000000^3371 ≤ 2254144541621^3371*2000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374860301 2000000000 2254144541621 20000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68332421/125000000 : ℝ)^4395 ≤ (1820135380067/4000000000000 : ℝ)^3371 := by
    have hnat : (68332421 : ℕ)^4395*4000000000000^3371 ≤ 1820135380067^3371*125000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68332421 125000000 1820135380067 4000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255484089/10000000000 : ℝ)^4395 ≤ (8645178554759/20000000000000 : ℝ)^3371 := by
    have hnat : (5255484089 : ℕ)^4395*20000000000000^3371 ≤ 8645178554759^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255484089 10000000000 8645178554759 20000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-374860301/2000000000 : ℝ), (68332421/125000000 : ℝ), (5255484089/10000000000 : ℝ)] ![(2254144541621/20000000000000 : ℝ), (1820135380067/4000000000000 : ℝ), (8645178554759/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-374860301/2000000000 : ℝ)|^4395 ≤ (2254144541621/20000000000000 : ℝ)^3371
        have hw : |(-374860301/2000000000 : ℝ)|=(374860301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68332421/125000000 : ℝ)|^4395 ≤ (1820135380067/4000000000000 : ℝ)^3371
        have hw : |(68332421/125000000 : ℝ)|=(68332421/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255484089/10000000000 : ℝ)|^4395 ≤ (8645178554759/20000000000000 : ℝ)^3371
        have hw : |(5255484089/10000000000 : ℝ)|=(5255484089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_box_13 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688711447/5000000000 : ℝ)*x 0 + (-199624009/1000000000 : ℝ)*x 1 + (5255485489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688711447/5000000000 : ℝ)^4395 ≤ (44538071385477/100000000000000 : ℝ)^3371 := by
    have hnat : (2688711447 : ℕ)^4395*100000000000000^3371 ≤ 44538071385477^3371*5000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688711447 5000000000 44538071385477 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199624009/1000000000 : ℝ)^4395 ≤ (6118010407241/50000000000000 : ℝ)^3371 := by
    have hnat : (199624009 : ℕ)^4395*50000000000000^3371 ≤ 6118010407241^3371*1000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199624009 1000000000 6118010407241 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255485489/10000000000 : ℝ)^4395 ≤ (43225907786517/100000000000000 : ℝ)^3371 := by
    have hnat : (5255485489 : ℕ)^4395*100000000000000^3371 ≤ 43225907786517^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255485489 10000000000 43225907786517 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688711447/5000000000 : ℝ), (-199624009/1000000000 : ℝ), (5255485489/10000000000 : ℝ)] ![(44538071385477/100000000000000 : ℝ), (6118010407241/50000000000000 : ℝ), (43225907786517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688711447/5000000000 : ℝ)|^4395 ≤ (44538071385477/100000000000000 : ℝ)^3371
        have hw : |(2688711447/5000000000 : ℝ)|=(2688711447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-199624009/1000000000 : ℝ)|^4395 ≤ (6118010407241/50000000000000 : ℝ)^3371
        have hw : |(-199624009/1000000000 : ℝ)|=(199624009/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255485489/10000000000 : ℝ)|^4395 ≤ (43225907786517/100000000000000 : ℝ)^3371
        have hw : |(5255485489/10000000000 : ℝ)|=(5255485489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_box_14 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377423763/10000000000 : ℝ)*x 0 + (41058473/78125000 : ℝ)*x 1 + (-249530023/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377423763/10000000000 : ℝ)^4395 ≤ (22269040384621/50000000000000 : ℝ)^3371 := by
    have hnat : (5377423763 : ℕ)^4395*50000000000000^3371 ≤ 22269040384621^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377423763 10000000000 22269040384621 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41058473/78125000 : ℝ)^4395 ≤ (4322589765293/10000000000000 : ℝ)^3371 := by
    have hnat : (41058473 : ℕ)^4395*10000000000000^3371 ≤ 4322589765293^3371*78125000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41058473 78125000 4322589765293 10000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249530023/1250000000 : ℝ)^4395 ≤ (6118010782841/50000000000000 : ℝ)^3371 := by
    have hnat : (249530023 : ℕ)^4395*50000000000000^3371 ≤ 6118010782841^3371*1250000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249530023 1250000000 6118010782841 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377423763/10000000000 : ℝ), (41058473/78125000 : ℝ), (-249530023/1250000000 : ℝ)] ![(22269040384621/50000000000000 : ℝ), (4322589765293/10000000000000 : ℝ), (6118010782841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377423763/10000000000 : ℝ)|^4395 ≤ (22269040384621/50000000000000 : ℝ)^3371
        have hw : |(5377423763/10000000000 : ℝ)|=(5377423763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41058473/78125000 : ℝ)|^4395 ≤ (4322589765293/10000000000000 : ℝ)^3371
        have hw : |(41058473/78125000 : ℝ)|=(41058473/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249530023/1250000000 : ℝ)|^4395 ≤ (6118010782841/50000000000000 : ℝ)^3371
        have hw : |(-249530023/1250000000 : ℝ)|=(249530023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1435_box_15 (p : ℝ) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1031960127/2500000000 : ℝ)*x 0 + (878760087/2000000000 : ℝ)*x 1 + (4393800087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031960127/2500000000 : ℝ)^4395 ≤ (31549468328193/100000000000000 : ℝ)^3371 := by
    have hnat : (1031960127 : ℕ)^4395*100000000000000^3371 ≤ 31549468328193^3371*2500000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031960127 2500000000 31549468328193 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (878760087/2000000000 : ℝ)^4395 ≤ (17112633797033/50000000000000 : ℝ)^3371 := by
    have hnat : (878760087 : ℕ)^4395*50000000000000^3371 ≤ 17112633797033^3371*2000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878760087 2000000000 17112633797033 50000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4393800087/10000000000 : ℝ)^4395 ≤ (34225264059909/100000000000000 : ℝ)^3371 := by
    have hnat : (4393800087 : ℕ)^4395*100000000000000^3371 ≤ 34225264059909^3371*10000000000^4395 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4393800087 10000000000 34225264059909 100000000000000 4395 3371 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4395/1024 : ℝ)) 4395 3371 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1031960127/2500000000 : ℝ), (878760087/2000000000 : ℝ), (4393800087/10000000000 : ℝ)] ![(31549468328193/100000000000000 : ℝ), (17112633797033/50000000000000 : ℝ), (34225264059909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1031960127/2500000000 : ℝ)|^4395 ≤ (31549468328193/100000000000000 : ℝ)^3371
        have hw : |(1031960127/2500000000 : ℝ)|=(1031960127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(878760087/2000000000 : ℝ)|^4395 ≤ (17112633797033/50000000000000 : ℝ)^3371
        have hw : |(878760087/2000000000 : ℝ)|=(878760087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4393800087/10000000000 : ℝ)|^4395 ≤ (34225264059909/100000000000000 : ℝ)^3371
        have hw : |(4393800087/10000000000 : ℝ)|=(4393800087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1435_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79202277/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11353/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62903/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(473/800 : ℝ) ∧ (40241/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84707/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11353/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11353/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11353/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11353/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11353/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11353/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11353/100000 : ℝ) ^ (2197/512 : ℝ) ≤ (8819926848085913/100000000000000000000 : ℝ) := by
    have hpowers : (11353/100000 : ℝ)^2197 ≤ (8819926848085913/100000000000000000000 : ℝ)^512 := by
      have hnat : (11353 : ℕ)^2197*100000000000000000000^512 ≤ 8819926848085913^512*100000^2197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11353 100000 8819926848085913 100000000000000000000 2197 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11353/100000 : ℝ)) (X := (8819926848085913/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hpowhi : (369/2500 : ℝ) ^ (2197/512 : ℝ) ≤ (27197975419972477/100000000000000000000 : ℝ) := by
    have hpowers : (369/2500 : ℝ)^2197 ≤ (27197975419972477/100000000000000000000 : ℝ)^512 := by
      have hnat : (369 : ℕ)^2197*100000000000000000000^512 ≤ 27197975419972477^512*2500^2197 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        369 2500 27197975419972477 100000000000000000000 2197 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (369/2500 : ℝ)) (X := (27197975419972477/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008819926848085913/50000000000000000000 : ℝ) ≤ (10000411060273747/10000000000000000 : ℝ) ^ (2197/512 : ℝ) := by
    have hpowers : (50008819926848085913/50000000000000000000 : ℝ)^512 ≤ (10000411060273747/10000000000000000 : ℝ)^2197 := by
      have hnat : (50008819926848085913 : ℕ)^512*10000000000000000^2197 ≤ 10000411060273747^2197*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008819926848085913 50000000000000000000 10000411060273747 10000000000000000 512 2197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000411060273747/10000000000000000 : ℝ)) (X := (50008819926848085913/50000000000000000000 : ℝ)) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003601790226805839/10000000000000000000 : ℝ) ≤ (625052453969611/625000000000000 : ℝ) ^ (2197/512 : ℝ) := by
    have hpowers : (10003601790226805839/10000000000000000000 : ℝ)^512 ≤ (625052453969611/625000000000000 : ℝ)^2197 := by
      have hnat : (10003601790226805839 : ℕ)^512*625000000000000^2197 ≤ 625052453969611^2197*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003601790226805839 10000000000000000000 625052453969611 625000000000000 512 2197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625052453969611/625000000000000 : ℝ)) (X := (10003601790226805839/10000000000000000000 : ℝ)) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027197975419972477/50000000000000000000 : ℝ) ≤ (2000253493350761/2000000000000000 : ℝ) ^ (2197/512 : ℝ) := by
    have hpowers : (50027197975419972477/50000000000000000000 : ℝ)^512 ≤ (2000253493350761/2000000000000000 : ℝ)^2197 := by
      have hnat : (50027197975419972477 : ℕ)^512*2000000000000000^2197 ≤ 2000253493350761^2197*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027197975419972477 50000000000000000000 2000253493350761 2000000000000000 512 2197 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000253493350761/2000000000000000 : ℝ)) (X := (50027197975419972477/50000000000000000000 : ℝ)) (by norm_num) 2197 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8819926848085913/100000000000000000000 : ℝ) ≤ ((6812335539916911511/6814000000000000000 : ℝ)+2*(428203240029/340700000000000 : ℝ)*(11353/100000 : ℝ))^(2197/512 : ℝ) := by
    rw [show (6812335539916911511/6814000000000000000 : ℝ)+2*(428203240029/340700000000000 : ℝ)*(11353/100000 : ℝ)=(10000411060273747/10000000000000000 : ℝ) by norm_num, show 1+2*(8819926848085913/100000000000000000000 : ℝ)=(50008819926848085913/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27197975419972477/100000000000000000000 : ℝ)+(8819926848085913/100000000000000000000 : ℝ) ≤ ((6812335539916911511/6814000000000000000 : ℝ)+(428203240029/340700000000000 : ℝ)*((369/2500 : ℝ)+(11353/100000 : ℝ)))^(2197/512 : ℝ) := by
    rw [show (6812335539916911511/6814000000000000000 : ℝ)+(428203240029/340700000000000 : ℝ)*((369/2500 : ℝ)+(11353/100000 : ℝ))=(625052453969611/625000000000000 : ℝ) by norm_num, show 1+(27197975419972477/100000000000000000000 : ℝ)+(8819926848085913/100000000000000000000 : ℝ)=(10003601790226805839/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27197975419972477/100000000000000000000 : ℝ) ≤ ((6812335539916911511/6814000000000000000 : ℝ)+2*(428203240029/340700000000000 : ℝ)*(369/2500 : ℝ))^(2197/512 : ℝ) := by
    rw [show (6812335539916911511/6814000000000000000 : ℝ)+2*(428203240029/340700000000000 : ℝ)*(369/2500 : ℝ)=(2000253493350761/2000000000000000 : ℝ) by norm_num, show 1+2*(27197975419972477/100000000000000000000 : ℝ)=(50027197975419972477/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6812335539916911511/6814000000000000000 : ℝ)*(X 1 0+X 2 0)+(428203240029/340700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2197/512 : ℝ)) (lo := (11353/100000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (6812335539916911511/6814000000000000000 : ℝ)) (alpha := (428203240029/340700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6812335539916911511/6814000000000000000 : ℝ)*(X 0 1+X 2 1)+(428203240029/340700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2197/512 : ℝ)) (lo := (11353/100000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (6812335539916911511/6814000000000000000 : ℝ)) (alpha := (428203240029/340700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6812335539916911511/6814000000000000000 : ℝ)*(X 0 2+X 1 2)+(428203240029/340700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2197/512 : ℝ)) (lo := (11353/100000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (6812335539916911511/6814000000000000000 : ℝ)) (alpha := (428203240029/340700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-903022101/5000000000 : ℝ)*X 0 0+(538599959/1000000000 : ℝ)*X 0 1+(1346500101/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66076333/125000000 : ℝ)*X 1 0+(-971653979/5000000000 : ℝ)*X 1 1+(5385999907/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5286106631/10000000000 : ℝ)*X 2 0+(2692999919/5000000000 : ℝ)*X 2 1+(-60728377/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1112263691/2500000000 : ℝ)*X 0 0+(4233484489/10000000000 : ℝ)*X 0 1+(330741/781250 : ℝ)*X 0 2+(1112263691/2500000000 : ℝ)*X 1 0+(4233484489/10000000000 : ℝ)*X 1 1+(330741/781250 : ℝ)*X 1 2+(1112263691/2500000000 : ℝ)*X 2 0+(4233484489/10000000000 : ℝ)*X 2 1+(330741/781250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2129235073/10000000000 : ℝ)*X 0 0+(5266613743/10000000000 : ℝ)*X 0 1+(5266613887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5369638537/10000000000 : ℝ)*X 1 0+(-1991817431/10000000000 : ℝ)*X 1 1+(1316653451/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2684819179/5000000000 : ℝ)*X 2 0+(5266613809/10000000000 : ℝ)*X 2 1+(-995908833/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4155641847/10000000000 : ℝ)*X 0 0+(2190070093/5000000000 : ℝ)*X 0 1+(1095035143/2500000000 : ℝ)*X 0 2+(4155641847/10000000000 : ℝ)*X 1 0+(2190070093/5000000000 : ℝ)*X 1 1+(1095035143/2500000000 : ℝ)*X 1 2+(4155641847/10000000000 : ℝ)*X 2 0+(2190070093/5000000000 : ℝ)*X 2 1+(1095035143/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2061148681/10000000000 : ℝ)*X 0 0+(5184007841/10000000000 : ℝ)*X 0 1+(337498171/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276328127/10000000000 : ℝ)*X 1 0+(-484376357/2500000000 : ℝ)*X 1 1+(2699985041/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1319082019/2500000000 : ℝ)*X 2 0+(5399969623/10000000000 : ℝ)*X 2 1+(-484376531/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4482832783/10000000000 : ℝ)*X 0 0+(1054076997/2500000000 : ℝ)*X 0 1+(1054077287/2500000000 : ℝ)*X 0 2+(4482832783/10000000000 : ℝ)*X 1 0+(1054076997/2500000000 : ℝ)*X 1 1+(1054077287/2500000000 : ℝ)*X 1 2+(4482832783/10000000000 : ℝ)*X 2 0+(1054076997/2500000000 : ℝ)*X 2 1+(1054077287/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-374860301/2000000000 : ℝ)*X 0 0+(68332421/125000000 : ℝ)*X 0 1+(5255484089/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2688711447/5000000000 : ℝ)*X 1 0+(-199624009/1000000000 : ℝ)*X 1 1+(5255485489/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5377423763/10000000000 : ℝ)*X 2 0+(41058473/78125000 : ℝ)*X 2 1+(-249530023/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1031960127/2500000000 : ℝ)*X 0 0+(878760087/2000000000 : ℝ)*X 0 1+(4393800087/10000000000 : ℝ)*X 0 2+(1031960127/2500000000 : ℝ)*X 1 0+(878760087/2000000000 : ℝ)*X 1 1+(4393800087/10000000000 : ℝ)*X 1 2+(1031960127/2500000000 : ℝ)*X 2 0+(878760087/2000000000 : ℝ)*X 2 1+(4393800087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1435_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62903/100000 : ℝ) ≤ (-214302578736541883323436192405973/340700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45656929/100000000000000 : ℝ)*(upper1) + (161879331/100000000000000 : ℝ)*(lower4) + (72237759/100000000000000 : ℝ)*(upper5) + (3023324205686319/100000000000000 : ℝ)*(major0) + (3023324205686319/100000000000000 : ℝ)*(major1) + (3023324205686319/100000000000000 : ℝ)*(major2) + (4614802129/50000000000000 : ℝ)*(sp2) + (2127727303/50000000000000 : ℝ)*(sp3) + (1039750657974587/25000000000000 : ℝ)*(sp4) + (415899262349719/10000000000000 : ℝ)*(sp5) + (519874584079397/12500000000000 : ℝ)*(sp6) + (477151285822949/25000000000000 : ℝ)*(sp7) + (654068217/20000000000000 : ℝ)*(sp12) + (3319685561/25000000000000 : ℝ)*(sp13) + (954304699373201/50000000000000 : ℝ)*(f.failure) + (4159005902239433/100000000000000 : ℝ)*(f.sum) + (33729096800547/8517500000000000000000000000 : ℝ)*base66 + (265040551435738009/681400000000000000000000000000000 : ℝ)*base67 + (461217100122861991/681400000000000000000000000000000 : ℝ)*base70 + (25381536144538009/681400000000000000000000000000000 : ℝ)*base71 + (44788044100649/17035000000000000000000000000 : ℝ)*base74 + (10377531021891861991/681400000000000000000000000000000 : ℝ)*base76 + (86075497951461991/681400000000000000000000000000000 : ℝ)*base78 + (1282906883597861991/681400000000000000000000000000000 : ℝ)*base80 + (41345966378189/17035000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (16978677/2500000000000000000000 : ℝ)*base89 + (16978677/2500000000000000000000 : ℝ)*base91 + (16978677/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (473/800 : ℝ) ≤ (50362025063314645247138036672019/85175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63495601/100000000000000 : ℝ)*(lower1) + (27074473/100000000000000 : ℝ)*(lower4) + (6725417/20000000000000 : ℝ)*(lower5) + (773784276659581/25000000000000 : ℝ)*(major0) + (773784276659581/25000000000000 : ℝ)*(major1) + (773784276659581/25000000000000 : ℝ)*(major2) + (843319879679127/20000000000000 : ℝ)*(sp0) + (2108310153747859/50000000000000 : ℝ)*(sp1) + (84331958096919/2000000000000 : ℝ)*(sp2) + (976972085539197/50000000000000 : ℝ)*(sp3) + (29427793/20000000000000 : ℝ)*(sp5) + (87912971/25000000000000 : ℝ)*(sp7) + (5637447183/25000000000000 : ℝ)*(sp10) + (2632029881/12500000000000 : ℝ)*(sp12) + (976972261365139/50000000000000 : ℝ)*(f.failure) + (2108310227317341/50000000000000 : ℝ)*(f.sum) + (36353875355247/8517500000000000000000000000 : ℝ)*base66 + (1865104002378683109/170350000000000000000000000000000 : ℝ)*base68 + (1628819230826683109/170350000000000000000000000000000 : ℝ)*base70 + (1985724256496833109/170350000000000000000000000000000 : ℝ)*base72 + (44029073997189/17035000000000000000000000000 : ℝ)*base74 + (2432841806952583109/170350000000000000000000000000000 : ℝ)*base76 + (1031572162511783109/170350000000000000000000000000000 : ℝ)*base78 + (646903529444783109/170350000000000000000000000000000 : ℝ)*base80 + (17739053113351/4258750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (37221503/2500000000000000000000 : ℝ)*base89 + (37221503/2500000000000000000000 : ℝ)*base91 + (37221503/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40241/50000 : ℝ) ≤ (137104480060036431037874614097181/170350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (226562689/50000000000000 : ℝ)*(upper0) + (15374721/20000000000000 : ℝ)*(upper2) + (494624357/100000000000000 : ℝ)*(lower5) + (3402674510503657/100000000000000 : ℝ)*(major0) + (3402674510503657/100000000000000 : ℝ)*(major1) + (3402674510503657/100000000000000 : ℝ)*(major2) + (54464737307/100000000000000 : ℝ)*(sp1) + (35281452091/100000000000000 : ℝ)*(sp3) + (11716124503/100000000000000 : ℝ)*(sp4) + (2315201276830327/50000000000000 : ℝ)*(sp8) + (2315187608279179/50000000000000 : ℝ)*(sp9) + (926085936259133/20000000000000 : ℝ)*(sp10) + (1074028030493627/50000000000000 : ℝ)*(sp11) + (15411510509/100000000000000 : ℝ)*(sp12) + (134255708902459/6250000000000 : ℝ)*(f.failure) + (926085936259133/20000000000000 : ℝ)*(f.sum) + (203871976900673/17035000000000000000000000000 : ℝ)*base65 + (6261455015527644273/681400000000000000000000000000000 : ℝ)*base68 + (7160279455485244273/681400000000000000000000000000000 : ℝ)*base70 + (5837553375820844273/681400000000000000000000000000000 : ℝ)*base72 + (74036978074909/8517500000000000000000000000 : ℝ)*base73 + (4698578860803844273/681400000000000000000000000000000 : ℝ)*base76 + (2059760430972444273/681400000000000000000000000000000 : ℝ)*base78 + (1410721654907555727/681400000000000000000000000000000 : ℝ)*base79 + (24382500704433/17035000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4425857/312500000000000000000 : ℝ)*base90 + (4425857/312500000000000000000 : ℝ)*base92 + (4425857/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-84707/100000 : ℝ) ≤ (-144294579514742061384273794986503/170350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83280653/50000000000000 : ℝ)*(lower2) + (160491437/100000000000000 : ℝ)*(upper3) + (179612749/100000000000000 : ℝ)*(upper5) + (1720124959752697/50000000000000 : ℝ)*(major0) + (1720124959752697/50000000000000 : ℝ)*(major1) + (1720124959752697/50000000000000 : ℝ)*(major2) + (2844207151/12500000000000 : ℝ)*(sp0) + (78697652251/25000000000000 : ℝ)*(sp6) + (146362729853/100000000000000 : ℝ)*(sp7) + (2847395723/20000000000000 : ℝ)*(sp8) + (1184221315720669/25000000000000 : ℝ)*(sp12) + (4736922253518499/100000000000000 : ℝ)*(sp13) + (947321492581899/20000000000000 : ℝ)*(sp14) + (434333229368639/20000000000000 : ℝ)*(sp15) + (271476563696631/12500000000000 : ℝ)*(f.failure) + (4736922253518499/100000000000000 : ℝ)*(f.sum) + (2995427804763/8517500000000000000000000000 : ℝ)*base65 + (1043728630868255167/340700000000000000000000000000000 : ℝ)*base67 + (1141644577874955167/340700000000000000000000000000000 : ℝ)*base69 + (2012167509016955167/340700000000000000000000000000000 : ℝ)*base71 + (32087994660371/17035000000000000000000000000 : ℝ)*base73 + (4592085131052455167/340700000000000000000000000000000 : ℝ)*base75 + (3029228892969255167/340700000000000000000000000000000 : ℝ)*base77 + (1919828834297555167/340700000000000000000000000000000 : ℝ)*base79 + (38344872412631/17035000000000000000000000000 : ℝ)*base81 + (71213/625000000000000000000 : ℝ)*base90 + (71213/625000000000000000000 : ℝ)*base92 + (71213/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1435_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79202277/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11353/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62903/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(473/800 : ℝ) else (40241/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84707/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1435_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1435_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79202277/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62903/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(473/800 : ℝ) else (40241/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84707/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1435_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1435_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1435_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2197/512 : ℝ) ≤ p) (hpb : p ≤ (4395/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (79202277/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11349/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62903/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(473/800 : ℝ) else (40241/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84707/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1435_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

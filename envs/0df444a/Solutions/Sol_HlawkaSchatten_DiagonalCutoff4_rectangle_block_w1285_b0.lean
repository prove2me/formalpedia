-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1285_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:24:21.541434+00:00
-- url     : https://prove2.me/submissions/d2172ab5-50a7-4bf7-b490-30799ab33dd1

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
theorem support_rectangle_w1285_s0_0 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-368665661/2000000000 : ℝ)*x 0 + (6021900907/10000000000 : ℝ)*x 1 + (2398564301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (368665661/2000000000 : ℝ)^4245 ≤ (336494332891/3125000000000 : ℝ)^3221 := by
    have hnat : (368665661 : ℕ)^4245*3125000000000^3221 ≤ 336494332891^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368665661 2000000000 336494332891 3125000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6021900907/10000000000 : ℝ)^4245 ≤ (51251655930409/100000000000000 : ℝ)^3221 := by
    have hnat : (6021900907 : ℕ)^4245*100000000000000^3221 ≤ 51251655930409^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6021900907 10000000000 51251655930409 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2398564301/5000000000 : ℝ)^4245 ≤ (37980525395893/100000000000000 : ℝ)^3221 := by
    have hnat : (2398564301 : ℕ)^4245*100000000000000^3221 ≤ 37980525395893^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2398564301 5000000000 37980525395893 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-368665661/2000000000 : ℝ), (6021900907/10000000000 : ℝ), (2398564301/5000000000 : ℝ)] ![(336494332891/3125000000000 : ℝ), (51251655930409/100000000000000 : ℝ), (37980525395893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-368665661/2000000000 : ℝ)|^4245 ≤ (336494332891/3125000000000 : ℝ)^3221
        have hw : |(-368665661/2000000000 : ℝ)|=(368665661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6021900907/10000000000 : ℝ)|^4245 ≤ (51251655930409/100000000000000 : ℝ)^3221
        have hw : |(6021900907/10000000000 : ℝ)|=(6021900907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2398564301/5000000000 : ℝ)|^4245 ≤ (37980525395893/100000000000000 : ℝ)^3221
        have hw : |(2398564301/5000000000 : ℝ)|=(2398564301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s0_1 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1377051053/2500000000 : ℝ)*x 0 + (-2542419451/10000000000 : ℝ)*x 1 + (2398564281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1377051053/2500000000 : ℝ)^4245 ≤ (45569427926569/100000000000000 : ℝ)^3221 := by
    have hnat : (1377051053 : ℕ)^4245*100000000000000^3221 ≤ 45569427926569^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377051053 2500000000 45569427926569 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2542419451/10000000000 : ℝ)^4245 ≤ (329000941537/2000000000000 : ℝ)^3221 := by
    have hnat : (2542419451 : ℕ)^4245*2000000000000^3221 ≤ 329000941537^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542419451 10000000000 329000941537 2000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2398564281/5000000000 : ℝ)^4245 ≤ (18990262489259/50000000000000 : ℝ)^3221 := by
    have hnat : (2398564281 : ℕ)^4245*50000000000000^3221 ≤ 18990262489259^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2398564281 5000000000 18990262489259 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1377051053/2500000000 : ℝ), (-2542419451/10000000000 : ℝ), (2398564281/5000000000 : ℝ)] ![(45569427926569/100000000000000 : ℝ), (329000941537/2000000000000 : ℝ), (18990262489259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1377051053/2500000000 : ℝ)|^4245 ≤ (45569427926569/100000000000000 : ℝ)^3221
        have hw : |(1377051053/2500000000 : ℝ)|=(1377051053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2542419451/10000000000 : ℝ)|^4245 ≤ (329000941537/2000000000000 : ℝ)^3221
        have hw : |(-2542419451/10000000000 : ℝ)|=(2542419451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2398564281/5000000000 : ℝ)|^4245 ≤ (18990262489259/50000000000000 : ℝ)^3221
        have hw : |(2398564281/5000000000 : ℝ)|=(2398564281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s0_2 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5508204227/10000000000 : ℝ)*x 0 + (4797128579/10000000000 : ℝ)*x 1 + (-2542419411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5508204227/10000000000 : ℝ)^4245 ≤ (11392357022529/25000000000000 : ℝ)^3221 := by
    have hnat : (5508204227 : ℕ)^4245*25000000000000^3221 ≤ 11392357022529^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508204227 10000000000 11392357022529 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4797128579/10000000000 : ℝ)^4245 ≤ (18990262577951/50000000000000 : ℝ)^3221 := by
    have hnat : (4797128579 : ℕ)^4245*50000000000000^3221 ≤ 18990262577951^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4797128579 10000000000 18990262577951 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2542419411/10000000000 : ℝ)^4245 ≤ (16450046735761/100000000000000 : ℝ)^3221 := by
    have hnat : (2542419411 : ℕ)^4245*100000000000000^3221 ≤ 16450046735761^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542419411 10000000000 16450046735761 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5508204227/10000000000 : ℝ), (4797128579/10000000000 : ℝ), (-2542419411/10000000000 : ℝ)] ![(11392357022529/25000000000000 : ℝ), (18990262577951/50000000000000 : ℝ), (16450046735761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5508204227/10000000000 : ℝ)|^4245 ≤ (11392357022529/25000000000000 : ℝ)^3221
        have hw : |(5508204227/10000000000 : ℝ)|=(5508204227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4797128579/10000000000 : ℝ)|^4245 ≤ (18990262577951/50000000000000 : ℝ)^3221
        have hw : |(4797128579/10000000000 : ℝ)|=(4797128579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2542419411/10000000000 : ℝ)|^4245 ≤ (16450046735761/100000000000000 : ℝ)^3221
        have hw : |(-2542419411/10000000000 : ℝ)|=(2542419411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s0_3 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2093704907/5000000000 : ℝ)*x 0 + (1554949649/5000000000 : ℝ)*x 1 + (2810182727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093704907/5000000000 : ℝ)^4245 ≤ (15875476104547/50000000000000 : ℝ)^3221 := by
    have hnat : (2093704907 : ℕ)^4245*50000000000000^3221 ≤ 15875476104547^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093704907 5000000000 15875476104547 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1554949649/5000000000 : ℝ)^4245 ≤ (268159663173/1250000000000 : ℝ)^3221 := by
    have hnat : (1554949649 : ℕ)^4245*1250000000000^3221 ≤ 268159663173^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1554949649 5000000000 268159663173 1250000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2810182727/5000000000 : ℝ)^4245 ≤ (46796274721781/100000000000000 : ℝ)^3221 := by
    have hnat : (2810182727 : ℕ)^4245*100000000000000^3221 ≤ 46796274721781^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2810182727 5000000000 46796274721781 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2093704907/5000000000 : ℝ), (1554949649/5000000000 : ℝ), (2810182727/5000000000 : ℝ)] ![(15875476104547/50000000000000 : ℝ), (268159663173/1250000000000 : ℝ), (46796274721781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2093704907/5000000000 : ℝ)|^4245 ≤ (15875476104547/50000000000000 : ℝ)^3221
        have hw : |(2093704907/5000000000 : ℝ)|=(2093704907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1554949649/5000000000 : ℝ)|^4245 ≤ (268159663173/1250000000000 : ℝ)^3221
        have hw : |(1554949649/5000000000 : ℝ)|=(1554949649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2810182727/5000000000 : ℝ)|^4245 ≤ (46796274721781/100000000000000 : ℝ)^3221
        have hw : |(2810182727/5000000000 : ℝ)|=(2810182727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s0_4 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-369618141/2000000000 : ℝ)*x 0 + (150898429/312500000 : ℝ)*x 1 + (2994577903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (369618141/2000000000 : ℝ)^4245 ≤ (10804497534927/100000000000000 : ℝ)^3221 := by
    have hnat : (369618141 : ℕ)^4245*100000000000000^3221 ≤ 10804497534927^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369618141 2000000000 10804497534927 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (150898429/312500000 : ℝ)^4245 ≤ (19155408692401/50000000000000 : ℝ)^3221 := by
    have hnat : (150898429 : ℕ)^4245*50000000000000^3221 ≤ 19155408692401^3221*312500000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150898429 312500000 19155408692401 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2994577903/5000000000 : ℝ)^4245 ≤ (2544234253129/5000000000000 : ℝ)^3221 := by
    have hnat : (2994577903 : ℕ)^4245*5000000000000^3221 ≤ 2544234253129^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2994577903 5000000000 2544234253129 5000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-369618141/2000000000 : ℝ), (150898429/312500000 : ℝ), (2994577903/5000000000 : ℝ)] ![(10804497534927/100000000000000 : ℝ), (19155408692401/50000000000000 : ℝ), (2544234253129/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-369618141/2000000000 : ℝ)|^4245 ≤ (10804497534927/100000000000000 : ℝ)^3221
        have hw : |(-369618141/2000000000 : ℝ)|=(369618141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(150898429/312500000 : ℝ)|^4245 ≤ (19155408692401/50000000000000 : ℝ)^3221
        have hw : |(150898429/312500000 : ℝ)|=(150898429/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2994577903/5000000000 : ℝ)|^4245 ≤ (2544234253129/5000000000000 : ℝ)^3221
        have hw : |(2994577903/5000000000 : ℝ)|=(2994577903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s0_5 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5174822241/10000000000 : ℝ)*x 0 + (-168798713/1250000000 : ℝ)*x 1 + (5989158369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174822241/10000000000 : ℝ)^4245 ≤ (41969991184701/100000000000000 : ℝ)^3221 := by
    have hnat : (5174822241 : ℕ)^4245*100000000000000^3221 ≤ 41969991184701^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174822241 10000000000 41969991184701 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168798713/1250000000 : ℝ)^4245 ≤ (714529504411/10000000000000 : ℝ)^3221 := by
    have hnat : (168798713 : ℕ)^4245*10000000000000^3221 ≤ 714529504411^3221*1250000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168798713 1250000000 714529504411 10000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5989158369/10000000000 : ℝ)^4245 ≤ (2544235688047/5000000000000 : ℝ)^3221 := by
    have hnat : (5989158369 : ℕ)^4245*5000000000000^3221 ≤ 2544235688047^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5989158369 10000000000 2544235688047 5000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174822241/10000000000 : ℝ), (-168798713/1250000000 : ℝ), (5989158369/10000000000 : ℝ)] ![(41969991184701/100000000000000 : ℝ), (714529504411/10000000000000 : ℝ), (2544235688047/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174822241/10000000000 : ℝ)|^4245 ≤ (41969991184701/100000000000000 : ℝ)^3221
        have hw : |(5174822241/10000000000 : ℝ)|=(5174822241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-168798713/1250000000 : ℝ)|^4245 ≤ (714529504411/10000000000000 : ℝ)^3221
        have hw : |(-168798713/1250000000 : ℝ)|=(168798713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5989158369/10000000000 : ℝ)|^4245 ≤ (2544235688047/5000000000000 : ℝ)^3221
        have hw : |(5989158369/10000000000 : ℝ)|=(5989158369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s0_6 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2587411743/5000000000 : ℝ)*x 0 + (5989156221/10000000000 : ℝ)*x 1 + (-337597811/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587411743/5000000000 : ℝ)^4245 ≤ (20985002246151/50000000000000 : ℝ)^3221 := by
    have hnat : (2587411743 : ℕ)^4245*50000000000000^3221 ≤ 20985002246151^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587411743 5000000000 20985002246151 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5989156221/10000000000 : ℝ)^4245 ≤ (1590146553419/3125000000000 : ℝ)^3221 := by
    have hnat : (5989156221 : ℕ)^4245*3125000000000^3221 ≤ 1590146553419^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5989156221 10000000000 1590146553419 3125000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337597811/2500000000 : ℝ)^4245 ≤ (7145305783233/100000000000000 : ℝ)^3221 := by
    have hnat : (337597811 : ℕ)^4245*100000000000000^3221 ≤ 7145305783233^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337597811 2500000000 7145305783233 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587411743/5000000000 : ℝ), (5989156221/10000000000 : ℝ), (-337597811/2500000000 : ℝ)] ![(20985002246151/50000000000000 : ℝ), (1590146553419/3125000000000 : ℝ), (7145305783233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587411743/5000000000 : ℝ)|^4245 ≤ (20985002246151/50000000000000 : ℝ)^3221
        have hw : |(2587411743/5000000000 : ℝ)|=(2587411743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5989156221/10000000000 : ℝ)|^4245 ≤ (1590146553419/3125000000000 : ℝ)^3221
        have hw : |(5989156221/10000000000 : ℝ)|=(5989156221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-337597811/2500000000 : ℝ)|^4245 ≤ (7145305783233/100000000000000 : ℝ)^3221
        have hw : |(-337597811/2500000000 : ℝ)|=(337597811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s0_7 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4197175939/10000000000 : ℝ)*x 0 + (2777778659/5000000000 : ℝ)*x 1 + (397126431/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4197175939/10000000000 : ℝ)^4245 ≤ (6369716358063/20000000000000 : ℝ)^3221 := by
    have hnat : (4197175939 : ℕ)^4245*20000000000000^3221 ≤ 6369716358063^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4197175939 10000000000 6369716358063 20000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2777778659/5000000000 : ℝ)^4245 ≤ (46086428350227/100000000000000 : ℝ)^3221 := by
    have hnat : (2777778659 : ℕ)^4245*100000000000000^3221 ≤ 46086428350227^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2777778659 5000000000 46086428350227 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397126431/1250000000 : ℝ)^4245 ≤ (5516247459717/25000000000000 : ℝ)^3221 := by
    have hnat : (397126431 : ℕ)^4245*25000000000000^3221 ≤ 5516247459717^3221*1250000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397126431 1250000000 5516247459717 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4197175939/10000000000 : ℝ), (2777778659/5000000000 : ℝ), (397126431/1250000000 : ℝ)] ![(6369716358063/20000000000000 : ℝ), (46086428350227/100000000000000 : ℝ), (5516247459717/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4197175939/10000000000 : ℝ)|^4245 ≤ (6369716358063/20000000000000 : ℝ)^3221
        have hw : |(4197175939/10000000000 : ℝ)|=(4197175939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2777778659/5000000000 : ℝ)|^4245 ≤ (46086428350227/100000000000000 : ℝ)^3221
        have hw : |(2777778659/5000000000 : ℝ)|=(2777778659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(397126431/1250000000 : ℝ)|^4245 ≤ (5516247459717/25000000000000 : ℝ)^3221
        have hw : |(397126431/1250000000 : ℝ)|=(397126431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1285_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (489/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27287/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1061/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1061 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1061*1^256 ≤ 0^256*1^1061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1061 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1061/256 : ℝ) ≤ (1121231273823157489/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1061 ≤ (1121231273823157489/50000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1061*50000000000000000000^256 ≤ 1121231273823157489^256*5^1061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1121231273823157489 50000000000000000000 1061 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1121231273823157489/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1061 := by
      have hnat : (1 : ℕ)^256*1^1061 ≤ 1^1061*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (51121231273823157489/50000000000000000000 : ℝ) ≤ (2010730443503661/2000000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (51121231273823157489/50000000000000000000 : ℝ)^256 ≤ (2010730443503661/2000000000000000 : ℝ)^1061 := by
      have hnat : (51121231273823157489 : ℕ)^256*2000000000000000^1061 ≤ 2010730443503661^1061*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51121231273823157489 50000000000000000000 2010730443503661 2000000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2010730443503661/2000000000000000 : ℝ)) (X := (51121231273823157489/50000000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (26121231273823157489/25000000000000000000 : ℝ) ≤ (1010730443503661/1000000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (26121231273823157489/25000000000000000000 : ℝ)^256 ≤ (1010730443503661/1000000000000000 : ℝ)^1061 := by
      have hnat : (26121231273823157489 : ℕ)^256*1000000000000000^1061 ≤ 1010730443503661^1061*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26121231273823157489 25000000000000000000 1010730443503661 1000000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1010730443503661/1000000000000000 : ℝ)) (X := (26121231273823157489/25000000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(10730443503661/800000000000000 : ℝ)*(0 : ℝ))^(1061/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(10730443503661/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1121231273823157489/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(10730443503661/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1061/256 : ℝ) := by
    rw [show (1 : ℝ)+(10730443503661/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2010730443503661/2000000000000000 : ℝ) by norm_num, show 1+(1121231273823157489/50000000000000000000 : ℝ)+(0 : ℝ)=(51121231273823157489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1121231273823157489/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(10730443503661/800000000000000 : ℝ)*(2/5 : ℝ))^(1061/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(10730443503661/800000000000000 : ℝ)*(2/5 : ℝ)=(1010730443503661/1000000000000000 : ℝ) by norm_num, show 1+2*(1121231273823157489/50000000000000000000 : ℝ)=(26121231273823157489/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(10730443503661/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10730443503661/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(10730443503661/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10730443503661/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(10730443503661/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10730443503661/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-368665661/2000000000 : ℝ)*X 0 0+(6021900907/10000000000 : ℝ)*X 0 1+(2398564301/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1377051053/2500000000 : ℝ)*X 1 0+(-2542419451/10000000000 : ℝ)*X 1 1+(2398564281/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5508204227/10000000000 : ℝ)*X 2 0+(4797128579/10000000000 : ℝ)*X 2 1+(-2542419411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2093704907/5000000000 : ℝ)*X 0 0+(1554949649/5000000000 : ℝ)*X 0 1+(2810182727/5000000000 : ℝ)*X 0 2+(2093704907/5000000000 : ℝ)*X 1 0+(1554949649/5000000000 : ℝ)*X 1 1+(2810182727/5000000000 : ℝ)*X 1 2+(2093704907/5000000000 : ℝ)*X 2 0+(1554949649/5000000000 : ℝ)*X 2 1+(2810182727/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-369618141/2000000000 : ℝ)*X 0 0+(150898429/312500000 : ℝ)*X 0 1+(2994577903/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5174822241/10000000000 : ℝ)*X 1 0+(-168798713/1250000000 : ℝ)*X 1 1+(5989158369/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2587411743/5000000000 : ℝ)*X 2 0+(5989156221/10000000000 : ℝ)*X 2 1+(-337597811/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4197175939/10000000000 : ℝ)*X 0 0+(2777778659/5000000000 : ℝ)*X 0 1+(397126431/1250000000 : ℝ)*X 0 2+(4197175939/10000000000 : ℝ)*X 1 0+(2777778659/5000000000 : ℝ)*X 1 1+(397126431/1250000000 : ℝ)*X 1 2+(4197175939/10000000000 : ℝ)*X 2 0+(2777778659/5000000000 : ℝ)*X 2 1+(397126431/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (131215676969755150080717/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43848853/100000000000000 : ℝ)*(base1) + (20068041/2500000000000 : ℝ)*(base19) + (402472547/50000000000000 : ℝ)*(base23) + (8839833/10000000000000 : ℝ)*(upper3) + (12378141/12500000000000 : ℝ)*(upper5) + (607409030789899/100000000000000 : ℝ)*(major0) + (607409030789899/100000000000000 : ℝ)*(major1) + (607409030789899/100000000000000 : ℝ)*(major2) + (40824032502641/5000000000000 : ℝ)*(sp0) + (816482361701029/100000000000000 : ℝ)*(sp1) + (102060294934697/12500000000000 : ℝ)*(sp2) + (398333552408357/100000000000000 : ℝ)*(sp3) + (1279109351/50000000000000 : ℝ)*(sp4) + (238310703/20000000000000 : ℝ)*(sp7) + (99583696952681/25000000000000 : ℝ)*(f.failure) + (81648316442267/10000000000000 : ℝ)*(f.sum) + (34022318599761/40000000000000000000000000000 : ℝ)*base66 + (216577772160239/80000000000000000000000000000 : ℝ)*base67 + (462122491679761/80000000000000000000000000000 : ℝ)*base70 + (12145901840239/80000000000000000000000000000 : ℝ)*base71 + (11484285240239/40000000000000000000000000000 : ℝ)*base73 + (66929600640239/80000000000000000000000000000 : ℝ)*base75 + (164844466479761/80000000000000000000000000000 : ℝ)*base78 + (66328124479761/80000000000000000000000000000 : ℝ)*base80 + (192016514159761/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (4238027/1250000000000000000000 : ℝ)*base90 + (4238027/1250000000000000000000 : ℝ)*base92 + (4238027/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (100385605922606912737533/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (370053911/100000000000000 : ℝ)*(base1) + (112716293/12500000000000 : ℝ)*(base19) + (537811487/50000000000000 : ℝ)*(base23) + (168087941/100000000000000 : ℝ)*(upper3) + (320548214282149/50000000000000 : ℝ)*(major0) + (320548214282149/50000000000000 : ℝ)*(major1) + (320548214282149/50000000000000 : ℝ)*(major2) + (101099283/6250000000000 : ℝ)*(sp1) + (68660433/6250000000000 : ℝ)*(sp2) + (458654271/100000000000000 : ℝ)*(sp3) + (26930196921011/3125000000000 : ℝ)*(sp4) + (861763412099569/100000000000000 : ℝ)*(sp5) + (43088187861427/5000000000000 : ℝ)*(sp6) + (26276620605789/6250000000000 : ℝ)*(sp7) + (210213379200403/50000000000000 : ℝ)*(f.failure) + (861765931418441/100000000000000 : ℝ)*(f.sum) + (3910458952511/20000000000000000000000000000 : ℝ)*base66 + (104677790607489/40000000000000000000000000000 : ℝ)*base67 + (301659996527489/40000000000000000000000000000 : ℝ)*base69 + (255228224647489/40000000000000000000000000000 : ℝ)*base71 + (17271001272511/20000000000000000000000000000 : ℝ)*base74 + (84031837127489/40000000000000000000000000000 : ℝ)*base75 + (9896183407489/40000000000000000000000000000 : ℝ)*base77 + (79052705232511/40000000000000000000000000000 : ℝ)*base80 + (110428160087489/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (10256201/2500000000000000000000 : ℝ)*base90 + (10256201/2500000000000000000000 : ℝ)*base92 + (10256201/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1285_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (489/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27287/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1285_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1285_s1_0 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2036385913/10000000000 : ℝ)*x 0 + (283433847/500000000 : ℝ)*x 1 + (2513378821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2036385913/10000000000 : ℝ)^4245 ≤ (12278271776047/100000000000000 : ℝ)^3221 := by
    have hnat : (2036385913 : ℕ)^4245*100000000000000^3221 ≤ 12278271776047^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036385913 10000000000 12278271776047 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283433847/500000000 : ℝ)^4245 ≤ (47327129750221/100000000000000 : ℝ)^3221 := by
    have hnat : (283433847 : ℕ)^4245*100000000000000^3221 ≤ 47327129750221^3221*500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283433847 500000000 47327129750221 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2513378821/5000000000 : ℝ)^4245 ≤ (40394598454627/100000000000000 : ℝ)^3221 := by
    have hnat : (2513378821 : ℕ)^4245*100000000000000^3221 ≤ 40394598454627^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2513378821 5000000000 40394598454627 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2036385913/10000000000 : ℝ), (283433847/500000000 : ℝ), (2513378821/5000000000 : ℝ)] ![(12278271776047/100000000000000 : ℝ), (47327129750221/100000000000000 : ℝ), (40394598454627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2036385913/10000000000 : ℝ)|^4245 ≤ (12278271776047/100000000000000 : ℝ)^3221
        have hw : |(-2036385913/10000000000 : ℝ)|=(2036385913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(283433847/500000000 : ℝ)|^4245 ≤ (47327129750221/100000000000000 : ℝ)^3221
        have hw : |(283433847/500000000 : ℝ)|=(283433847/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2513378821/5000000000 : ℝ)|^4245 ≤ (40394598454627/100000000000000 : ℝ)^3221
        have hw : |(2513378821/5000000000 : ℝ)|=(2513378821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s1_1 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5411730797/10000000000 : ℝ)*x 0 + (-2380665681/10000000000 : ℝ)*x 1 + (5026757509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5411730797/10000000000 : ℝ)^4245 ≤ (44520507560197/100000000000000 : ℝ)^3221 := by
    have hnat : (5411730797 : ℕ)^4245*100000000000000^3221 ≤ 44520507560197^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411730797 10000000000 44520507560197 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2380665681/10000000000 : ℝ)^4245 ≤ (754244768837/5000000000000 : ℝ)^3221 := by
    have hnat : (2380665681 : ℕ)^4245*5000000000000^3221 ≤ 754244768837^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2380665681 10000000000 754244768837 5000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5026757509/10000000000 : ℝ)^4245 ≤ (40394597046071/100000000000000 : ℝ)^3221 := by
    have hnat : (5026757509 : ℕ)^4245*100000000000000^3221 ≤ 40394597046071^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5026757509 10000000000 40394597046071 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5411730797/10000000000 : ℝ), (-2380665681/10000000000 : ℝ), (5026757509/10000000000 : ℝ)] ![(44520507560197/100000000000000 : ℝ), (754244768837/5000000000000 : ℝ), (40394597046071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5411730797/10000000000 : ℝ)|^4245 ≤ (44520507560197/100000000000000 : ℝ)^3221
        have hw : |(5411730797/10000000000 : ℝ)|=(5411730797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2380665681/10000000000 : ℝ)|^4245 ≤ (754244768837/5000000000000 : ℝ)^3221
        have hw : |(-2380665681/10000000000 : ℝ)|=(2380665681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5026757509/10000000000 : ℝ)|^4245 ≤ (40394597046071/100000000000000 : ℝ)^3221
        have hw : |(5026757509/10000000000 : ℝ)|=(5026757509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s1_2 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5411730591/10000000000 : ℝ)*x 0 + (2513378827/5000000000 : ℝ)*x 1 + (-595166441/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5411730591/10000000000 : ℝ)^4245 ≤ (44520505326737/100000000000000 : ℝ)^3221 := by
    have hnat : (5411730591 : ℕ)^4245*100000000000000^3221 ≤ 44520505326737^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411730591 10000000000 44520505326737 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2513378827/5000000000 : ℝ)^4245 ≤ (20197299290857/50000000000000 : ℝ)^3221 := by
    have hnat : (2513378827 : ℕ)^4245*50000000000000^3221 ≤ 20197299290857^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2513378827 5000000000 20197299290857 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (595166441/2500000000 : ℝ)^4245 ≤ (754244803493/5000000000000 : ℝ)^3221 := by
    have hnat : (595166441 : ℕ)^4245*5000000000000^3221 ≤ 754244803493^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595166441 2500000000 754244803493 5000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5411730591/10000000000 : ℝ), (2513378827/5000000000 : ℝ), (-595166441/2500000000 : ℝ)] ![(44520505326737/100000000000000 : ℝ), (20197299290857/50000000000000 : ℝ), (754244803493/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5411730591/10000000000 : ℝ)|^4245 ≤ (44520505326737/100000000000000 : ℝ)^3221
        have hw : |(5411730591/10000000000 : ℝ)|=(5411730591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2513378827/5000000000 : ℝ)|^4245 ≤ (20197299290857/50000000000000 : ℝ)^3221
        have hw : |(2513378827/5000000000 : ℝ)|=(2513378827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-595166441/2500000000 : ℝ)|^4245 ≤ (754244803493/5000000000000 : ℝ)^3221
        have hw : |(-595166441/2500000000 : ℝ)|=(595166441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s1_3 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075591203/2500000000 : ℝ)*x 0 + (1846140479/5000000000 : ℝ)*x 1 + (5008049249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075591203/2500000000 : ℝ)^4245 ≤ (32904685725419/100000000000000 : ℝ)^3221 := by
    have hnat : (1075591203 : ℕ)^4245*100000000000000^3221 ≤ 32904685725419^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075591203 2500000000 32904685725419 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1846140479/5000000000 : ℝ)^4245 ≤ (6724683096933/25000000000000 : ℝ)^3221 := by
    have hnat : (1846140479 : ℕ)^4245*25000000000000^3221 ≤ 6724683096933^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846140479 5000000000 6724683096933 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5008049249/10000000000 : ℝ)^4245 ≤ (160786327453/400000000000 : ℝ)^3221 := by
    have hnat : (5008049249 : ℕ)^4245*400000000000^3221 ≤ 160786327453^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5008049249 10000000000 160786327453 400000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075591203/2500000000 : ℝ), (1846140479/5000000000 : ℝ), (5008049249/10000000000 : ℝ)] ![(32904685725419/100000000000000 : ℝ), (6724683096933/25000000000000 : ℝ), (160786327453/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075591203/2500000000 : ℝ)|^4245 ≤ (32904685725419/100000000000000 : ℝ)^3221
        have hw : |(1075591203/2500000000 : ℝ)|=(1075591203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1846140479/5000000000 : ℝ)|^4245 ≤ (6724683096933/25000000000000 : ℝ)^3221
        have hw : |(1846140479/5000000000 : ℝ)|=(1846140479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5008049249/10000000000 : ℝ)|^4245 ≤ (160786327453/400000000000 : ℝ)^3221
        have hw : |(5008049249/10000000000 : ℝ)|=(5008049249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s1_4 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2037038333/10000000000 : ℝ)*x 0 + (5035171359/10000000000 : ℝ)*x 1 + (1132020643/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037038333/10000000000 : ℝ)^4245 ≤ (6141728177597/50000000000000 : ℝ)^3221 := by
    have hnat : (2037038333 : ℕ)^4245*50000000000000^3221 ≤ 6141728177597^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037038333 10000000000 6141728177597 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5035171359/10000000000 : ℝ)^4245 ≤ (40483728824231/100000000000000 : ℝ)^3221 := by
    have hnat : (5035171359 : ℕ)^4245*100000000000000^3221 ≤ 40483728824231^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5035171359 10000000000 40483728824231 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132020643/2000000000 : ℝ)^4245 ≤ (184503182831/390625000000 : ℝ)^3221 := by
    have hnat : (1132020643 : ℕ)^4245*390625000000^3221 ≤ 184503182831^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132020643 2000000000 184503182831 390625000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2037038333/10000000000 : ℝ), (5035171359/10000000000 : ℝ), (1132020643/2000000000 : ℝ)] ![(6141728177597/50000000000000 : ℝ), (40483728824231/100000000000000 : ℝ), (184503182831/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2037038333/10000000000 : ℝ)|^4245 ≤ (6141728177597/50000000000000 : ℝ)^3221
        have hw : |(-2037038333/10000000000 : ℝ)|=(2037038333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5035171359/10000000000 : ℝ)|^4245 ≤ (40483728824231/100000000000000 : ℝ)^3221
        have hw : |(5035171359/10000000000 : ℝ)|=(5035171359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132020643/2000000000 : ℝ)|^4245 ≤ (184503182831/390625000000 : ℝ)^3221
        have hw : |(1132020643/2000000000 : ℝ)|=(1132020643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s1_5 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2622992633/5000000000 : ℝ)*x 0 + (-218414977/1250000000 : ℝ)*x 1 + (5660103741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2622992633/5000000000 : ℝ)^4245 ≤ (5341537331337/12500000000000 : ℝ)^3221 := by
    have hnat : (2622992633 : ℕ)^4245*12500000000000^3221 ≤ 5341537331337^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622992633 5000000000 5341537331337 12500000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218414977/1250000000 : ℝ)^4245 ≤ (10034880749141/100000000000000 : ℝ)^3221 := by
    have hnat : (218414977 : ℕ)^4245*100000000000000^3221 ≤ 10034880749141^3221*1250000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218414977 1250000000 10034880749141 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5660103741/10000000000 : ℝ)^4245 ≤ (47232820589587/100000000000000 : ℝ)^3221 := by
    have hnat : (5660103741 : ℕ)^4245*100000000000000^3221 ≤ 47232820589587^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5660103741 10000000000 47232820589587 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2622992633/5000000000 : ℝ), (-218414977/1250000000 : ℝ), (5660103741/10000000000 : ℝ)] ![(5341537331337/12500000000000 : ℝ), (10034880749141/100000000000000 : ℝ), (47232820589587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2622992633/5000000000 : ℝ)|^4245 ≤ (5341537331337/12500000000000 : ℝ)^3221
        have hw : |(2622992633/5000000000 : ℝ)|=(2622992633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-218414977/1250000000 : ℝ)|^4245 ≤ (10034880749141/100000000000000 : ℝ)^3221
        have hw : |(-218414977/1250000000 : ℝ)|=(218414977/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5660103741/10000000000 : ℝ)|^4245 ≤ (47232820589587/100000000000000 : ℝ)^3221
        have hw : |(5660103741/10000000000 : ℝ)|=(5660103741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s1_6 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5245985173/10000000000 : ℝ)*x 0 + (2830051697/5000000000 : ℝ)*x 1 + (-1747320451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245985173/10000000000 : ℝ)^4245 ≤ (10683074413077/25000000000000 : ℝ)^3221 := by
    have hnat : (5245985173 : ℕ)^4245*25000000000000^3221 ≤ 10683074413077^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245985173 10000000000 10683074413077 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2830051697/5000000000 : ℝ)^4245 ≤ (9446563354669/20000000000000 : ℝ)^3221 := by
    have hnat : (2830051697 : ℕ)^4245*20000000000000^3221 ≤ 9446563354669^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2830051697 5000000000 9446563354669 20000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1747320451/10000000000 : ℝ)^4245 ≤ (10034885555327/100000000000000 : ℝ)^3221 := by
    have hnat : (1747320451 : ℕ)^4245*100000000000000^3221 ≤ 10034885555327^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1747320451 10000000000 10034885555327 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5245985173/10000000000 : ℝ), (2830051697/5000000000 : ℝ), (-1747320451/10000000000 : ℝ)] ![(10683074413077/25000000000000 : ℝ), (9446563354669/20000000000000 : ℝ), (10034885555327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5245985173/10000000000 : ℝ)|^4245 ≤ (10683074413077/25000000000000 : ℝ)^3221
        have hw : |(5245985173/10000000000 : ℝ)|=(5245985173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2830051697/5000000000 : ℝ)|^4245 ≤ (9446563354669/20000000000000 : ℝ)^3221
        have hw : |(2830051697/5000000000 : ℝ)|=(2830051697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1747320451/10000000000 : ℝ)|^4245 ≤ (10034885555327/100000000000000 : ℝ)^3221
        have hw : |(-1747320451/10000000000 : ℝ)|=(1747320451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s1_7 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4303701541/10000000000 : ℝ)*x 0 + (4990803573/10000000000 : ℝ)*x 1 + (3709854321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303701541/10000000000 : ℝ)^4245 ≤ (8229539976013/25000000000000 : ℝ)^3221 := by
    have hnat : (4303701541 : ℕ)^4245*25000000000000^3221 ≤ 8229539976013^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303701541 10000000000 8229539976013 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4990803573/10000000000 : ℝ)^4245 ≤ (8002851076549/20000000000000 : ℝ)^3221 := by
    have hnat : (4990803573 : ℕ)^4245*20000000000000^3221 ≤ 8002851076549^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4990803573 10000000000 8002851076549 20000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3709854321/10000000000 : ℝ)^4245 ≤ (5413516939939/20000000000000 : ℝ)^3221 := by
    have hnat : (3709854321 : ℕ)^4245*20000000000000^3221 ≤ 5413516939939^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3709854321 10000000000 5413516939939 20000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303701541/10000000000 : ℝ), (4990803573/10000000000 : ℝ), (3709854321/10000000000 : ℝ)] ![(8229539976013/25000000000000 : ℝ), (8002851076549/20000000000000 : ℝ), (5413516939939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303701541/10000000000 : ℝ)|^4245 ≤ (8229539976013/25000000000000 : ℝ)^3221
        have hw : |(4303701541/10000000000 : ℝ)|=(4303701541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4990803573/10000000000 : ℝ)|^4245 ≤ (8002851076549/20000000000000 : ℝ)^3221
        have hw : |(4990803573/10000000000 : ℝ)|=(4990803573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3709854321/10000000000 : ℝ)|^4245 ≤ (5413516939939/20000000000000 : ℝ)^3221
        have hw : |(3709854321/10000000000 : ℝ)|=(3709854321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1285_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27287/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (489/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (6339/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19907/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27287/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (489/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27287/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (489/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27287/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (489/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27287/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (489/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27287/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (489/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27287/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (489/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (489/50000 : ℝ) ^ (1061/256 : ℝ) ≤ (29293859827/6250000000000000000 : ℝ) := by
    have hpowers : (489/50000 : ℝ)^1061 ≤ (29293859827/6250000000000000000 : ℝ)^256 := by
      have hnat : (489 : ℕ)^1061*6250000000000000000^256 ≤ 29293859827^256*50000^1061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        489 50000 29293859827 6250000000000000000 1061 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (489/50000 : ℝ)) (X := (29293859827/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hpowhi : (27287/100000 : ℝ) ^ (1061/256 : ℝ) ≤ (459516540853941213/100000000000000000000 : ℝ) := by
    have hpowers : (27287/100000 : ℝ)^1061 ≤ (459516540853941213/100000000000000000000 : ℝ)^256 := by
      have hnat : (27287 : ℕ)^1061*100000000000000000000^256 ≤ 459516540853941213^256*100000^1061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27287 100000 459516540853941213 100000000000000000000 1061 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27287/100000 : ℝ)) (X := (459516540853941213/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125000029293859827/3125000000000000000 : ℝ) ≤ (5000000011308921/5000000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (3125000029293859827/3125000000000000000 : ℝ)^256 ≤ (5000000011308921/5000000000000000 : ℝ)^1061 := by
      have hnat : (3125000029293859827 : ℕ)^256*5000000000000000^1061 ≤ 5000000011308921^1061*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125000029293859827 3125000000000000000 5000000011308921 5000000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000011308921/5000000000000000 : ℝ)) (X := (3125000029293859827/3125000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20091903401911139689/20000000000000000000 : ℝ) ≤ (10011068033848017/10000000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (20091903401911139689/20000000000000000000 : ℝ)^256 ≤ (10011068033848017/10000000000000000 : ℝ)^1061 := by
      have hnat : (20091903401911139689 : ℕ)^256*10000000000000000^1061 ≤ 10011068033848017^1061*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20091903401911139689 20000000000000000000 10011068033848017 10000000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011068033848017/10000000000000000 : ℝ)) (X := (20091903401911139689/20000000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50459516540853941213/50000000000000000000 : ℝ) ≤ (626383502817387/625000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (50459516540853941213/50000000000000000000 : ℝ)^256 ≤ (626383502817387/625000000000000 : ℝ)^1061 := by
      have hnat : (50459516540853941213 : ℕ)^256*625000000000000^1061 ≤ 626383502817387^1061*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50459516540853941213 50000000000000000000 626383502817387 625000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (626383502817387/625000000000000 : ℝ)) (X := (50459516540853941213/50000000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(29293859827/6250000000000000000 : ℝ) ≤ ((131534175782543291439/131545000000000000000 : ℝ)+2*(442720449207/105236000000000 : ℝ)*(489/50000 : ℝ))^(1061/256 : ℝ) := by
    rw [show (131534175782543291439/131545000000000000000 : ℝ)+2*(442720449207/105236000000000 : ℝ)*(489/50000 : ℝ)=(5000000011308921/5000000000000000 : ℝ) by norm_num, show 1+2*(29293859827/6250000000000000000 : ℝ)=(3125000029293859827/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(459516540853941213/100000000000000000000 : ℝ)+(29293859827/6250000000000000000 : ℝ) ≤ ((131534175782543291439/131545000000000000000 : ℝ)+(442720449207/105236000000000 : ℝ)*((27287/100000 : ℝ)+(489/50000 : ℝ)))^(1061/256 : ℝ) := by
    rw [show (131534175782543291439/131545000000000000000 : ℝ)+(442720449207/105236000000000 : ℝ)*((27287/100000 : ℝ)+(489/50000 : ℝ))=(10011068033848017/10000000000000000 : ℝ) by norm_num, show 1+(459516540853941213/100000000000000000000 : ℝ)+(29293859827/6250000000000000000 : ℝ)=(20091903401911139689/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(459516540853941213/100000000000000000000 : ℝ) ≤ ((131534175782543291439/131545000000000000000 : ℝ)+2*(442720449207/105236000000000 : ℝ)*(27287/100000 : ℝ))^(1061/256 : ℝ) := by
    rw [show (131534175782543291439/131545000000000000000 : ℝ)+2*(442720449207/105236000000000 : ℝ)*(27287/100000 : ℝ)=(626383502817387/625000000000000 : ℝ) by norm_num, show 1+2*(459516540853941213/100000000000000000000 : ℝ)=(50459516540853941213/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (131534175782543291439/131545000000000000000 : ℝ)*(X 1 0+X 2 0)+(442720449207/105236000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (489/50000 : ℝ)) (hi := (27287/100000 : ℝ)) (c := (131534175782543291439/131545000000000000000 : ℝ)) (alpha := (442720449207/105236000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (131534175782543291439/131545000000000000000 : ℝ)*(X 0 1+X 2 1)+(442720449207/105236000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (489/50000 : ℝ)) (hi := (27287/100000 : ℝ)) (c := (131534175782543291439/131545000000000000000 : ℝ)) (alpha := (442720449207/105236000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (131534175782543291439/131545000000000000000 : ℝ)*(X 0 2+X 1 2)+(442720449207/105236000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (489/50000 : ℝ)) (hi := (27287/100000 : ℝ)) (c := (131534175782543291439/131545000000000000000 : ℝ)) (alpha := (442720449207/105236000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2036385913/10000000000 : ℝ)*X 0 0+(283433847/500000000 : ℝ)*X 0 1+(2513378821/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5411730797/10000000000 : ℝ)*X 1 0+(-2380665681/10000000000 : ℝ)*X 1 1+(5026757509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5411730591/10000000000 : ℝ)*X 2 0+(2513378827/5000000000 : ℝ)*X 2 1+(-595166441/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1075591203/2500000000 : ℝ)*X 0 0+(1846140479/5000000000 : ℝ)*X 0 1+(5008049249/10000000000 : ℝ)*X 0 2+(1075591203/2500000000 : ℝ)*X 1 0+(1846140479/5000000000 : ℝ)*X 1 1+(5008049249/10000000000 : ℝ)*X 1 2+(1075591203/2500000000 : ℝ)*X 2 0+(1846140479/5000000000 : ℝ)*X 2 1+(5008049249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2037038333/10000000000 : ℝ)*X 0 0+(5035171359/10000000000 : ℝ)*X 0 1+(1132020643/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2622992633/5000000000 : ℝ)*X 1 0+(-218414977/1250000000 : ℝ)*X 1 1+(5660103741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5245985173/10000000000 : ℝ)*X 2 0+(2830051697/5000000000 : ℝ)*X 2 1+(-1747320451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4303701541/10000000000 : ℝ)*X 0 0+(4990803573/10000000000 : ℝ)*X 0 1+(3709854321/10000000000 : ℝ)*X 0 2+(4303701541/10000000000 : ℝ)*X 1 0+(4990803573/10000000000 : ℝ)*X 1 1+(3709854321/10000000000 : ℝ)*X 1 2+(4303701541/10000000000 : ℝ)*X 2 0+(4990803573/10000000000 : ℝ)*X 2 1+(3709854321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1127135881248958324813107339/411078125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (706919/2500000000000 : ℝ)*(base1) + (17019887/3125000000000 : ℝ)*(base19) + (485336747/100000000000000 : ℝ)*(base23) + (37556539/50000000000000 : ℝ)*(upper3) + (28422883/100000000000000 : ℝ)*(upper5) + (1158924402629957/100000000000000 : ℝ)*(major0) + (1158924402629957/100000000000000 : ℝ)*(major1) + (579462201314979/50000000000000 : ℝ)*(major2) + (97364457239229/6250000000000 : ℝ)*(sp0) + (389458320510721/25000000000000 : ℝ)*(sp1) + (38945833533563/2500000000000 : ℝ)*(sp2) + (760013453876387/100000000000000 : ℝ)*(sp3) + (634782091/25000000000000 : ℝ)*(sp4) + (281006153/20000000000000 : ℝ)*(sp7) + (95001860897989/12500000000000 : ℝ)*(f.failure) + (1557833826679267/100000000000000 : ℝ)*(f.sum) + (13393406378411/10523600000000000000000000000 : ℝ)*base65 + (63102541798365961877/13154500000000000000000000000000000 : ℝ)*base68 + (28241616447075960219/6577250000000000000000000000000000 : ℝ)*base70 + (75657784999150961877/13154500000000000000000000000000000 : ℝ)*base72 + (198234765445259/52618000000000000000000000000 : ℝ)*base73 + (28675171718843960219/6577250000000000000000000000000000 : ℝ)*base76 + (50895755100933711877/13154500000000000000000000000000000 : ℝ)*base78 + (9425901058072711877/13154500000000000000000000000000000 : ℝ)*base80 + (110674657424737/26309000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2705137/625000000000000000000 : ℝ)*base89 + (2705137/625000000000000000000 : ℝ)*base91 + (3544863/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27103748105082436205070489879/3288625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17762343/100000000000000 : ℝ)*(base1) + (392963801/25000000000000 : ℝ)*(base19) + (375610829/25000000000000 : ℝ)*(base23) + (227139721/100000000000000 : ℝ)*(upper3) + (179232073/100000000000000 : ℝ)*(upper5) + (595211302510671/50000000000000 : ℝ)*(major0) + (595211302510671/50000000000000 : ℝ)*(major1) + (595211302510671/50000000000000 : ℝ)*(major2) + (8354744573/100000000000000 : ℝ)*(sp1) + (352783163/5000000000000 : ℝ)*(sp2) + (1600173755027679/100000000000000 : ℝ)*(sp4) + (1600163810665559/100000000000000 : ℝ)*(sp5) + (1600165179158759/100000000000000 : ℝ)*(sp6) + (780671180292803/100000000000000 : ℝ)*(sp7) + (390335599027573/50000000000000 : ℝ)*(f.failure) + (200021717158167/12500000000000 : ℝ)*(f.sum) + (27680122477663/13154500000000000000000000000 : ℝ)*base65 + (3097555413151695569/6577250000000000000000000000000000 : ℝ)*base67 + (50962776236098695569/6577250000000000000000000000000000 : ℝ)*base69 + (37406155996736195569/6577250000000000000000000000000000 : ℝ)*base71 + (9667065272561/3288625000000000000000000000 : ℝ)*base74 + (11639918289768945569/6577250000000000000000000000000000 : ℝ)*base75 + (41855674882504195569/6577250000000000000000000000000000 : ℝ)*base77 + (104523523359045445569/6577250000000000000000000000000000 : ℝ)*base79 + (15284750925861/6577250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (20064591/2500000000000000000000 : ℝ)*base90 + (20064591/2500000000000000000000 : ℝ)*base92 + (20064591/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1285_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27287/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (489/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6339/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19907/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1285_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1285_s2_0 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2081744931/10000000000 : ℝ)*x 0 + (5496422131/10000000000 : ℝ)*x 1 + (5170052203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2081744931/10000000000 : ℝ)^4245 ≤ (631998861267/5000000000000 : ℝ)^3221 := by
    have hnat : (2081744931 : ℕ)^4245*5000000000000^3221 ≤ 631998861267^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081744931 10000000000 631998861267 5000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5496422131/10000000000 : ℝ)^4245 ≤ (45441010265361/100000000000000 : ℝ)^3221 := by
    have hnat : (5496422131 : ℕ)^4245*100000000000000^3221 ≤ 45441010265361^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496422131 10000000000 45441010265361 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5170052203/10000000000 : ℝ)^4245 ≤ (20959506251623/50000000000000 : ℝ)^3221 := by
    have hnat : (5170052203 : ℕ)^4245*50000000000000^3221 ≤ 20959506251623^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170052203 10000000000 20959506251623 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2081744931/10000000000 : ℝ), (5496422131/10000000000 : ℝ), (5170052203/10000000000 : ℝ)] ![(631998861267/5000000000000 : ℝ), (45441010265361/100000000000000 : ℝ), (20959506251623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2081744931/10000000000 : ℝ)|^4245 ≤ (631998861267/5000000000000 : ℝ)^3221
        have hw : |(-2081744931/10000000000 : ℝ)|=(2081744931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5496422131/10000000000 : ℝ)|^4245 ≤ (45441010265361/100000000000000 : ℝ)^3221
        have hw : |(5496422131/10000000000 : ℝ)|=(5496422131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5170052203/10000000000 : ℝ)|^4245 ≤ (20959506251623/50000000000000 : ℝ)^3221
        have hw : |(5170052203/10000000000 : ℝ)|=(5170052203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s2_1 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370111349/10000000000 : ℝ)*x 0 + (-2250950183/10000000000 : ℝ)*x 1 + (1034010547/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370111349/10000000000 : ℝ)^4245 ≤ (11017455138491/25000000000000 : ℝ)^3221 := by
    have hnat : (5370111349 : ℕ)^4245*25000000000000^3221 ≤ 11017455138491^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370111349 10000000000 11017455138491 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250950183/10000000000 : ℝ)^4245 ≤ (14011161236743/100000000000000 : ℝ)^3221 := by
    have hnat : (2250950183 : ℕ)^4245*100000000000000^3221 ≤ 14011161236743^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250950183 10000000000 14011161236743 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034010547/2000000000 : ℝ)^4245 ≤ (1047975454701/2500000000000 : ℝ)^3221 := by
    have hnat : (1034010547 : ℕ)^4245*2500000000000^3221 ≤ 1047975454701^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034010547 2000000000 1047975454701 2500000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370111349/10000000000 : ℝ), (-2250950183/10000000000 : ℝ), (1034010547/2000000000 : ℝ)] ![(11017455138491/25000000000000 : ℝ), (14011161236743/100000000000000 : ℝ), (1047975454701/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370111349/10000000000 : ℝ)|^4245 ≤ (11017455138491/25000000000000 : ℝ)^3221
        have hw : |(5370111349/10000000000 : ℝ)|=(5370111349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2250950183/10000000000 : ℝ)|^4245 ≤ (14011161236743/100000000000000 : ℝ)^3221
        have hw : |(-2250950183/10000000000 : ℝ)|=(2250950183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034010547/2000000000 : ℝ)|^4245 ≤ (1047975454701/2500000000000 : ℝ)^3221
        have hw : |(1034010547/2000000000 : ℝ)|=(1034010547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s2_2 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342527913/2500000000 : ℝ)*x 0 + (646256533/1250000000 : ℝ)*x 1 + (-1125475199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342527913/2500000000 : ℝ)^4245 ≤ (5508727978881/12500000000000 : ℝ)^3221 := by
    have hnat : (1342527913 : ℕ)^4245*12500000000000^3221 ≤ 5508727978881^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342527913 2500000000 5508727978881 12500000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (646256533/1250000000 : ℝ)^4245 ≤ (20959506577537/50000000000000 : ℝ)^3221 := by
    have hnat : (646256533 : ℕ)^4245*50000000000000^3221 ≤ 20959506577537^3221*1250000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646256533 1250000000 20959506577537 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125475199/5000000000 : ℝ)^4245 ≤ (87569768753/625000000000 : ℝ)^3221 := by
    have hnat : (1125475199 : ℕ)^4245*625000000000^3221 ≤ 87569768753^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125475199 5000000000 87569768753 625000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342527913/2500000000 : ℝ), (646256533/1250000000 : ℝ), (-1125475199/5000000000 : ℝ)] ![(5508727978881/12500000000000 : ℝ), (20959506577537/50000000000000 : ℝ), (87569768753/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342527913/2500000000 : ℝ)|^4245 ≤ (5508727978881/12500000000000 : ℝ)^3221
        have hw : |(1342527913/2500000000 : ℝ)|=(1342527913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(646256533/1250000000 : ℝ)|^4245 ≤ (20959506577537/50000000000000 : ℝ)^3221
        have hw : |(646256533/1250000000 : ℝ)|=(646256533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1125475199/5000000000 : ℝ)|^4245 ≤ (87569768753/625000000000 : ℝ)^3221
        have hw : |(-1125475199/5000000000 : ℝ)|=(1125475199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s2_3 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083467073/2500000000 : ℝ)*x 0 + (4011716319/10000000000 : ℝ)*x 1 + (4680696893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083467073/2500000000 : ℝ)^4245 ≤ (1661129646677/5000000000000 : ℝ)^3221 := by
    have hnat : (1083467073 : ℕ)^4245*5000000000000^3221 ≤ 1661129646677^3221*2500000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083467073 2500000000 1661129646677 5000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4011716319/10000000000 : ℝ)^4245 ≤ (7501765222313/25000000000000 : ℝ)^3221 := by
    have hnat : (4011716319 : ℕ)^4245*25000000000000^3221 ≤ 7501765222313^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4011716319 10000000000 7501765222313 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4680696893/10000000000 : ℝ)^4245 ≤ (36770346164581/100000000000000 : ℝ)^3221 := by
    have hnat : (4680696893 : ℕ)^4245*100000000000000^3221 ≤ 36770346164581^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4680696893 10000000000 36770346164581 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083467073/2500000000 : ℝ), (4011716319/10000000000 : ℝ), (4680696893/10000000000 : ℝ)] ![(1661129646677/5000000000000 : ℝ), (7501765222313/25000000000000 : ℝ), (36770346164581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083467073/2500000000 : ℝ)|^4245 ≤ (1661129646677/5000000000000 : ℝ)^3221
        have hw : |(1083467073/2500000000 : ℝ)|=(1083467073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4011716319/10000000000 : ℝ)|^4245 ≤ (7501765222313/25000000000000 : ℝ)^3221
        have hw : |(4011716319/10000000000 : ℝ)|=(4011716319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4680696893/10000000000 : ℝ)|^4245 ≤ (36770346164581/100000000000000 : ℝ)^3221
        have hw : |(4680696893/10000000000 : ℝ)|=(4680696893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s2_4 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-208182981/1000000000 : ℝ)*x 0 + (2586118371/5000000000 : ℝ)*x 1 + (5494217071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208182981/1000000000 : ℝ)^4245 ≤ (12640656442757/100000000000000 : ℝ)^3221 := by
    have hnat : (208182981 : ℕ)^4245*100000000000000^3221 ≤ 12640656442757^3221*1000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208182981 1000000000 12640656442757 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2586118371/5000000000 : ℝ)^4245 ≤ (5242794675641/12500000000000 : ℝ)^3221 := by
    have hnat : (2586118371 : ℕ)^4245*12500000000000^3221 ≤ 5242794675641^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586118371 5000000000 5242794675641 12500000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5494217071/10000000000 : ℝ)^4245 ≤ (45416986140243/100000000000000 : ℝ)^3221 := by
    have hnat : (5494217071 : ℕ)^4245*100000000000000^3221 ≤ 45416986140243^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494217071 10000000000 45416986140243 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208182981/1000000000 : ℝ), (2586118371/5000000000 : ℝ), (5494217071/10000000000 : ℝ)] ![(12640656442757/100000000000000 : ℝ), (5242794675641/12500000000000 : ℝ), (45416986140243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208182981/1000000000 : ℝ)|^4245 ≤ (12640656442757/100000000000000 : ℝ)^3221
        have hw : |(-208182981/1000000000 : ℝ)|=(208182981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2586118371/5000000000 : ℝ)|^4245 ≤ (5242794675641/12500000000000 : ℝ)^3221
        have hw : |(2586118371/5000000000 : ℝ)|=(2586118371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5494217071/10000000000 : ℝ)|^4245 ≤ (45416986140243/100000000000000 : ℝ)^3221
        have hw : |(5494217071/10000000000 : ℝ)|=(5494217071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s2_5 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057306381/2000000000 : ℝ)*x 0 + (-385357037/2000000000 : ℝ)*x 1 + (2747108611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057306381/2000000000 : ℝ)^4245 ≤ (10792028702129/25000000000000 : ℝ)^3221 := by
    have hnat : (1057306381 : ℕ)^4245*25000000000000^3221 ≤ 10792028702129^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057306381 2000000000 10792028702129 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (385357037/2000000000 : ℝ)^4245 ≤ (5707448700031/50000000000000 : ℝ)^3221 := by
    have hnat : (385357037 : ℕ)^4245*50000000000000^3221 ≤ 5707448700031^3221*2000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385357037 2000000000 5707448700031 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2747108611/5000000000 : ℝ)^4245 ≤ (45416987785283/100000000000000 : ℝ)^3221 := by
    have hnat : (2747108611 : ℕ)^4245*100000000000000^3221 ≤ 45416987785283^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747108611 5000000000 45416987785283 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057306381/2000000000 : ℝ), (-385357037/2000000000 : ℝ), (2747108611/5000000000 : ℝ)] ![(10792028702129/25000000000000 : ℝ), (5707448700031/50000000000000 : ℝ), (45416987785283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057306381/2000000000 : ℝ)|^4245 ≤ (10792028702129/25000000000000 : ℝ)^3221
        have hw : |(1057306381/2000000000 : ℝ)|=(1057306381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-385357037/2000000000 : ℝ)|^4245 ≤ (5707448700031/50000000000000 : ℝ)^3221
        have hw : |(-385357037/2000000000 : ℝ)|=(385357037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2747108611/5000000000 : ℝ)|^4245 ≤ (45416987785283/100000000000000 : ℝ)^3221
        have hw : |(2747108611/5000000000 : ℝ)|=(2747108611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s2_6 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286532083/10000000000 : ℝ)*x 0 + (137355427/250000000 : ℝ)*x 1 + (-1926785137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286532083/10000000000 : ℝ)^4245 ≤ (43168116724091/100000000000000 : ℝ)^3221 := by
    have hnat : (5286532083 : ℕ)^4245*100000000000000^3221 ≤ 43168116724091^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286532083 10000000000 43168116724091 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137355427/250000000 : ℝ)^4245 ≤ (11354246559573/25000000000000 : ℝ)^3221 := by
    have hnat : (137355427 : ℕ)^4245*25000000000000^3221 ≤ 11354246559573^3221*250000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137355427 250000000 11354246559573 25000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1926785137/10000000000 : ℝ)^4245 ≤ (1141489702529/10000000000000 : ℝ)^3221 := by
    have hnat : (1926785137 : ℕ)^4245*10000000000000^3221 ≤ 1141489702529^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926785137 10000000000 1141489702529 10000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286532083/10000000000 : ℝ), (137355427/250000000 : ℝ), (-1926785137/10000000000 : ℝ)] ![(43168116724091/100000000000000 : ℝ), (11354246559573/25000000000000 : ℝ), (1141489702529/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286532083/10000000000 : ℝ)|^4245 ≤ (43168116724091/100000000000000 : ℝ)^3221
        have hw : |(5286532083/10000000000 : ℝ)|=(5286532083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137355427/250000000 : ℝ)|^4245 ≤ (11354246559573/25000000000000 : ℝ)^3221
        have hw : |(137355427/250000000 : ℝ)|=(137355427/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1926785137/10000000000 : ℝ)|^4245 ≤ (1141489702529/10000000000000 : ℝ)^3221
        have hw : |(-1926785137/10000000000 : ℝ)|=(1926785137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1285_s2_7 (p : ℝ) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4334042287/10000000000 : ℝ)*x 0 + (2338108939/5000000000 : ℝ)*x 1 + (401624057/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334042287/10000000000 : ℝ)^4245 ≤ (33224350793709/100000000000000 : ℝ)^3221 := by
    have hnat : (4334042287 : ℕ)^4245*100000000000000^3221 ≤ 33224350793709^3221*10000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334042287 10000000000 33224350793709 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2338108939/5000000000 : ℝ)^4245 ≤ (36723981127909/100000000000000 : ℝ)^3221 := by
    have hnat : (2338108939 : ℕ)^4245*100000000000000^3221 ≤ 36723981127909^3221*5000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2338108939 5000000000 36723981127909 100000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (401624057/1000000000 : ℝ)^4245 ≤ (15025834032751/50000000000000 : ℝ)^3221 := by
    have hnat : (401624057 : ℕ)^4245*50000000000000^3221 ≤ 15025834032751^3221*1000000000^4245 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401624057 1000000000 15025834032751 50000000000000 4245 3221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4245/1024 : ℝ)) 4245 3221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334042287/10000000000 : ℝ), (2338108939/5000000000 : ℝ), (401624057/1000000000 : ℝ)] ![(33224350793709/100000000000000 : ℝ), (36723981127909/100000000000000 : ℝ), (15025834032751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334042287/10000000000 : ℝ)|^4245 ≤ (33224350793709/100000000000000 : ℝ)^3221
        have hw : |(4334042287/10000000000 : ℝ)|=(4334042287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2338108939/5000000000 : ℝ)|^4245 ≤ (36723981127909/100000000000000 : ℝ)^3221
        have hw : |(2338108939/5000000000 : ℝ)|=(2338108939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(401624057/1000000000 : ℝ)|^4245 ≤ (15025834032751/50000000000000 : ℝ)^3221
        have hw : |(401624057/1000000000 : ℝ)|=(401624057/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1285_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19907/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9453/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (327/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19907/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19907/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19907/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19907/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19907/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19907/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6339/100000 : ℝ) ^ (1061/256 : ℝ) ≤ (27094277686997/2500000000000000000 : ℝ) := by
    have hpowers : (6339/100000 : ℝ)^1061 ≤ (27094277686997/2500000000000000000 : ℝ)^256 := by
      have hnat : (6339 : ℕ)^1061*2500000000000000000^256 ≤ 27094277686997^256*100000^1061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6339 100000 27094277686997 2500000000000000000 1061 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6339/100000 : ℝ)) (X := (27094277686997/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hpowhi : (19907/100000 : ℝ) ^ (1061/256 : ℝ) ≤ (124367727907839719/100000000000000000000 : ℝ) := by
    have hpowers : (19907/100000 : ℝ)^1061 ≤ (124367727907839719/100000000000000000000 : ℝ)^256 := by
      have hnat : (19907 : ℕ)^1061*100000000000000000000^256 ≤ 124367727907839719^256*100000^1061 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19907 100000 124367727907839719 100000000000000000000 1061 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19907/100000 : ℝ)) (X := (124367727907839719/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250027094277686997/1250000000000000000 : ℝ) ≤ (10000052298420769/10000000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (1250027094277686997/1250000000000000000 : ℝ)^256 ≤ (10000052298420769/10000000000000000 : ℝ)^1061 := by
      have hnat : (1250027094277686997 : ℕ)^256*10000000000000000^1061 ≤ 10000052298420769^1061*1250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250027094277686997 1250000000000000000 10000052298420769 10000000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000052298420769/10000000000000000 : ℝ)) (X := (1250027094277686997/1250000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100125451499015319599/100000000000000000000 : ℝ) ≤ (5001512738491883/5000000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (100125451499015319599/100000000000000000000 : ℝ)^256 ≤ (5001512738491883/5000000000000000 : ℝ)^1061 := by
      have hnat : (100125451499015319599 : ℕ)^256*5000000000000000^1061 ≤ 5001512738491883^1061*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100125451499015319599 100000000000000000000 5001512738491883 5000000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001512738491883/5000000000000000 : ℝ)) (X := (100125451499015319599/100000000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50124367727907839719/50000000000000000000 : ℝ) ≤ (10005998655546763/10000000000000000 : ℝ) ^ (1061/256 : ℝ) := by
    have hpowers : (50124367727907839719/50000000000000000000 : ℝ)^256 ≤ (10005998655546763/10000000000000000 : ℝ)^1061 := by
      have hnat : (50124367727907839719 : ℕ)^256*10000000000000000^1061 ≤ 10005998655546763^1061*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50124367727907839719 50000000000000000000 10005998655546763 10000000000000000 256 1061 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005998655546763/10000000000000000 : ℝ)) (X := (50124367727907839719/50000000000000000000 : ℝ)) (by norm_num) 1061 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(27094277686997/2500000000000000000 : ℝ) ≤ ((67821507813575658913/67840000000000000000 : ℝ)+2*(2973178562997/1356800000000000 : ℝ)*(6339/100000 : ℝ))^(1061/256 : ℝ) := by
    rw [show (67821507813575658913/67840000000000000000 : ℝ)+2*(2973178562997/1356800000000000 : ℝ)*(6339/100000 : ℝ)=(10000052298420769/10000000000000000 : ℝ) by norm_num, show 1+2*(27094277686997/2500000000000000000 : ℝ)=(1250027094277686997/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(124367727907839719/100000000000000000000 : ℝ)+(27094277686997/2500000000000000000 : ℝ) ≤ ((67821507813575658913/67840000000000000000 : ℝ)+(2973178562997/1356800000000000 : ℝ)*((19907/100000 : ℝ)+(6339/100000 : ℝ)))^(1061/256 : ℝ) := by
    rw [show (67821507813575658913/67840000000000000000 : ℝ)+(2973178562997/1356800000000000 : ℝ)*((19907/100000 : ℝ)+(6339/100000 : ℝ))=(5001512738491883/5000000000000000 : ℝ) by norm_num, show 1+(124367727907839719/100000000000000000000 : ℝ)+(27094277686997/2500000000000000000 : ℝ)=(100125451499015319599/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(124367727907839719/100000000000000000000 : ℝ) ≤ ((67821507813575658913/67840000000000000000 : ℝ)+2*(2973178562997/1356800000000000 : ℝ)*(19907/100000 : ℝ))^(1061/256 : ℝ) := by
    rw [show (67821507813575658913/67840000000000000000 : ℝ)+2*(2973178562997/1356800000000000 : ℝ)*(19907/100000 : ℝ)=(10005998655546763/10000000000000000 : ℝ) by norm_num, show 1+2*(124367727907839719/100000000000000000000 : ℝ)=(50124367727907839719/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (67821507813575658913/67840000000000000000 : ℝ)*(X 1 0+X 2 0)+(2973178562997/1356800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (6339/100000 : ℝ)) (hi := (19907/100000 : ℝ)) (c := (67821507813575658913/67840000000000000000 : ℝ)) (alpha := (2973178562997/1356800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (67821507813575658913/67840000000000000000 : ℝ)*(X 0 1+X 2 1)+(2973178562997/1356800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (6339/100000 : ℝ)) (hi := (19907/100000 : ℝ)) (c := (67821507813575658913/67840000000000000000 : ℝ)) (alpha := (2973178562997/1356800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (67821507813575658913/67840000000000000000 : ℝ)*(X 0 2+X 1 2)+(2973178562997/1356800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1061/256 : ℝ)) (lo := (6339/100000 : ℝ)) (hi := (19907/100000 : ℝ)) (c := (67821507813575658913/67840000000000000000 : ℝ)) (alpha := (2973178562997/1356800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2081744931/10000000000 : ℝ)*X 0 0+(5496422131/10000000000 : ℝ)*X 0 1+(5170052203/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5370111349/10000000000 : ℝ)*X 1 0+(-2250950183/10000000000 : ℝ)*X 1 1+(1034010547/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1342527913/2500000000 : ℝ)*X 2 0+(646256533/1250000000 : ℝ)*X 2 1+(-1125475199/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1083467073/2500000000 : ℝ)*X 0 0+(4011716319/10000000000 : ℝ)*X 0 1+(4680696893/10000000000 : ℝ)*X 0 2+(1083467073/2500000000 : ℝ)*X 1 0+(4011716319/10000000000 : ℝ)*X 1 1+(4680696893/10000000000 : ℝ)*X 1 2+(1083467073/2500000000 : ℝ)*X 2 0+(4011716319/10000000000 : ℝ)*X 2 1+(4680696893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-208182981/1000000000 : ℝ)*X 0 0+(2586118371/5000000000 : ℝ)*X 0 1+(5494217071/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057306381/2000000000 : ℝ)*X 1 0+(-385357037/2000000000 : ℝ)*X 1 1+(2747108611/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5286532083/10000000000 : ℝ)*X 2 0+(137355427/250000000 : ℝ)*X 2 1+(-1926785137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4334042287/10000000000 : ℝ)*X 0 0+(2338108939/5000000000 : ℝ)*X 0 1+(401624057/1000000000 : ℝ)*X 0 2+(4334042287/10000000000 : ℝ)*X 1 0+(2338108939/5000000000 : ℝ)*X 1 1+(401624057/1000000000 : ℝ)*X 1 2+(4334042287/10000000000 : ℝ)*X 2 0+(2338108939/5000000000 : ℝ)*X 2 1+(401624057/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1285_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (998014519990878435041073087/424000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (665081689/50000000000000 : ℝ)*(base19) + (283503653/20000000000000 : ℝ)*(base23) + (5741201/12500000000000 : ℝ)*(lower2) + (54425329/12500000000000 : ℝ)*(upper3) + (25383123/10000000000000 : ℝ)*(upper5) + (569858979296333/25000000000000 : ℝ)*(major0) + (569858979296333/25000000000000 : ℝ)*(major1) + (569858979296333/25000000000000 : ℝ)*(major2) + (3064021481152489/100000000000000 : ℝ)*(sp0) + (766007891741127/25000000000000 : ℝ)*(sp1) + (153201573980481/5000000000000 : ℝ)*(sp2) + (373706044269943/25000000000000 : ℝ)*(sp3) + (2853993849/25000000000000 : ℝ)*(sp4) + (7340851369/50000000000000 : ℝ)*(sp7) + (149483885878251/10000000000000 : ℝ)*(f.failure) + (612806579425577/20000000000000 : ℝ)*(f.sum) + (36830224331441/16960000000000000000000000000 : ℝ)*base65 + (6269017251548283971/1696000000000000000000000000000000 : ℝ)*base68 + (19418299131484283971/1696000000000000000000000000000000 : ℝ)*base70 + (20997741672252283971/1696000000000000000000000000000000 : ℝ)*base72 + (21069108804721/16960000000000000000000000000 : ℝ)*base73 + (17180869782396283971/1696000000000000000000000000000000 : ℝ)*base76 + (8033892879939716029/1696000000000000000000000000000000 : ℝ)*base77 + (17857184509692283971/1696000000000000000000000000000000 : ℝ)*base80 + (91687009430159/16960000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4100783/500000000000000000000 : ℝ)*base89 + (4100783/500000000000000000000 : ℝ)*base91 + (4100783/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3043228224734838108839253483/339200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1692772489/100000000000000 : ℝ)*(base19) + (2046086811/100000000000000 : ℝ)*(base23) + (126666361/50000000000000 : ℝ)*(upper3) + (94371547/100000000000000 : ℝ)*(lower4) + (133603137/100000000000000 : ℝ)*(upper5) + (231049088641703/10000000000000 : ℝ)*(major0) + (231049088641703/10000000000000 : ℝ)*(major1) + (231049088641703/10000000000000 : ℝ)*(major2) + (17160763897/100000000000000 : ℝ)*(sp1) + (10801390603/50000000000000 : ℝ)*(sp2) + (97055530420887/3125000000000 : ℝ)*(sp4) + (1552879059965999/50000000000000 : ℝ)*(sp5) + (3105753324600367/100000000000000 : ℝ)*(sp6) + (303040900061259/20000000000000 : ℝ)*(sp7) + (303040900061259/20000000000000 : ℝ)*(f.failure) + (97055530420887/3125000000000 : ℝ)*(f.sum) + (30163130527891/6784000000000000000000000000 : ℝ)*base65 + (2211340818850798839/678400000000000000000000000000000 : ℝ)*base67 + (2683056438332398839/678400000000000000000000000000000 : ℝ)*base69 + (6784331444002798839/678400000000000000000000000000000 : ℝ)*base71 + (1769760301129/1356800000000000000000000000 : ℝ)*base74 + (1253695089488401161/678400000000000000000000000000000 : ℝ)*base76 + (950279001250798839/678400000000000000000000000000000 : ℝ)*base77 + (3502451849923601161/678400000000000000000000000000000 : ℝ)*base80 + (11720289974381/6784000000000000000000000000 : ℝ)*base82 + (2588047/1000000000000000000000 : ℝ)*base89 + (2588047/1000000000000000000000 : ℝ)*base91 + (2588047/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1285_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19907/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9453/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (327/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1285_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1285_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9453/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (327/2000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1285_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1285_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1285_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1061/256 : ℝ) ≤ p) (hpb : p ≤ (4245/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76243533/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9453/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (327/2000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1285_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

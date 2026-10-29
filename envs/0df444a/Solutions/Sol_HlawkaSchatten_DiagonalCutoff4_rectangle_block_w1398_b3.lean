-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1398_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:44:43.405073+00:00
-- url     : https://prove2.me/submissions/7dd03c6e-fb09-469f-bb70-1752bb6d3853

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
theorem support_rectangle_w1398_box_0 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1833627819/10000000000 : ℝ)*x 0 + (215503161/400000000 : ℝ)*x 1 + (5387578907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1833627819/10000000000 : ℝ)^2179 ≤ (10890445342777/100000000000000 : ℝ)^1667 := by
    have hnat : (1833627819 : ℕ)^2179*100000000000000^1667 ≤ 10890445342777^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833627819 10000000000 10890445342777 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215503161/400000000 : ℝ)^2179 ≤ (44554777956761/100000000000000 : ℝ)^1667 := by
    have hnat : (215503161 : ℕ)^2179*100000000000000^1667 ≤ 44554777956761^1667*400000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215503161 400000000 44554777956761 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387578907/10000000000 : ℝ)^2179 ≤ (44554776681191/100000000000000 : ℝ)^1667 := by
    have hnat : (5387578907 : ℕ)^2179*100000000000000^1667 ≤ 44554776681191^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387578907 10000000000 44554776681191 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1833627819/10000000000 : ℝ), (215503161/400000000 : ℝ), (5387578907/10000000000 : ℝ)] ![(10890445342777/100000000000000 : ℝ), (44554777956761/100000000000000 : ℝ), (44554776681191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1833627819/10000000000 : ℝ)|^2179 ≤ (10890445342777/100000000000000 : ℝ)^1667
        have hw : |(-1833627819/10000000000 : ℝ)|=(1833627819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215503161/400000000 : ℝ)|^2179 ≤ (44554777956761/100000000000000 : ℝ)^1667
        have hw : |(215503161/400000000 : ℝ)|=(215503161/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387578907/10000000000 : ℝ)|^2179 ≤ (44554776681191/100000000000000 : ℝ)^1667
        have hw : |(5387578907/10000000000 : ℝ)|=(5387578907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_box_1 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (211432421/400000000 : ℝ)*x 0 + (-986655697/5000000000 : ℝ)*x 1 + (5387579241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211432421/400000000 : ℝ)^2179 ≤ (10864468611279/25000000000000 : ℝ)^1667 := by
    have hnat : (211432421 : ℕ)^2179*25000000000000^1667 ≤ 10864468611279^1667*400000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211432421 400000000 10864468611279 25000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (986655697/5000000000 : ℝ)^2179 ≤ (5993672623469/50000000000000 : ℝ)^1667 := by
    have hnat : (986655697 : ℕ)^2179*50000000000000^1667 ≤ 5993672623469^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986655697 5000000000 5993672623469 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387579241/10000000000 : ℝ)^2179 ≤ (22277390145851/50000000000000 : ℝ)^1667 := by
    have hnat : (5387579241 : ℕ)^2179*50000000000000^1667 ≤ 22277390145851^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387579241 10000000000 22277390145851 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211432421/400000000 : ℝ), (-986655697/5000000000 : ℝ), (5387579241/10000000000 : ℝ)] ![(10864468611279/25000000000000 : ℝ), (5993672623469/50000000000000 : ℝ), (22277390145851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211432421/400000000 : ℝ)|^2179 ≤ (10864468611279/25000000000000 : ℝ)^1667
        have hw : |(211432421/400000000 : ℝ)|=(211432421/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-986655697/5000000000 : ℝ)|^2179 ≤ (5993672623469/50000000000000 : ℝ)^1667
        have hw : |(-986655697/5000000000 : ℝ)|=(986655697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387579241/10000000000 : ℝ)|^2179 ≤ (22277390145851/50000000000000 : ℝ)^1667
        have hw : |(5387579241/10000000000 : ℝ)|=(5387579241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_box_2 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1321452523/2500000000 : ℝ)*x 0 + (2693789797/5000000000 : ℝ)*x 1 + (-3946623/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321452523/2500000000 : ℝ)^2179 ≤ (43457869791759/100000000000000 : ℝ)^1667 := by
    have hnat : (1321452523 : ℕ)^2179*100000000000000^1667 ≤ 43457869791759^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321452523 2500000000 43457869791759 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693789797/5000000000 : ℝ)^2179 ≤ (22277392053801/50000000000000 : ℝ)^1667 := by
    have hnat : (2693789797 : ℕ)^2179*50000000000000^1667 ≤ 22277392053801^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693789797 5000000000 22277392053801 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3946623/20000000 : ℝ)^2179 ≤ (11987346088633/100000000000000 : ℝ)^1667 := by
    have hnat : (3946623 : ℕ)^2179*100000000000000^1667 ≤ 11987346088633^1667*20000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3946623 20000000 11987346088633 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321452523/2500000000 : ℝ), (2693789797/5000000000 : ℝ), (-3946623/20000000 : ℝ)] ![(43457869791759/100000000000000 : ℝ), (22277392053801/50000000000000 : ℝ), (11987346088633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321452523/2500000000 : ℝ)|^2179 ≤ (43457869791759/100000000000000 : ℝ)^1667
        have hw : |(1321452523/2500000000 : ℝ)|=(1321452523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693789797/5000000000 : ℝ)|^2179 ≤ (22277392053801/50000000000000 : ℝ)^1667
        have hw : |(2693789797/5000000000 : ℝ)|=(2693789797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3946623/20000000 : ℝ)|^2179 ≤ (11987346088633/100000000000000 : ℝ)^1667
        have hw : |(-3946623/20000000 : ℝ)|=(3946623/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_box_3 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (222956159/500000000 : ℝ)*x 0 + (2121245407/5000000000 : ℝ)*x 1 + (4242491523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (222956159/500000000 : ℝ)^2179 ≤ (34795289357701/100000000000000 : ℝ)^1667 := by
    have hnat : (222956159 : ℕ)^2179*100000000000000^1667 ≤ 34795289357701^1667*500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222956159 500000000 34795289357701 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2121245407/5000000000 : ℝ)^2179 ≤ (3260235175223/10000000000000 : ℝ)^1667 := by
    have hnat : (2121245407 : ℕ)^2179*10000000000000^1667 ≤ 3260235175223^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121245407 5000000000 3260235175223 10000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4242491523/10000000000 : ℝ)^2179 ≤ (3260235887413/10000000000000 : ℝ)^1667 := by
    have hnat : (4242491523 : ℕ)^2179*10000000000000^1667 ≤ 3260235887413^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242491523 10000000000 3260235887413 10000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(222956159/500000000 : ℝ), (2121245407/5000000000 : ℝ), (4242491523/10000000000 : ℝ)] ![(34795289357701/100000000000000 : ℝ), (3260235175223/10000000000000 : ℝ), (3260235887413/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(222956159/500000000 : ℝ)|^2179 ≤ (34795289357701/100000000000000 : ℝ)^1667
        have hw : |(222956159/500000000 : ℝ)|=(222956159/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2121245407/5000000000 : ℝ)|^2179 ≤ (3260235175223/10000000000000 : ℝ)^1667
        have hw : |(2121245407/5000000000 : ℝ)|=(2121245407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4242491523/10000000000 : ℝ)|^2179 ≤ (3260235887413/10000000000000 : ℝ)^1667
        have hw : |(4242491523/10000000000 : ℝ)|=(4242491523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_box_4 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2162240801/10000000000 : ℝ)*x 0 + (5266031249/10000000000 : ℝ)*x 1 + (658253929/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162240801/10000000000 : ℝ)^2179 ≤ (2701826367911/20000000000000 : ℝ)^1667 := by
    have hnat : (2162240801 : ℕ)^2179*20000000000000^1667 ≤ 2701826367911^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162240801 10000000000 2701826367911 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266031249/10000000000 : ℝ)^2179 ≤ (43245433093683/100000000000000 : ℝ)^1667 := by
    have hnat : (5266031249 : ℕ)^2179*100000000000000^1667 ≤ 43245433093683^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266031249 10000000000 43245433093683 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658253929/1250000000 : ℝ)^2179 ≤ (43245435058081/100000000000000 : ℝ)^1667 := by
    have hnat : (658253929 : ℕ)^2179*100000000000000^1667 ≤ 43245435058081^1667*1250000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658253929 1250000000 43245435058081 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2162240801/10000000000 : ℝ), (5266031249/10000000000 : ℝ), (658253929/1250000000 : ℝ)] ![(2701826367911/20000000000000 : ℝ), (43245433093683/100000000000000 : ℝ), (43245435058081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2162240801/10000000000 : ℝ)|^2179 ≤ (2701826367911/20000000000000 : ℝ)^1667
        have hw : |(-2162240801/10000000000 : ℝ)|=(2162240801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266031249/10000000000 : ℝ)|^2179 ≤ (43245433093683/100000000000000 : ℝ)^1667
        have hw : |(5266031249/10000000000 : ℝ)|=(5266031249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658253929/1250000000 : ℝ)|^2179 ≤ (43245435058081/100000000000000 : ℝ)^1667
        have hw : |(658253929/1250000000 : ℝ)|=(658253929/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_box_5 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1342745993/2500000000 : ℝ)*x 0 + (-126403759/625000000 : ℝ)*x 1 + (5266031151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342745993/2500000000 : ℝ)^2179 ≤ (44375471769967/100000000000000 : ℝ)^1667 := by
    have hnat : (1342745993 : ℕ)^2179*100000000000000^1667 ≤ 44375471769967^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342745993 2500000000 44375471769967 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126403759/625000000 : ℝ)^2179 ≤ (12379096185711/100000000000000 : ℝ)^1667 := by
    have hnat : (126403759 : ℕ)^2179*100000000000000^1667 ≤ 12379096185711^1667*625000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126403759 625000000 12379096185711 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266031151/10000000000 : ℝ)^2179 ≤ (4324543204171/10000000000000 : ℝ)^1667 := by
    have hnat : (5266031151 : ℕ)^2179*10000000000000^1667 ≤ 4324543204171^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266031151 10000000000 4324543204171 10000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342745993/2500000000 : ℝ), (-126403759/625000000 : ℝ), (5266031151/10000000000 : ℝ)] ![(44375471769967/100000000000000 : ℝ), (12379096185711/100000000000000 : ℝ), (4324543204171/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342745993/2500000000 : ℝ)|^2179 ≤ (44375471769967/100000000000000 : ℝ)^1667
        have hw : |(1342745993/2500000000 : ℝ)|=(1342745993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-126403759/625000000 : ℝ)|^2179 ≤ (12379096185711/100000000000000 : ℝ)^1667
        have hw : |(-126403759/625000000 : ℝ)|=(126403759/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266031151/10000000000 : ℝ)|^2179 ≤ (4324543204171/10000000000000 : ℝ)^1667
        have hw : |(5266031151/10000000000 : ℝ)|=(5266031151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_box_6 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2685491969/5000000000 : ℝ)*x 0 + (5266031321/10000000000 : ℝ)*x 1 + (-50561499/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685491969/5000000000 : ℝ)^2179 ≤ (22187735701389/50000000000000 : ℝ)^1667 := by
    have hnat : (2685491969 : ℕ)^2179*50000000000000^1667 ≤ 22187735701389^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685491969 5000000000 22187735701389 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266031321/10000000000 : ℝ)^2179 ≤ (43245433866561/100000000000000 : ℝ)^1667 := by
    have hnat : (5266031321 : ℕ)^2179*100000000000000^1667 ≤ 43245433866561^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266031321 10000000000 43245433866561 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50561499/250000000 : ℝ)^2179 ≤ (6189547356787/50000000000000 : ℝ)^1667 := by
    have hnat : (50561499 : ℕ)^2179*50000000000000^1667 ≤ 6189547356787^1667*250000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50561499 250000000 6189547356787 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685491969/5000000000 : ℝ), (5266031321/10000000000 : ℝ), (-50561499/250000000 : ℝ)] ![(22187735701389/50000000000000 : ℝ), (43245433866561/100000000000000 : ℝ), (6189547356787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685491969/5000000000 : ℝ)|^2179 ≤ (22187735701389/50000000000000 : ℝ)^1667
        have hw : |(2685491969/5000000000 : ℝ)|=(2685491969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266031321/10000000000 : ℝ)|^2179 ≤ (43245433866561/100000000000000 : ℝ)^1667
        have hw : |(5266031321/10000000000 : ℝ)|=(5266031321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-50561499/250000000 : ℝ)|^2179 ≤ (6189547356787/50000000000000 : ℝ)^1667
        have hw : |(-50561499/250000000 : ℝ)|=(50561499/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_box_7 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4164248081/10000000000 : ℝ)*x 0 + (877975397/2000000000 : ℝ)*x 1 + (877975369/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4164248081/10000000000 : ℝ)^2179 ≤ (124291560797/390625000000 : ℝ)^1667 := by
    have hnat : (4164248081 : ℕ)^2179*390625000000^1667 ≤ 124291560797^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4164248081 10000000000 124291560797 390625000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (877975397/2000000000 : ℝ)^2179 ≤ (34090680919477/100000000000000 : ℝ)^1667 := by
    have hnat : (877975397 : ℕ)^2179*100000000000000^1667 ≤ 34090680919477^1667*2000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877975397 2000000000 34090680919477 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (877975369/2000000000 : ℝ)^2179 ≤ (34090679498349/100000000000000 : ℝ)^1667 := by
    have hnat : (877975369 : ℕ)^2179*100000000000000^1667 ≤ 34090679498349^1667*2000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877975369 2000000000 34090679498349 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4164248081/10000000000 : ℝ), (877975397/2000000000 : ℝ), (877975369/2000000000 : ℝ)] ![(124291560797/390625000000 : ℝ), (34090680919477/100000000000000 : ℝ), (34090679498349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4164248081/10000000000 : ℝ)|^2179 ≤ (124291560797/390625000000 : ℝ)^1667
        have hw : |(4164248081/10000000000 : ℝ)|=(4164248081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(877975397/2000000000 : ℝ)|^2179 ≤ (34090680919477/100000000000000 : ℝ)^1667
        have hw : |(877975397/2000000000 : ℝ)|=(877975397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(877975369/2000000000 : ℝ)|^2179 ≤ (34090679498349/100000000000000 : ℝ)^1667
        have hw : |(877975369/2000000000 : ℝ)|=(877975369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_box_8 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1046547567/5000000000 : ℝ)*x 0 + (80970283/156250000 : ℝ)*x 1 + (1350392761/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046547567/5000000000 : ℝ)^2179 ≤ (2589447182753/20000000000000 : ℝ)^1667 := by
    have hnat : (1046547567 : ℕ)^2179*20000000000000^1667 ≤ 2589447182753^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046547567 5000000000 2589447182753 20000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80970283/156250000 : ℝ)^2179 ≤ (42346673294003/100000000000000 : ℝ)^1667 := by
    have hnat : (80970283 : ℕ)^2179*100000000000000^1667 ≤ 42346673294003^1667*156250000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80970283 156250000 42346673294003 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350392761/2500000000 : ℝ)^2179 ≤ (1788243630991/4000000000000 : ℝ)^1667 := by
    have hnat : (1350392761 : ℕ)^2179*4000000000000^1667 ≤ 1788243630991^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350392761 2500000000 1788243630991 4000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1046547567/5000000000 : ℝ), (80970283/156250000 : ℝ), (1350392761/2500000000 : ℝ)] ![(2589447182753/20000000000000 : ℝ), (42346673294003/100000000000000 : ℝ), (1788243630991/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1046547567/5000000000 : ℝ)|^2179 ≤ (2589447182753/20000000000000 : ℝ)^1667
        have hw : |(-1046547567/5000000000 : ℝ)|=(1046547567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80970283/156250000 : ℝ)|^2179 ≤ (42346673294003/100000000000000 : ℝ)^1667
        have hw : |(80970283/156250000 : ℝ)|=(80970283/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350392761/2500000000 : ℝ)|^2179 ≤ (1788243630991/4000000000000 : ℝ)^1667
        have hw : |(1350392761/2500000000 : ℝ)|=(1350392761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_box_9 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2638000539/5000000000 : ℝ)*x 0 + (-983762769/5000000000 : ℝ)*x 1 + (5401571181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638000539/5000000000 : ℝ)^2179 ≤ (5419060561769/12500000000000 : ℝ)^1667 := by
    have hnat : (2638000539 : ℕ)^2179*12500000000000^1667 ≤ 5419060561769^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638000539 5000000000 5419060561769 12500000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (983762769/5000000000 : ℝ)^2179 ≤ (186584738037/1562500000000 : ℝ)^1667 := by
    have hnat : (983762769 : ℕ)^2179*1562500000000^1667 ≤ 186584738037^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983762769 5000000000 186584738037 1562500000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401571181/10000000000 : ℝ)^2179 ≤ (22353046128457/50000000000000 : ℝ)^1667 := by
    have hnat : (5401571181 : ℕ)^2179*50000000000000^1667 ≤ 22353046128457^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401571181 10000000000 22353046128457 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638000539/5000000000 : ℝ), (-983762769/5000000000 : ℝ), (5401571181/10000000000 : ℝ)] ![(5419060561769/12500000000000 : ℝ), (186584738037/1562500000000 : ℝ), (22353046128457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638000539/5000000000 : ℝ)|^2179 ≤ (5419060561769/12500000000000 : ℝ)^1667
        have hw : |(2638000539/5000000000 : ℝ)|=(2638000539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-983762769/5000000000 : ℝ)|^2179 ≤ (186584738037/1562500000000 : ℝ)^1667
        have hw : |(-983762769/5000000000 : ℝ)|=(983762769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401571181/10000000000 : ℝ)|^2179 ≤ (22353046128457/50000000000000 : ℝ)^1667
        have hw : |(5401571181/10000000000 : ℝ)|=(5401571181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_box_10 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5276001221/10000000000 : ℝ)*x 0 + (337598197/625000000 : ℝ)*x 1 + (-245940673/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276001221/10000000000 : ℝ)^2179 ≤ (21676243015033/50000000000000 : ℝ)^1667 := by
    have hnat : (5276001221 : ℕ)^2179*50000000000000^1667 ≤ 21676243015033^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276001221 10000000000 21676243015033 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337598197/625000000 : ℝ)^2179 ≤ (5588261492897/12500000000000 : ℝ)^1667 := by
    have hnat : (337598197 : ℕ)^2179*12500000000000^1667 ≤ 5588261492897^1667*625000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337598197 625000000 5588261492897 12500000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245940673/1250000000 : ℝ)^2179 ≤ (1194142201263/10000000000000 : ℝ)^1667 := by
    have hnat : (245940673 : ℕ)^2179*10000000000000^1667 ≤ 1194142201263^1667*1250000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245940673 1250000000 1194142201263 10000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276001221/10000000000 : ℝ), (337598197/625000000 : ℝ), (-245940673/1250000000 : ℝ)] ![(21676243015033/50000000000000 : ℝ), (5588261492897/12500000000000 : ℝ), (1194142201263/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276001221/10000000000 : ℝ)|^2179 ≤ (21676243015033/50000000000000 : ℝ)^1667
        have hw : |(5276001221/10000000000 : ℝ)|=(5276001221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337598197/625000000 : ℝ)|^2179 ≤ (5588261492897/12500000000000 : ℝ)^1667
        have hw : |(337598197/625000000 : ℝ)|=(337598197/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-245940673/1250000000 : ℝ)|^2179 ≤ (1194142201263/10000000000000 : ℝ)^1667
        have hw : |(-245940673/1250000000 : ℝ)|=(245940673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_box_11 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4492509869/10000000000 : ℝ)*x 0 + (1056377719/2500000000 : ℝ)*x 1 + (2112755179/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4492509869/10000000000 : ℝ)^2179 ≤ (35136218540051/100000000000000 : ℝ)^1667 := by
    have hnat : (4492509869 : ℕ)^2179*100000000000000^1667 ≤ 35136218540051^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492509869 10000000000 35136218540051 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056377719/2500000000 : ℝ)^2179 ≤ (32431893321733/100000000000000 : ℝ)^1667 := by
    have hnat : (1056377719 : ℕ)^2179*100000000000000^1667 ≤ 32431893321733^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056377719 2500000000 32431893321733 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2112755179/5000000000 : ℝ)^2179 ≤ (32431888124831/100000000000000 : ℝ)^1667 := by
    have hnat : (2112755179 : ℕ)^2179*100000000000000^1667 ≤ 32431888124831^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112755179 5000000000 32431888124831 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4492509869/10000000000 : ℝ), (1056377719/2500000000 : ℝ), (2112755179/5000000000 : ℝ)] ![(35136218540051/100000000000000 : ℝ), (32431893321733/100000000000000 : ℝ), (32431888124831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4492509869/10000000000 : ℝ)|^2179 ≤ (35136218540051/100000000000000 : ℝ)^1667
        have hw : |(4492509869/10000000000 : ℝ)|=(4492509869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056377719/2500000000 : ℝ)|^2179 ≤ (32431893321733/100000000000000 : ℝ)^1667
        have hw : |(1056377719/2500000000 : ℝ)|=(1056377719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2112755179/5000000000 : ℝ)|^2179 ≤ (32431888124831/100000000000000 : ℝ)^1667
        have hw : |(2112755179/5000000000 : ℝ)|=(2112755179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_box_12 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1903006803/10000000000 : ℝ)*x 0 + (5469426941/10000000000 : ℝ)*x 1 + (131373063/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1903006803/10000000000 : ℝ)^2179 ≤ (5716085025607/50000000000000 : ℝ)^1667 := by
    have hnat : (1903006803 : ℕ)^2179*50000000000000^1667 ≤ 5716085025607^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903006803 10000000000 5716085025607 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5469426941/10000000000 : ℝ)^2179 ≤ (1817664156839/4000000000000 : ℝ)^1667 := by
    have hnat : (5469426941 : ℕ)^2179*4000000000000^1667 ≤ 1817664156839^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469426941 10000000000 1817664156839 4000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131373063/250000000 : ℝ)^2179 ≤ (43126226016963/100000000000000 : ℝ)^1667 := by
    have hnat : (131373063 : ℕ)^2179*100000000000000^1667 ≤ 43126226016963^1667*250000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131373063 250000000 43126226016963 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1903006803/10000000000 : ℝ), (5469426941/10000000000 : ℝ), (131373063/250000000 : ℝ)] ![(5716085025607/50000000000000 : ℝ), (1817664156839/4000000000000 : ℝ), (43126226016963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1903006803/10000000000 : ℝ)|^2179 ≤ (5716085025607/50000000000000 : ℝ)^1667
        have hw : |(-1903006803/10000000000 : ℝ)|=(1903006803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5469426941/10000000000 : ℝ)|^2179 ≤ (1817664156839/4000000000000 : ℝ)^1667
        have hw : |(5469426941/10000000000 : ℝ)|=(5469426941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131373063/250000000 : ℝ)|^2179 ≤ (43126226016963/100000000000000 : ℝ)^1667
        have hw : |(131373063/250000000 : ℝ)|=(131373063/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_box_13 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (537876667/1000000000 : ℝ)*x 0 + (-2026850707/10000000000 : ℝ)*x 1 + (5254922259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537876667/1000000000 : ℝ)^2179 ≤ (22229770544963/50000000000000 : ℝ)^1667 := by
    have hnat : (537876667 : ℕ)^2179*50000000000000^1667 ≤ 22229770544963^1667*1000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537876667 1000000000 22229770544963 50000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2026850707/10000000000 : ℝ)^2179 ≤ (12414235679377/100000000000000 : ℝ)^1667 := by
    have hnat : (2026850707 : ℕ)^2179*100000000000000^1667 ≤ 12414235679377^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026850707 10000000000 12414235679377 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254922259/10000000000 : ℝ)^2179 ≤ (43126223217097/100000000000000 : ℝ)^1667 := by
    have hnat : (5254922259 : ℕ)^2179*100000000000000^1667 ≤ 43126223217097^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254922259 10000000000 43126223217097 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537876667/1000000000 : ℝ), (-2026850707/10000000000 : ℝ), (5254922259/10000000000 : ℝ)] ![(22229770544963/50000000000000 : ℝ), (12414235679377/100000000000000 : ℝ), (43126223217097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537876667/1000000000 : ℝ)|^2179 ≤ (22229770544963/50000000000000 : ℝ)^1667
        have hw : |(537876667/1000000000 : ℝ)|=(537876667/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2026850707/10000000000 : ℝ)|^2179 ≤ (12414235679377/100000000000000 : ℝ)^1667
        have hw : |(-2026850707/10000000000 : ℝ)|=(2026850707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254922259/10000000000 : ℝ)|^2179 ≤ (43126223217097/100000000000000 : ℝ)^1667
        have hw : |(5254922259/10000000000 : ℝ)|=(5254922259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_box_14 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2689383299/5000000000 : ℝ)*x 0 + (5254922477/10000000000 : ℝ)*x 1 + (-126678157/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689383299/5000000000 : ℝ)^2179 ≤ (44459540312003/100000000000000 : ℝ)^1667 := by
    have hnat : (2689383299 : ℕ)^2179*100000000000000^1667 ≤ 44459540312003^1667*5000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689383299 5000000000 44459540312003 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254922477/10000000000 : ℝ)^2179 ≤ (43126225555683/100000000000000 : ℝ)^1667 := by
    have hnat : (5254922477 : ℕ)^2179*100000000000000^1667 ≤ 43126225555683^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254922477 10000000000 43126225555683 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126678157/625000000 : ℝ)^2179 ≤ (775889632387/6250000000000 : ℝ)^1667 := by
    have hnat : (126678157 : ℕ)^2179*6250000000000^1667 ≤ 775889632387^1667*625000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126678157 625000000 775889632387 6250000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689383299/5000000000 : ℝ), (5254922477/10000000000 : ℝ), (-126678157/625000000 : ℝ)] ![(44459540312003/100000000000000 : ℝ), (43126225555683/100000000000000 : ℝ), (775889632387/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689383299/5000000000 : ℝ)|^2179 ≤ (44459540312003/100000000000000 : ℝ)^1667
        have hw : |(2689383299/5000000000 : ℝ)|=(2689383299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254922477/10000000000 : ℝ)|^2179 ≤ (43126225555683/100000000000000 : ℝ)^1667
        have hw : |(5254922477/10000000000 : ℝ)|=(5254922477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-126678157/625000000 : ℝ)|^2179 ≤ (775889632387/6250000000000 : ℝ)^1667
        have hw : |(-126678157/625000000 : ℝ)|=(126678157/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1398_box_15 (p : ℝ) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4136848361/10000000000 : ℝ)*x 0 + (275208553/625000000 : ℝ)*x 1 + (1100834071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4136848361/10000000000 : ℝ)^2179 ≤ (788631389869/2500000000000 : ℝ)^1667 := by
    have hnat : (4136848361 : ℕ)^2179*2500000000000^1667 ≤ 788631389869^1667*10000000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4136848361 10000000000 788631389869 2500000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (275208553/625000000 : ℝ)^2179 ≤ (267401367647/781250000000 : ℝ)^1667 := by
    have hnat : (275208553 : ℕ)^2179*781250000000^1667 ≤ 267401367647^1667*625000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275208553 625000000 267401367647 781250000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100834071/2500000000 : ℝ)^2179 ≤ (34227369328317/100000000000000 : ℝ)^1667 := by
    have hnat : (1100834071 : ℕ)^2179*100000000000000^1667 ≤ 34227369328317^1667*2500000000^2179 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100834071 2500000000 34227369328317 100000000000000 2179 1667 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2179/512 : ℝ)) 2179 1667 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4136848361/10000000000 : ℝ), (275208553/625000000 : ℝ), (1100834071/2500000000 : ℝ)] ![(788631389869/2500000000000 : ℝ), (267401367647/781250000000 : ℝ), (34227369328317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4136848361/10000000000 : ℝ)|^2179 ≤ (788631389869/2500000000000 : ℝ)^1667
        have hw : |(4136848361/10000000000 : ℝ)|=(4136848361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(275208553/625000000 : ℝ)|^2179 ≤ (267401367647/781250000000 : ℝ)^1667
        have hw : |(275208553/625000000 : ℝ)|=(275208553/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1100834071/2500000000 : ℝ)|^2179 ≤ (34227369328317/100000000000000 : ℝ)^1667
        have hw : |(1100834071/2500000000 : ℝ)|=(1100834071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1398_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (737/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62881/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59051/100000 : ℝ) ∧ (20069/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10571/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (737/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2819/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (737/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2819/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (737/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2819/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (737/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2819/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (737/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2819/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (737/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2819/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2819/25000 : ℝ) ^ (4357/1024 : ℝ) ≤ (4634478703845427/50000000000000000000 : ℝ) := by
    have hpowers : (2819/25000 : ℝ)^4357 ≤ (4634478703845427/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2819 : ℕ)^4357*50000000000000000000^1024 ≤ 4634478703845427^1024*25000^4357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2819 25000 4634478703845427 50000000000000000000 4357 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2819/25000 : ℝ)) (X := (4634478703845427/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (737/5000 : ℝ) ^ (4357/1024 : ℝ) ≤ (7244263566341411/25000000000000000000 : ℝ) := by
    have hpowers : (737/5000 : ℝ)^4357 ≤ (7244263566341411/25000000000000000000 : ℝ)^1024 := by
      have hnat : (737 : ℕ)^4357*25000000000000000000^1024 ≤ 7244263566341411^1024*5000^4357 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        737 5000 7244263566341411 25000000000000000000 4357 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (737/5000 : ℝ)) (X := (7244263566341411/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004634478703845427/25000000000000000000 : ℝ) ≤ (1250054456847989/1250000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (25004634478703845427/25000000000000000000 : ℝ)^1024 ≤ (1250054456847989/1250000000000000 : ℝ)^4357 := by
      have hnat : (25004634478703845427 : ℕ)^1024*1250000000000000^4357 ≤ 1250054456847989^4357*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004634478703845427 25000000000000000000 1250054456847989 1250000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250054456847989/1250000000000000 : ℝ)) (X := (25004634478703845427/25000000000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019123005836528249/50000000000000000000 : ℝ) ≤ (10000898741980589/10000000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (50019123005836528249/50000000000000000000 : ℝ)^1024 ≤ (10000898741980589/10000000000000000 : ℝ)^4357 := by
      have hnat : (50019123005836528249 : ℕ)^1024*10000000000000000^4357 ≤ 10000898741980589^4357*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019123005836528249 50000000000000000000 10000898741980589 10000000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000898741980589/10000000000000000 : ℝ)) (X := (50019123005836528249/50000000000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507244263566341411/12500000000000000000 : ℝ) ≤ (5000680914588633/5000000000000000 : ℝ) ^ (4357/1024 : ℝ) := by
    have hpowers : (12507244263566341411/12500000000000000000 : ℝ)^1024 ≤ (5000680914588633/5000000000000000 : ℝ)^4357 := by
      have hnat : (12507244263566341411 : ℕ)^1024*5000000000000000^4357 ≤ 5000680914588633^4357*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507244263566341411 12500000000000000000 5000680914588633 5000000000000000 1024 4357 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000680914588633/5000000000000000 : ℝ)) (X := (12507244263566341411/12500000000000000000 : ℝ)) (by norm_num) 4357 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4634478703845427/50000000000000000000 : ℝ) ≤ ((4328883195714001433/4330000000000000000 : ℝ)+2*(463087196677/346400000000000 : ℝ)*(2819/25000 : ℝ))^(4357/1024 : ℝ) := by
    rw [show (4328883195714001433/4330000000000000000 : ℝ)+2*(463087196677/346400000000000 : ℝ)*(2819/25000 : ℝ)=(1250054456847989/1250000000000000 : ℝ) by norm_num, show 1+2*(4634478703845427/50000000000000000000 : ℝ)=(25004634478703845427/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7244263566341411/25000000000000000000 : ℝ)+(4634478703845427/50000000000000000000 : ℝ) ≤ ((4328883195714001433/4330000000000000000 : ℝ)+(463087196677/346400000000000 : ℝ)*((737/5000 : ℝ)+(2819/25000 : ℝ)))^(4357/1024 : ℝ) := by
    rw [show (4328883195714001433/4330000000000000000 : ℝ)+(463087196677/346400000000000 : ℝ)*((737/5000 : ℝ)+(2819/25000 : ℝ))=(10000898741980589/10000000000000000 : ℝ) by norm_num, show 1+(7244263566341411/25000000000000000000 : ℝ)+(4634478703845427/50000000000000000000 : ℝ)=(50019123005836528249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7244263566341411/25000000000000000000 : ℝ) ≤ ((4328883195714001433/4330000000000000000 : ℝ)+2*(463087196677/346400000000000 : ℝ)*(737/5000 : ℝ))^(4357/1024 : ℝ) := by
    rw [show (4328883195714001433/4330000000000000000 : ℝ)+2*(463087196677/346400000000000 : ℝ)*(737/5000 : ℝ)=(5000680914588633/5000000000000000 : ℝ) by norm_num, show 1+2*(7244263566341411/25000000000000000000 : ℝ)=(12507244263566341411/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4328883195714001433/4330000000000000000 : ℝ)*(X 1 0+X 2 0)+(463087196677/346400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (2819/25000 : ℝ)) (hi := (737/5000 : ℝ)) (c := (4328883195714001433/4330000000000000000 : ℝ)) (alpha := (463087196677/346400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4328883195714001433/4330000000000000000 : ℝ)*(X 0 1+X 2 1)+(463087196677/346400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (2819/25000 : ℝ)) (hi := (737/5000 : ℝ)) (c := (4328883195714001433/4330000000000000000 : ℝ)) (alpha := (463087196677/346400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4328883195714001433/4330000000000000000 : ℝ)*(X 0 2+X 1 2)+(463087196677/346400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4357/1024 : ℝ)) (lo := (2819/25000 : ℝ)) (hi := (737/5000 : ℝ)) (c := (4328883195714001433/4330000000000000000 : ℝ)) (alpha := (463087196677/346400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1833627819/10000000000 : ℝ)*X 0 0+(215503161/400000000 : ℝ)*X 0 1+(5387578907/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((211432421/400000000 : ℝ)*X 1 0+(-986655697/5000000000 : ℝ)*X 1 1+(5387579241/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1321452523/2500000000 : ℝ)*X 2 0+(2693789797/5000000000 : ℝ)*X 2 1+(-3946623/20000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((222956159/500000000 : ℝ)*X 0 0+(2121245407/5000000000 : ℝ)*X 0 1+(4242491523/10000000000 : ℝ)*X 0 2+(222956159/500000000 : ℝ)*X 1 0+(2121245407/5000000000 : ℝ)*X 1 1+(4242491523/10000000000 : ℝ)*X 1 2+(222956159/500000000 : ℝ)*X 2 0+(2121245407/5000000000 : ℝ)*X 2 1+(4242491523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2162240801/10000000000 : ℝ)*X 0 0+(5266031249/10000000000 : ℝ)*X 0 1+(658253929/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1342745993/2500000000 : ℝ)*X 1 0+(-126403759/625000000 : ℝ)*X 1 1+(5266031151/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2685491969/5000000000 : ℝ)*X 2 0+(5266031321/10000000000 : ℝ)*X 2 1+(-50561499/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4164248081/10000000000 : ℝ)*X 0 0+(877975397/2000000000 : ℝ)*X 0 1+(877975369/2000000000 : ℝ)*X 0 2+(4164248081/10000000000 : ℝ)*X 1 0+(877975397/2000000000 : ℝ)*X 1 1+(877975369/2000000000 : ℝ)*X 1 2+(4164248081/10000000000 : ℝ)*X 2 0+(877975397/2000000000 : ℝ)*X 2 1+(877975369/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1046547567/5000000000 : ℝ)*X 0 0+(80970283/156250000 : ℝ)*X 0 1+(1350392761/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2638000539/5000000000 : ℝ)*X 1 0+(-983762769/5000000000 : ℝ)*X 1 1+(5401571181/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276001221/10000000000 : ℝ)*X 2 0+(337598197/625000000 : ℝ)*X 2 1+(-245940673/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4492509869/10000000000 : ℝ)*X 0 0+(1056377719/2500000000 : ℝ)*X 0 1+(2112755179/5000000000 : ℝ)*X 0 2+(4492509869/10000000000 : ℝ)*X 1 0+(1056377719/2500000000 : ℝ)*X 1 1+(2112755179/5000000000 : ℝ)*X 1 2+(4492509869/10000000000 : ℝ)*X 2 0+(1056377719/2500000000 : ℝ)*X 2 1+(2112755179/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1903006803/10000000000 : ℝ)*X 0 0+(5469426941/10000000000 : ℝ)*X 0 1+(131373063/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((537876667/1000000000 : ℝ)*X 1 0+(-2026850707/10000000000 : ℝ)*X 1 1+(5254922259/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2689383299/5000000000 : ℝ)*X 2 0+(5254922477/10000000000 : ℝ)*X 2 1+(-126678157/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4136848361/10000000000 : ℝ)*X 0 0+(275208553/625000000 : ℝ)*X 0 1+(1100834071/2500000000 : ℝ)*X 0 2+(4136848361/10000000000 : ℝ)*X 1 0+(275208553/625000000 : ℝ)*X 1 1+(1100834071/2500000000 : ℝ)*X 1 2+(4136848361/10000000000 : ℝ)*X 2 0+(275208553/625000000 : ℝ)*X 2 1+(1100834071/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1398_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62881/100000 : ℝ) ≤ (-17016615338510955425549027087199/27062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64791/2500000000000 : ℝ)*(upper1) + (56942963/100000000000000 : ℝ)*(lower2) + (9572563/100000000000000 : ℝ)*(lower3) + (718609/100000000000000 : ℝ)*(upper5) + (372861726832367/12500000000000 : ℝ)*(major0) + (372861726832367/12500000000000 : ℝ)*(major1) + (372861726832367/12500000000000 : ℝ)*(major2) + (51978963/625000000000 : ℝ)*(sp1) + (530730741/25000000000000 : ℝ)*(sp3) + (4086079783931237/100000000000000 : ℝ)*(sp4) + (408607287839761/10000000000000 : ℝ)*(sp5) + (4086081195031691/100000000000000 : ℝ)*(sp6) + (1900663960740897/100000000000000 : ℝ)*(sp7) + (705550227/50000000000000 : ℝ)*(sp12) + (1900666083663861/100000000000000 : ℝ)*(f.failure) + (4086081195031691/100000000000000 : ℝ)*(f.sum) + (6697163599911/2165000000000000000000000000 : ℝ)*base66 + (635277883314019411/54125000000000000000000000000000 : ℝ)*base67 + (177035870490394411/54125000000000000000000000000000 : ℝ)*base69 + (540666916269394411/54125000000000000000000000000000 : ℝ)*base71 + (86641361453/1082500000000000000000000000 : ℝ)*base74 + (861737854370644411/54125000000000000000000000000000 : ℝ)*base75 + (174176785887644411/54125000000000000000000000000000 : ℝ)*base77 + (488088324080019411/54125000000000000000000000000000 : ℝ)*base79 + (700740023627/1082500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (38623627/10000000000000000000000 : ℝ)*base90 + (38623627/10000000000000000000000 : ℝ)*base92 + (38623627/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59051/100000 : ℝ) ≤ (63925658376360687959492227985703/108250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70424283/100000000000000 : ℝ)*(lower1) + (67242371/50000000000000 : ℝ)*(upper2) + (3913487/100000000000000 : ℝ)*(lower4) + (3053460184834853/100000000000000 : ℝ)*(major0) + (3053460184834853/100000000000000 : ℝ)*(major1) + (3053460184834853/100000000000000 : ℝ)*(major2) + (1035400130816131/25000000000000 : ℝ)*(sp0) + (517699308840049/12500000000000 : ℝ)*(sp1) + (517698708115001/12500000000000 : ℝ)*(sp2) + (486406273111263/25000000000000 : ℝ)*(sp3) + (5574895473/50000000000000 : ℝ)*(sp5) + (1595559133/10000000000000 : ℝ)*(sp6) + (5081385717/100000000000000 : ℝ)*(sp7) + (2548623407/50000000000000 : ℝ)*(sp12) + (1945630173830769/100000000000000 : ℝ)*(f.failure) + (2070802810255669/50000000000000 : ℝ)*(f.sum) + (62345505083999/17320000000000000000000000000 : ℝ)*base66 + (2548666877052856849/433000000000000000000000000000000 : ℝ)*base67 + (3188483714506856849/433000000000000000000000000000000 : ℝ)*base69 + (1480885801886856849/433000000000000000000000000000000 : ℝ)*base71 + (65180395261839/17320000000000000000000000000 : ℝ)*base74 + (3250101879096856849/433000000000000000000000000000000 : ℝ)*base75 + (1506266437525143151/433000000000000000000000000000000 : ℝ)*base78 + (3348790859788856849/433000000000000000000000000000000 : ℝ)*base79 + (45672972097039/17320000000000000000000000000 : ℝ)*base82 + (71583217/10000000000000000000000 : ℝ)*base89 + (71583217/10000000000000000000000 : ℝ)*base91 + (71583217/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (20069/25000 : ℝ) ≤ (86901317050859041310023894403889/108250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1949511/50000000000000 : ℝ)*(upper0) + (65736563/100000000000000 : ℝ)*(upper1) + (50382293/50000000000000 : ℝ)*(upper4) + (1681500605711589/50000000000000 : ℝ)*(major0) + (1681500605711589/50000000000000 : ℝ)*(major1) + (1681500605711589/50000000000000 : ℝ)*(major2) + (96464687327/100000000000000 : ℝ)*(sp1) + (26554518283/20000000000000 : ℝ)*(sp2) + (22040165687/50000000000000 : ℝ)*(sp3) + (125680727/25000000000000 : ℝ)*(sp4) + (2278188133189727/50000000000000 : ℝ)*(sp8) + (911256060883007/20000000000000 : ℝ)*(sp9) + (4556243996510947/100000000000000 : ℝ)*(sp10) + (214282212243467/10000000000000 : ℝ)*(sp11) + (2142866202766043/100000000000000 : ℝ)*(f.failure) + (2278188384551181/50000000000000 : ℝ)*(f.sum) + (65147034586207/8660000000000000000000000000 : ℝ)*base66 + (199462500318619537/216500000000000000000000000000000 : ℝ)*base67 + (727285950151619537/216500000000000000000000000000000 : ℝ)*base69 + (421225605854880463/216500000000000000000000000000000 : ℝ)*base72 + (17141668571673/8660000000000000000000000000 : ℝ)*base73 + (1146709038136619537/216500000000000000000000000000000 : ℝ)*base75 + (811207502277880463/216500000000000000000000000000000 : ℝ)*base78 + (6877222379537619537/216500000000000000000000000000000 : ℝ)*base79 + (13791966490513/8660000000000000000000000000 : ℝ)*base81 + (90568101/10000000000000000000000 : ℝ)*base90 + (90568101/10000000000000000000000 : ℝ)*base92 + (90568101/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-10571/12500 : ℝ) ≤ (-45770908054009754648192801927127/54125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52991107/25000000000000 : ℝ)*(lower0) + (124005447/100000000000000 : ℝ)*(lower1) + (33450081/50000000000000 : ℝ)*(lower2) + (850028947090591/25000000000000 : ℝ)*(major0) + (850028947090591/25000000000000 : ℝ)*(major1) + (850028947090591/25000000000000 : ℝ)*(major2) + (281765463/12500000000000 : ℝ)*(sp0) + (3876167851/1562500000000 : ℝ)*(sp5) + (59493286091/50000000000000 : ℝ)*(sp6) + (28742465133/50000000000000 : ℝ)*(sp7) + (4661902528679899/100000000000000 : ℝ)*(sp12) + (4661656708061139/100000000000000 : ℝ)*(sp13) + (4661785796231421/100000000000000 : ℝ)*(sp14) + (2166457705021031/100000000000000 : ℝ)*(sp15) + (1083257594975649/50000000000000 : ℝ)*(f.failure) + (4661904782803603/100000000000000 : ℝ)*(f.sum) + (24012290772987/4330000000000000000000000000 : ℝ)*base65 + (1326190458710904403/108250000000000000000000000000000 : ℝ)*base67 + (1305539527729654403/108250000000000000000000000000000 : ℝ)*base69 + (908759188262404403/108250000000000000000000000000000 : ℝ)*base71 + (14786260421137/4330000000000000000000000000 : ℝ)*base73 + (1605938467559404403/108250000000000000000000000000000 : ℝ)*base75 + (713339323890404403/108250000000000000000000000000000 : ℝ)*base77 + (2109444734600904403/108250000000000000000000000000000 : ℝ)*base79 + (31697243888447/4330000000000000000000000000 : ℝ)*base81 + (3841057/5000000000000000000000 : ℝ)*base89 + (3841057/5000000000000000000000 : ℝ)*base91 + (3841057/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1398_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (737/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62881/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59051/100000 : ℝ) else (20069/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10571/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1398_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1398_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (737/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62881/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59051/100000 : ℝ) else (20069/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10571/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1398_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4357/1024 : ℝ) ≤ p) (hpb : p ≤ (2179/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156939393/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (737/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62881/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59051/100000 : ℝ) else (20069/25000 : ℝ) ≤ X j i ∧ X j i ≤ (10571/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1398_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

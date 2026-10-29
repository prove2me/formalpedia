-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1530_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:04:53.658449+00:00
-- url     : https://prove2.me/submissions/793b1295-367c-4805-a906-15d51336598f

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
theorem support_rectangle_w1530_s3_0 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-460336691/2500000000 : ℝ)*x 0 + (1358391851/2500000000 : ℝ)*x 1 + (521609583/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (460336691/2500000000 : ℝ)^4557 ≤ (5637849343963/50000000000000 : ℝ)^3533 := by
    have hnat : (460336691 : ℕ)^4557*50000000000000^3533 ≤ 5637849343963^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460336691 2500000000 5637849343963 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358391851/2500000000 : ℝ)^4557 ≤ (11382626223669/25000000000000 : ℝ)^3533 := by
    have hnat : (1358391851 : ℕ)^4557*25000000000000^3533 ≤ 11382626223669^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358391851 2500000000 11382626223669 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521609583/1000000000 : ℝ)^4557 ≤ (53992245501/125000000000 : ℝ)^3533 := by
    have hnat : (521609583 : ℕ)^4557*125000000000^3533 ≤ 53992245501^3533*1000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521609583 1000000000 53992245501 125000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-460336691/2500000000 : ℝ), (1358391851/2500000000 : ℝ), (521609583/1000000000 : ℝ)] ![(5637849343963/50000000000000 : ℝ), (11382626223669/25000000000000 : ℝ), (53992245501/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-460336691/2500000000 : ℝ)|^4557 ≤ (5637849343963/50000000000000 : ℝ)^3533
        have hw : |(-460336691/2500000000 : ℝ)|=(460336691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358391851/2500000000 : ℝ)|^4557 ≤ (11382626223669/25000000000000 : ℝ)^3533
        have hw : |(1358391851/2500000000 : ℝ)|=(1358391851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521609583/1000000000 : ℝ)|^4557 ≤ (53992245501/125000000000 : ℝ)^3533
        have hw : |(521609583/1000000000 : ℝ)|=(521609583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s3_1 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351272139/10000000000 : ℝ)*x 0 + (-488186931/2500000000 : ℝ)*x 1 + (326005981/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351272139/10000000000 : ℝ)^4557 ≤ (44643001719637/100000000000000 : ℝ)^3533 := by
    have hnat : (5351272139 : ℕ)^4557*100000000000000^3533 ≤ 44643001719637^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351272139 10000000000 44643001719637 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (488186931/2500000000 : ℝ)^4557 ≤ (2432640657319/20000000000000 : ℝ)^3533 := by
    have hnat : (488186931 : ℕ)^4557*20000000000000^3533 ≤ 2432640657319^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488186931 2500000000 2432640657319 20000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326005981/625000000 : ℝ)^4557 ≤ (43193794969549/100000000000000 : ℝ)^3533 := by
    have hnat : (326005981 : ℕ)^4557*100000000000000^3533 ≤ 43193794969549^3533*625000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326005981 625000000 43193794969549 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351272139/10000000000 : ℝ), (-488186931/2500000000 : ℝ), (326005981/625000000 : ℝ)] ![(44643001719637/100000000000000 : ℝ), (2432640657319/20000000000000 : ℝ), (43193794969549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351272139/10000000000 : ℝ)|^4557 ≤ (44643001719637/100000000000000 : ℝ)^3533
        have hw : |(5351272139/10000000000 : ℝ)|=(5351272139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-488186931/2500000000 : ℝ)|^4557 ≤ (2432640657319/20000000000000 : ℝ)^3533
        have hw : |(-488186931/2500000000 : ℝ)|=(488186931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326005981/625000000 : ℝ)|^4557 ≤ (43193794969549/100000000000000 : ℝ)^3533
        have hw : |(326005981/625000000 : ℝ)|=(326005981/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s3_2 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535127237/1000000000 : ℝ)*x 0 + (1304023843/2500000000 : ℝ)*x 1 + (-976373923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535127237/1000000000 : ℝ)^4557 ≤ (44643004205309/100000000000000 : ℝ)^3533 := by
    have hnat : (535127237 : ℕ)^4557*100000000000000^3533 ≤ 44643004205309^3533*1000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535127237 1000000000 44643004205309 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304023843/2500000000 : ℝ)^4557 ≤ (4319379150891/10000000000000 : ℝ)^3533 := by
    have hnat : (1304023843 : ℕ)^4557*10000000000000^3533 ≤ 4319379150891^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304023843 2500000000 4319379150891 10000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (976373923/5000000000 : ℝ)^4557 ≤ (2432640853351/20000000000000 : ℝ)^3533 := by
    have hnat : (976373923 : ℕ)^4557*20000000000000^3533 ≤ 2432640853351^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976373923 5000000000 2432640853351 20000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535127237/1000000000 : ℝ), (1304023843/2500000000 : ℝ), (-976373923/5000000000 : ℝ)] ![(44643004205309/100000000000000 : ℝ), (4319379150891/10000000000000 : ℝ), (2432640853351/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535127237/1000000000 : ℝ)|^4557 ≤ (44643004205309/100000000000000 : ℝ)^3533
        have hw : |(535127237/1000000000 : ℝ)|=(535127237/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304023843/2500000000 : ℝ)|^4557 ≤ (4319379150891/10000000000000 : ℝ)^3533
        have hw : |(1304023843/2500000000 : ℝ)|=(1304023843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-976373923/5000000000 : ℝ)|^4557 ≤ (2432640853351/20000000000000 : ℝ)^3533
        have hw : |(-976373923/5000000000 : ℝ)|=(976373923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s3_3 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2130604879/5000000000 : ℝ)*x 0 + (1004407631/2500000000 : ℝ)*x 1 + (903405571/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130604879/5000000000 : ℝ)^4557 ≤ (33278000755623/100000000000000 : ℝ)^3533 := by
    have hnat : (2130604879 : ℕ)^4557*100000000000000^3533 ≤ 33278000755623^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130604879 5000000000 33278000755623 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1004407631/2500000000 : ℝ)^4557 ≤ (308450293169/1000000000000 : ℝ)^3533 := by
    have hnat : (1004407631 : ℕ)^4557*1000000000000^3533 ≤ 308450293169^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004407631 2500000000 308450293169 1000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903405571/2000000000 : ℝ)^4557 ≤ (8969242476429/25000000000000 : ℝ)^3533 := by
    have hnat : (903405571 : ℕ)^4557*25000000000000^3533 ≤ 8969242476429^3533*2000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903405571 2000000000 8969242476429 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2130604879/5000000000 : ℝ), (1004407631/2500000000 : ℝ), (903405571/2000000000 : ℝ)] ![(33278000755623/100000000000000 : ℝ), (308450293169/1000000000000 : ℝ), (8969242476429/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2130604879/5000000000 : ℝ)|^4557 ≤ (33278000755623/100000000000000 : ℝ)^3533
        have hw : |(2130604879/5000000000 : ℝ)|=(2130604879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1004407631/2500000000 : ℝ)|^4557 ≤ (308450293169/1000000000000 : ℝ)^3533
        have hw : |(1004407631/2500000000 : ℝ)|=(1004407631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903405571/2000000000 : ℝ)|^4557 ≤ (8969242476429/25000000000000 : ℝ)^3533
        have hw : |(903405571/2000000000 : ℝ)|=(903405571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s3_4 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-368275483/2000000000 : ℝ)*x 0 + (521724559/1000000000 : ℝ)*x 1 + (42440693/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (368275483/2000000000 : ℝ)^4557 ≤ (281898519617/2500000000000 : ℝ)^3533 := by
    have hnat : (368275483 : ℕ)^4557*2500000000000^3533 ≤ 281898519617^3533*2000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368275483 2000000000 281898519617 2500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521724559/1000000000 : ℝ)^4557 ≤ (43206077359589/100000000000000 : ℝ)^3533 := by
    have hnat : (521724559 : ℕ)^4557*100000000000000^3533 ≤ 43206077359589^3533*1000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521724559 1000000000 43206077359589 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42440693/78125000 : ℝ)^4557 ≤ (355609233101/781250000000 : ℝ)^3533 := by
    have hnat : (42440693 : ℕ)^4557*781250000000^3533 ≤ 355609233101^3533*78125000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42440693 78125000 355609233101 781250000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-368275483/2000000000 : ℝ), (521724559/1000000000 : ℝ), (42440693/78125000 : ℝ)] ![(281898519617/2500000000000 : ℝ), (43206077359589/100000000000000 : ℝ), (355609233101/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-368275483/2000000000 : ℝ)|^4557 ≤ (281898519617/2500000000000 : ℝ)^3533
        have hw : |(-368275483/2000000000 : ℝ)|=(368275483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521724559/1000000000 : ℝ)|^4557 ≤ (43206077359589/100000000000000 : ℝ)^3533
        have hw : |(521724559/1000000000 : ℝ)|=(521724559/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42440693/78125000 : ℝ)|^4557 ≤ (355609233101/781250000000 : ℝ)^3533
        have hw : |(42440693/78125000 : ℝ)|=(42440693/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s3_5 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294032123/10000000000 : ℝ)*x 0 + (-13891477/80000000 : ℝ)*x 1 + (5432408707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294032123/10000000000 : ℝ)^4557 ≤ (22014014368579/50000000000000 : ℝ)^3533 := by
    have hnat : (5294032123 : ℕ)^4557*50000000000000^3533 ≤ 22014014368579^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294032123 10000000000 22014014368579 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13891477/80000000 : ℝ)^4557 ≤ (10453989377003/100000000000000 : ℝ)^3533 := by
    have hnat : (13891477 : ℕ)^4557*100000000000000^3533 ≤ 10453989377003^3533*80000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13891477 80000000 10453989377003 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432408707/10000000000 : ℝ)^4557 ≤ (910359637387/2000000000000 : ℝ)^3533 := by
    have hnat : (5432408707 : ℕ)^4557*2000000000000^3533 ≤ 910359637387^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432408707 10000000000 910359637387 2000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294032123/10000000000 : ℝ), (-13891477/80000000 : ℝ), (5432408707/10000000000 : ℝ)] ![(22014014368579/50000000000000 : ℝ), (10453989377003/100000000000000 : ℝ), (910359637387/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294032123/10000000000 : ℝ)|^4557 ≤ (22014014368579/50000000000000 : ℝ)^3533
        have hw : |(5294032123/10000000000 : ℝ)|=(5294032123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13891477/80000000 : ℝ)|^4557 ≤ (10453989377003/100000000000000 : ℝ)^3533
        have hw : |(-13891477/80000000 : ℝ)|=(13891477/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432408707/10000000000 : ℝ)|^4557 ≤ (910359637387/2000000000000 : ℝ)^3533
        have hw : |(5432408707/10000000000 : ℝ)|=(5432408707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s3_6 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294032127/10000000000 : ℝ)*x 0 + (2716204351/5000000000 : ℝ)*x 1 + (-434108657/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294032127/10000000000 : ℝ)^4557 ≤ (22014014390033/50000000000000 : ℝ)^3533 := by
    have hnat : (5294032127 : ℕ)^4557*50000000000000^3533 ≤ 22014014390033^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294032127 10000000000 22014014390033 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716204351/5000000000 : ℝ)^4557 ≤ (45517981815313/100000000000000 : ℝ)^3533 := by
    have hnat : (2716204351 : ℕ)^4557*100000000000000^3533 ≤ 45517981815313^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716204351 5000000000 45517981815313 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434108657/2500000000 : ℝ)^4557 ≤ (10453989400299/100000000000000 : ℝ)^3533 := by
    have hnat : (434108657 : ℕ)^4557*100000000000000^3533 ≤ 10453989400299^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434108657 2500000000 10453989400299 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294032127/10000000000 : ℝ), (2716204351/5000000000 : ℝ), (-434108657/2500000000 : ℝ)] ![(22014014390033/50000000000000 : ℝ), (45517981815313/100000000000000 : ℝ), (10453989400299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294032127/10000000000 : ℝ)|^4557 ≤ (22014014390033/50000000000000 : ℝ)^3533
        have hw : |(5294032127/10000000000 : ℝ)|=(5294032127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716204351/5000000000 : ℝ)|^4557 ≤ (45517981815313/100000000000000 : ℝ)^3533
        have hw : |(2716204351/5000000000 : ℝ)|=(2716204351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-434108657/2500000000 : ℝ)|^4557 ≤ (10453989400299/100000000000000 : ℝ)^3533
        have hw : |(-434108657/2500000000 : ℝ)|=(434108657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s3_7 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4261279483/10000000000 : ℝ)*x 0 + (4514386827/10000000000 : ℝ)*x 1 + (804058273/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4261279483/10000000000 : ℝ)^4557 ≤ (33278703098623/100000000000000 : ℝ)^3533 := by
    have hnat : (4261279483 : ℕ)^4557*100000000000000^3533 ≤ 33278703098623^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4261279483 10000000000 33278703098623 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514386827/10000000000 : ℝ)^4557 ≤ (35849915713013/100000000000000 : ℝ)^3533 := by
    have hnat : (4514386827 : ℕ)^4557*100000000000000^3533 ≤ 35849915713013^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514386827 10000000000 35849915713013 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (804058273/2000000000 : ℝ)^4557 ≤ (30871381171279/100000000000000 : ℝ)^3533 := by
    have hnat : (804058273 : ℕ)^4557*100000000000000^3533 ≤ 30871381171279^3533*2000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804058273 2000000000 30871381171279 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4261279483/10000000000 : ℝ), (4514386827/10000000000 : ℝ), (804058273/2000000000 : ℝ)] ![(33278703098623/100000000000000 : ℝ), (35849915713013/100000000000000 : ℝ), (30871381171279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4261279483/10000000000 : ℝ)|^4557 ≤ (33278703098623/100000000000000 : ℝ)^3533
        have hw : |(4261279483/10000000000 : ℝ)|=(4261279483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514386827/10000000000 : ℝ)|^4557 ≤ (35849915713013/100000000000000 : ℝ)^3533
        have hw : |(4514386827/10000000000 : ℝ)|=(4514386827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(804058273/2000000000 : ℝ)|^4557 ≤ (30871381171279/100000000000000 : ℝ)^3533
        have hw : |(804058273/2000000000 : ℝ)|=(804058273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1530_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3983/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10571/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2733/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (777/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3983/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10571/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3983/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10571/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3983/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10571/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3983/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10571/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3983/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10571/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3983/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10571/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10571/100000 : ℝ) ^ (4555/1024 : ℝ) ≤ (4560704615203671/100000000000000000000 : ℝ) := by
    have hpowers : (10571/100000 : ℝ)^4555 ≤ (4560704615203671/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10571 : ℕ)^4555*100000000000000000000^1024 ≤ 4560704615203671^1024*100000^4555 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10571 100000 4560704615203671 100000000000000000000 4555 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10571/100000 : ℝ)) (X := (4560704615203671/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3983/25000 : ℝ) ^ (4555/1024 : ℝ) ≤ (14140836097380079/50000000000000000000 : ℝ) := by
    have hpowers : (3983/25000 : ℝ)^4555 ≤ (14140836097380079/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3983 : ℕ)^4555*50000000000000000000^1024 ≤ 14140836097380079^1024*25000^4555 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3983 25000 14140836097380079 50000000000000000000 4555 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3983/25000 : ℝ)) (X := (14140836097380079/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004560704615203671/50000000000000000000 : ℝ) ≤ (39063300973591/39062500000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (50004560704615203671/50000000000000000000 : ℝ)^1024 ≤ (39063300973591/39062500000000 : ℝ)^4555 := by
      have hnat : (50004560704615203671 : ℕ)^1024*39062500000000^4555 ≤ 39063300973591^4555*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004560704615203671 50000000000000000000 39063300973591 39062500000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39063300973591/39062500000000 : ℝ)) (X := (50004560704615203671/50000000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100032842376809963829/100000000000000000000 : ℝ) ≤ (625046139288767/625000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (100032842376809963829/100000000000000000000 : ℝ)^1024 ≤ (625046139288767/625000000000000 : ℝ)^4555 := by
      have hnat : (100032842376809963829 : ℕ)^1024*625000000000000^4555 ≤ 625046139288767^4555*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100032842376809963829 100000000000000000000 625046139288767 625000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625046139288767/625000000000000 : ℝ)) (X := (100032842376809963829/100000000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014140836097380079/25000000000000000000 : ℝ) ≤ (312539731500039/312500000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (25014140836097380079/25000000000000000000 : ℝ)^1024 ≤ (312539731500039/312500000000000 : ℝ)^4555 := by
      have hnat : (25014140836097380079 : ℕ)^1024*312500000000000^4555 ≤ 312539731500039^4555*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014140836097380079 25000000000000000000 312539731500039 312500000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312539731500039/312500000000000 : ℝ)) (X := (25014140836097380079/25000000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4560704615203671/100000000000000000000 : ℝ) ≤ ((1674994587203102227/1675312500000000000 : ℝ)+2*(33323711311/33506250000000 : ℝ)*(10571/100000 : ℝ))^(4555/1024 : ℝ) := by
    rw [show (1674994587203102227/1675312500000000000 : ℝ)+2*(33323711311/33506250000000 : ℝ)*(10571/100000 : ℝ)=(39063300973591/39062500000000 : ℝ) by norm_num, show 1+2*(4560704615203671/100000000000000000000 : ℝ)=(50004560704615203671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14140836097380079/50000000000000000000 : ℝ)+(4560704615203671/100000000000000000000 : ℝ) ≤ ((1674994587203102227/1675312500000000000 : ℝ)+(33323711311/33506250000000 : ℝ)*((3983/25000 : ℝ)+(10571/100000 : ℝ)))^(4555/1024 : ℝ) := by
    rw [show (1674994587203102227/1675312500000000000 : ℝ)+(33323711311/33506250000000 : ℝ)*((3983/25000 : ℝ)+(10571/100000 : ℝ))=(625046139288767/625000000000000 : ℝ) by norm_num, show 1+(14140836097380079/50000000000000000000 : ℝ)+(4560704615203671/100000000000000000000 : ℝ)=(100032842376809963829/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14140836097380079/50000000000000000000 : ℝ) ≤ ((1674994587203102227/1675312500000000000 : ℝ)+2*(33323711311/33506250000000 : ℝ)*(3983/25000 : ℝ))^(4555/1024 : ℝ) := by
    rw [show (1674994587203102227/1675312500000000000 : ℝ)+2*(33323711311/33506250000000 : ℝ)*(3983/25000 : ℝ)=(312539731500039/312500000000000 : ℝ) by norm_num, show 1+2*(14140836097380079/50000000000000000000 : ℝ)=(25014140836097380079/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1674994587203102227/1675312500000000000 : ℝ)*(X 1 0+X 2 0)+(33323711311/33506250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (10571/100000 : ℝ)) (hi := (3983/25000 : ℝ)) (c := (1674994587203102227/1675312500000000000 : ℝ)) (alpha := (33323711311/33506250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1674994587203102227/1675312500000000000 : ℝ)*(X 0 1+X 2 1)+(33323711311/33506250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (10571/100000 : ℝ)) (hi := (3983/25000 : ℝ)) (c := (1674994587203102227/1675312500000000000 : ℝ)) (alpha := (33323711311/33506250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1674994587203102227/1675312500000000000 : ℝ)*(X 0 2+X 1 2)+(33323711311/33506250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (10571/100000 : ℝ)) (hi := (3983/25000 : ℝ)) (c := (1674994587203102227/1675312500000000000 : ℝ)) (alpha := (33323711311/33506250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-460336691/2500000000 : ℝ)*X 0 0+(1358391851/2500000000 : ℝ)*X 0 1+(521609583/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351272139/10000000000 : ℝ)*X 1 0+(-488186931/2500000000 : ℝ)*X 1 1+(326005981/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535127237/1000000000 : ℝ)*X 2 0+(1304023843/2500000000 : ℝ)*X 2 1+(-976373923/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2130604879/5000000000 : ℝ)*X 0 0+(1004407631/2500000000 : ℝ)*X 0 1+(903405571/2000000000 : ℝ)*X 0 2+(2130604879/5000000000 : ℝ)*X 1 0+(1004407631/2500000000 : ℝ)*X 1 1+(903405571/2000000000 : ℝ)*X 1 2+(2130604879/5000000000 : ℝ)*X 2 0+(1004407631/2500000000 : ℝ)*X 2 1+(903405571/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-368275483/2000000000 : ℝ)*X 0 0+(521724559/1000000000 : ℝ)*X 0 1+(42440693/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294032123/10000000000 : ℝ)*X 1 0+(-13891477/80000000 : ℝ)*X 1 1+(5432408707/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294032127/10000000000 : ℝ)*X 2 0+(2716204351/5000000000 : ℝ)*X 2 1+(-434108657/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4261279483/10000000000 : ℝ)*X 0 0+(4514386827/10000000000 : ℝ)*X 0 1+(804058273/2000000000 : ℝ)*X 0 2+(4261279483/10000000000 : ℝ)*X 1 0+(4514386827/10000000000 : ℝ)*X 1 1+(804058273/2000000000 : ℝ)*X 1 2+(4261279483/10000000000 : ℝ)*X 2 0+(4514386827/10000000000 : ℝ)*X 2 1+(804058273/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45716552855549183418511/4467500000000000000000000000 : ℝ) := by norm_num
    linear_combination (670846379/50000000000000 : ℝ)*(base19) + (332990319/25000000000000 : ℝ)*(base23) + (15295853/10000000000000 : ℝ)*(lower2) + (118869473/50000000000000 : ℝ)*(upper3) + (8305877/20000000000000 : ℝ)*(lower4) + (825096261202717/25000000000000 : ℝ)*(major0) + (825096261202717/25000000000000 : ℝ)*(major1) + (825096261202717/25000000000000 : ℝ)*(major2) + (4598321653443171/100000000000000 : ℝ)*(sp0) + (4598336145126417/100000000000000 : ℝ)*(sp1) + (4598336154857899/100000000000000 : ℝ)*(sp2) + (1001210532222753/50000000000000 : ℝ)*(sp3) + (3958344001/25000000000000 : ℝ)*(sp4) + (11197252383/100000000000000 : ℝ)*(sp7) + (62576008178059/3125000000000 : ℝ)*(f.failure) + (183933499472767/4000000000000 : ℝ)*(f.sum) + (10663073866603/26805000000000000000000000000 : ℝ)*base65 + (8171347626796369/27921875000000000000000000000000 : ℝ)*base68 + (209433489628609881/27921875000000000000000000000000 : ℝ)*base69 + (95542407869594003/13960937500000000000000000000000 : ℝ)*base71 + (113466907131317/26805000000000000000000000000 : ℝ)*base74 + (10037626988296369/27921875000000000000000000000000 : ℝ)*base76 + (95671574728452619/27921875000000000000000000000000 : ℝ)*base78 + (206862746554328631/27921875000000000000000000000000 : ℝ)*base79 + (16187594070013/26805000000000000000000000000 : ℝ)*base81 + (1832151/312500000000000000000 : ℝ)*base90 + (1832151/312500000000000000000 : ℝ)*base92 + (1832151/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (111504391165835229220119/8935000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2017856379/100000000000000 : ℝ)*(base19) + (218893283/10000000000000 : ℝ)*(base23) + (259827009/100000000000000 : ℝ)*(upper3) + (37916499/50000000000000 : ℝ)*(lower4) + (129197329/50000000000000 : ℝ)*(upper5) + (3335767933579311/100000000000000 : ℝ)*(major0) + (3335767933579311/100000000000000 : ℝ)*(major1) + (3335767933579311/100000000000000 : ℝ)*(major2) + (30661197921/100000000000000 : ℝ)*(sp1) + (16455303761/50000000000000 : ℝ)*(sp2) + (145238607512671/3125000000000 : ℝ)*(sp4) + (1161900690337793/25000000000000 : ℝ)*(sp5) + (29047502130407/625000000000 : ℝ)*(sp6) + (202390001076959/10000000000000 : ℝ)*(sp7) + (202390001076959/10000000000000 : ℝ)*(f.failure) + (145238607512671/3125000000000 : ℝ)*(f.sum) + (4675784993319/4467500000000000000000000000 : ℝ)*base66 + (8630366016762301/55843750000000000000000000000000 : ℝ)*base68 + (492256842094612699/55843750000000000000000000000000 : ℝ)*base69 + (135830351468168551/55843750000000000000000000000000 : ℝ)*base72 + (18945354919601/4467500000000000000000000000 : ℝ)*base73 + (469490778616987699/55843750000000000000000000000000 : ℝ)*base75 + (34348643291137301/55843750000000000000000000000000 : ℝ)*base78 + (398750128422987699/55843750000000000000000000000000 : ℝ)*base79 + (20452963045041/4467500000000000000000000000 : ℝ)*base81 + (8124251/1000000000000000000000 : ℝ)*base90 + (8124251/1000000000000000000000 : ℝ)*base92 + (8124251/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1530_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3983/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10571/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2733/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (777/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1530_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1530_s4_0 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-115106471/625000000 : ℝ)*x 0 + (1086241563/2000000000 : ℝ)*x 1 + (326138713/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (115106471/625000000 : ℝ)^4557 ≤ (2819629180479/25000000000000 : ℝ)^3533 := by
    have hnat : (115106471 : ℕ)^4557*25000000000000^3533 ≤ 2819629180479^3533*625000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115106471 625000000 2819629180479 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086241563/2000000000 : ℝ)^4557 ≤ (45505003623683/100000000000000 : ℝ)^3533 := by
    have hnat : (1086241563 : ℕ)^4557*100000000000000^3533 ≤ 45505003623683^3533*2000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086241563 2000000000 45505003623683 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326138713/625000000 : ℝ)^4557 ≤ (21608239819249/50000000000000 : ℝ)^3533 := by
    have hnat : (326138713 : ℕ)^4557*50000000000000^3533 ≤ 21608239819249^3533*625000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326138713 625000000 21608239819249 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-115106471/625000000 : ℝ), (1086241563/2000000000 : ℝ), (326138713/625000000 : ℝ)] ![(2819629180479/25000000000000 : ℝ), (45505003623683/100000000000000 : ℝ), (21608239819249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-115106471/625000000 : ℝ)|^4557 ≤ (2819629180479/25000000000000 : ℝ)^3533
        have hw : |(-115106471/625000000 : ℝ)|=(115106471/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086241563/2000000000 : ℝ)|^4557 ≤ (45505003623683/100000000000000 : ℝ)^3533
        have hw : |(1086241563/2000000000 : ℝ)|=(1086241563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326138713/625000000 : ℝ)|^4557 ≤ (21608239819249/50000000000000 : ℝ)^3533
        have hw : |(326138713/625000000 : ℝ)|=(326138713/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s4_1 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42805217/80000000 : ℝ)*x 0 + (-487688481/2500000000 : ℝ)*x 1 + (5218219679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42805217/80000000 : ℝ)^4557 ≤ (1785453207277/4000000000000 : ℝ)^3533 := by
    have hnat : (42805217 : ℕ)^4557*4000000000000^3533 ≤ 1785453207277^3533*80000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42805217 80000000 1785453207277 4000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (487688481/2500000000 : ℝ)^4557 ≤ (12147187269389/100000000000000 : ℝ)^3533 := by
    have hnat : (487688481 : ℕ)^4557*100000000000000^3533 ≤ 12147187269389^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487688481 2500000000 12147187269389 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218219679/10000000000 : ℝ)^4557 ≤ (21608241266693/50000000000000 : ℝ)^3533 := by
    have hnat : (5218219679 : ℕ)^4557*50000000000000^3533 ≤ 21608241266693^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218219679 10000000000 21608241266693 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42805217/80000000 : ℝ), (-487688481/2500000000 : ℝ), (5218219679/10000000000 : ℝ)] ![(1785453207277/4000000000000 : ℝ), (12147187269389/100000000000000 : ℝ), (21608241266693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42805217/80000000 : ℝ)|^4557 ≤ (1785453207277/4000000000000 : ℝ)^3533
        have hw : |(42805217/80000000 : ℝ)|=(42805217/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-487688481/2500000000 : ℝ)|^4557 ≤ (12147187269389/100000000000000 : ℝ)^3533
        have hw : |(-487688481/2500000000 : ℝ)|=(487688481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218219679/10000000000 : ℝ)|^4557 ≤ (21608241266693/50000000000000 : ℝ)^3533
        have hw : |(5218219679/10000000000 : ℝ)|=(5218219679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s4_2 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350652513/10000000000 : ℝ)*x 0 + (1304554829/2500000000 : ℝ)*x 1 + (-1950753887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350652513/10000000000 : ℝ)^4557 ≤ (11159083589213/25000000000000 : ℝ)^3533 := by
    have hnat : (5350652513 : ℕ)^4557*25000000000000^3533 ≤ 11159083589213^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350652513 10000000000 11159083589213 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304554829/2500000000 : ℝ)^4557 ≤ (10804119663933/25000000000000 : ℝ)^3533 := by
    have hnat : (1304554829 : ℕ)^4557*25000000000000^3533 ≤ 10804119663933^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304554829 2500000000 10804119663933 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1950753887/10000000000 : ℝ)^4557 ≤ (2429437394443/20000000000000 : ℝ)^3533 := by
    have hnat : (1950753887 : ℕ)^4557*20000000000000^3533 ≤ 2429437394443^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950753887 10000000000 2429437394443 20000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350652513/10000000000 : ℝ), (1304554829/2500000000 : ℝ), (-1950753887/10000000000 : ℝ)] ![(11159083589213/25000000000000 : ℝ), (10804119663933/25000000000000 : ℝ), (2429437394443/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350652513/10000000000 : ℝ)|^4557 ≤ (11159083589213/25000000000000 : ℝ)^3533
        have hw : |(5350652513/10000000000 : ℝ)|=(5350652513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304554829/2500000000 : ℝ)|^4557 ≤ (10804119663933/25000000000000 : ℝ)^3533
        have hw : |(1304554829/2500000000 : ℝ)|=(1304554829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1950753887/10000000000 : ℝ)|^4557 ≤ (2429437394443/20000000000000 : ℝ)^3533
        have hw : |(-1950753887/10000000000 : ℝ)|=(1950753887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s4_3 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4261434293/10000000000 : ℝ)*x 0 + (4022752529/10000000000 : ℝ)*x 1 + (4511854317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4261434293/10000000000 : ℝ)^4557 ≤ (4160032814811/12500000000000 : ℝ)^3533 := by
    have hnat : (4261434293 : ℕ)^4557*12500000000000^3533 ≤ 4160032814811^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4261434293 10000000000 4160032814811 12500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4022752529/10000000000 : ℝ)^4557 ≤ (30895760009101/100000000000000 : ℝ)^3533 := by
    have hnat : (4022752529 : ℕ)^4557*100000000000000^3533 ≤ 30895760009101^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022752529 10000000000 30895760009101 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4511854317/10000000000 : ℝ)^4557 ≤ (35823977466363/100000000000000 : ℝ)^3533 := by
    have hnat : (4511854317 : ℕ)^4557*100000000000000^3533 ≤ 35823977466363^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511854317 10000000000 35823977466363 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4261434293/10000000000 : ℝ), (4022752529/10000000000 : ℝ), (4511854317/10000000000 : ℝ)] ![(4160032814811/12500000000000 : ℝ), (30895760009101/100000000000000 : ℝ), (35823977466363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4261434293/10000000000 : ℝ)|^4557 ≤ (4160032814811/12500000000000 : ℝ)^3533
        have hw : |(4261434293/10000000000 : ℝ)|=(4261434293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4022752529/10000000000 : ℝ)|^4557 ≤ (30895760009101/100000000000000 : ℝ)^3533
        have hw : |(4022752529/10000000000 : ℝ)|=(4022752529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4511854317/10000000000 : ℝ)|^4557 ≤ (35823977466363/100000000000000 : ℝ)^3533
        have hw : |(4511854317/10000000000 : ℝ)|=(4511854317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s4_4 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-368346369/2000000000 : ℝ)*x 0 + (5219322671/10000000000 : ℝ)*x 1 + (5430096513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (368346369/2000000000 : ℝ)^4557 ≤ (1127874033291/10000000000000 : ℝ)^3533 := by
    have hnat : (368346369 : ℕ)^4557*10000000000000^3533 ≤ 1127874033291^3533*2000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368346369 2000000000 1127874033291 10000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219322671/10000000000 : ℝ)^4557 ≤ (5403533165343/12500000000000 : ℝ)^3533 := by
    have hnat : (5219322671 : ℕ)^4557*12500000000000^3533 ≤ 5403533165343^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219322671 10000000000 5403533165343 12500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430096513/10000000000 : ℝ)^4557 ≤ (45492994333441/100000000000000 : ℝ)^3533 := by
    have hnat : (5430096513 : ℕ)^4557*100000000000000^3533 ≤ 45492994333441^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430096513 10000000000 45492994333441 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-368346369/2000000000 : ℝ), (5219322671/10000000000 : ℝ), (5430096513/10000000000 : ℝ)] ![(1127874033291/10000000000000 : ℝ), (5403533165343/12500000000000 : ℝ), (45492994333441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-368346369/2000000000 : ℝ)|^4557 ≤ (1127874033291/10000000000000 : ℝ)^3533
        have hw : |(-368346369/2000000000 : ℝ)|=(368346369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219322671/10000000000 : ℝ)|^4557 ≤ (5403533165343/12500000000000 : ℝ)^3533
        have hw : |(5219322671/10000000000 : ℝ)|=(5219322671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430096513/10000000000 : ℝ)|^4557 ≤ (45492994333441/100000000000000 : ℝ)^3533
        have hw : |(5430096513/10000000000 : ℝ)|=(5430096513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s4_5 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647296687/5000000000 : ℝ)*x 0 + (-347775331/2000000000 : ℝ)*x 1 + (2715048253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647296687/5000000000 : ℝ)^4557 ≤ (1761361974643/4000000000000 : ℝ)^3533 := by
    have hnat : (2647296687 : ℕ)^4557*4000000000000^3533 ≤ 1761361974643^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647296687 5000000000 1761361974643 4000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (347775331/2000000000 : ℝ)^4557 ≤ (5236478184851/50000000000000 : ℝ)^3533 := by
    have hnat : (347775331 : ℕ)^4557*50000000000000^3533 ≤ 5236478184851^3533*2000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347775331 2000000000 5236478184851 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715048253/5000000000 : ℝ)^4557 ≤ (22746497128899/50000000000000 : ℝ)^3533 := by
    have hnat : (2715048253 : ℕ)^4557*50000000000000^3533 ≤ 22746497128899^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715048253 5000000000 22746497128899 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647296687/5000000000 : ℝ), (-347775331/2000000000 : ℝ), (2715048253/5000000000 : ℝ)] ![(1761361974643/4000000000000 : ℝ), (5236478184851/50000000000000 : ℝ), (22746497128899/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647296687/5000000000 : ℝ)|^4557 ≤ (1761361974643/4000000000000 : ℝ)^3533
        have hw : |(2647296687/5000000000 : ℝ)|=(2647296687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-347775331/2000000000 : ℝ)|^4557 ≤ (5236478184851/50000000000000 : ℝ)^3533
        have hw : |(-347775331/2000000000 : ℝ)|=(347775331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715048253/5000000000 : ℝ)|^4557 ≤ (22746497128899/50000000000000 : ℝ)^3533
        have hw : |(2715048253/5000000000 : ℝ)|=(2715048253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s4_6 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294593387/10000000000 : ℝ)*x 0 + (2715048247/5000000000 : ℝ)*x 1 + (-434719163/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294593387/10000000000 : ℝ)^4557 ≤ (44034049505531/100000000000000 : ℝ)^3533 := by
    have hnat : (5294593387 : ℕ)^4557*100000000000000^3533 ≤ 44034049505531^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294593387 10000000000 44034049505531 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715048247/5000000000 : ℝ)^4557 ≤ (45492994128123/100000000000000 : ℝ)^3533 := by
    have hnat : (2715048247 : ℕ)^4557*100000000000000^3533 ≤ 45492994128123^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715048247 5000000000 45492994128123 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (434719163/2500000000 : ℝ)^4557 ≤ (2618239086599/25000000000000 : ℝ)^3533 := by
    have hnat : (434719163 : ℕ)^4557*25000000000000^3533 ≤ 2618239086599^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434719163 2500000000 2618239086599 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294593387/10000000000 : ℝ), (2715048247/5000000000 : ℝ), (-434719163/2500000000 : ℝ)] ![(44034049505531/100000000000000 : ℝ), (45492994128123/100000000000000 : ℝ), (2618239086599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294593387/10000000000 : ℝ)|^4557 ≤ (44034049505531/100000000000000 : ℝ)^3533
        have hw : |(5294593387/10000000000 : ℝ)|=(5294593387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715048247/5000000000 : ℝ)|^4557 ≤ (45492994128123/100000000000000 : ℝ)^3533
        have hw : |(2715048247/5000000000 : ℝ)|=(2715048247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-434719163/2500000000 : ℝ)|^4557 ≤ (2618239086599/25000000000000 : ℝ)^3533
        have hw : |(-434719163/2500000000 : ℝ)|=(434719163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s4_7 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (170459969/400000000 : ℝ)*x 0 + (4509321041/10000000000 : ℝ)*x 1 + (805060999/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170459969/400000000 : ℝ)^4557 ≤ (3328091659127/10000000000000 : ℝ)^3533 := by
    have hnat : (170459969 : ℕ)^4557*10000000000000^3533 ≤ 3328091659127^3533*400000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170459969 400000000 3328091659127 10000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4509321041/10000000000 : ℝ)^4557 ≤ (35798035595639/100000000000000 : ℝ)^3533 := by
    have hnat : (4509321041 : ℕ)^4557*100000000000000^3533 ≤ 35798035595639^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509321041 10000000000 35798035595639 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (805060999/2000000000 : ℝ)^4557 ≤ (15460523898783/50000000000000 : ℝ)^3533 := by
    have hnat : (805060999 : ℕ)^4557*50000000000000^3533 ≤ 15460523898783^3533*2000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805060999 2000000000 15460523898783 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(170459969/400000000 : ℝ), (4509321041/10000000000 : ℝ), (805060999/2000000000 : ℝ)] ![(3328091659127/10000000000000 : ℝ), (35798035595639/100000000000000 : ℝ), (15460523898783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(170459969/400000000 : ℝ)|^4557 ≤ (3328091659127/10000000000000 : ℝ)^3533
        have hw : |(170459969/400000000 : ℝ)|=(170459969/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4509321041/10000000000 : ℝ)|^4557 ≤ (35798035595639/100000000000000 : ℝ)^3533
        have hw : |(4509321041/10000000000 : ℝ)|=(4509321041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(805060999/2000000000 : ℝ)|^4557 ≤ (15460523898783/50000000000000 : ℝ)^3533
        have hw : |(805060999/2000000000 : ℝ)|=(805060999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1530_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (777/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2733/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5489/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (777/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2733/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (777/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2733/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (777/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2733/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (777/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2733/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (777/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2733/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (777/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2733/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2733/25000 : ℝ) ^ (4555/1024 : ℝ) ≤ (5295452883771149/100000000000000000000 : ℝ) := by
    have hpowers : (2733/25000 : ℝ)^4555 ≤ (5295452883771149/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2733 : ℕ)^4555*100000000000000000000^1024 ≤ 5295452883771149^1024*25000^4555 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2733 25000 5295452883771149 100000000000000000000 4555 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2733/25000 : ℝ)) (X := (5295452883771149/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (777/5000 : ℝ) ^ (4555/1024 : ℝ) ≤ (6328755248422123/25000000000000000000 : ℝ) := by
    have hpowers : (777/5000 : ℝ)^4555 ≤ (6328755248422123/25000000000000000000 : ℝ)^1024 := by
      have hnat : (777 : ℕ)^4555*25000000000000000000^1024 ≤ 6328755248422123^1024*5000^4555 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        777 5000 6328755248422123 25000000000000000000 4555 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (777/5000 : ℝ)) (X := (6328755248422123/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005295452883771149/50000000000000000000 : ℝ) ≤ (10000238082159029/10000000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (50005295452883771149/50000000000000000000 : ℝ)^1024 ≤ (10000238082159029/10000000000000000 : ℝ)^4555 := by
      have hnat : (50005295452883771149 : ℕ)^1024*10000000000000000^4555 ≤ 10000238082159029^4555*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005295452883771149 50000000000000000000 10000238082159029 10000000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000238082159029/10000000000000000 : ℝ)) (X := (50005295452883771149/50000000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030610473877459641/100000000000000000000 : ℝ) ≤ (10000688066014973/10000000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (100030610473877459641/100000000000000000000 : ℝ)^1024 ≤ (10000688066014973/10000000000000000 : ℝ)^4555 := by
      have hnat : (100030610473877459641 : ℕ)^1024*10000000000000000^4555 ≤ 10000688066014973^4555*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030610473877459641 100000000000000000000 10000688066014973 10000000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000688066014973/10000000000000000 : ℝ)) (X := (100030610473877459641/100000000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506328755248422123/12500000000000000000 : ℝ) ≤ (10001138049870917/10000000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (12506328755248422123/12500000000000000000 : ℝ)^1024 ≤ (10001138049870917/10000000000000000 : ℝ)^4555 := by
      have hnat : (12506328755248422123 : ℕ)^1024*10000000000000000^4555 ≤ 10001138049870917^4555*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506328755248422123 12500000000000000000 10001138049870917 10000000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001138049870917/10000000000000000 : ℝ)) (X := (12506328755248422123/12500000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5295452883771149/100000000000000000000 : ℝ) ≤ ((79984824020073691/80000000000000000 : ℝ)+2*(6249775777/6400000000000 : ℝ)*(2733/25000 : ℝ))^(4555/1024 : ℝ) := by
    rw [show (79984824020073691/80000000000000000 : ℝ)+2*(6249775777/6400000000000 : ℝ)*(2733/25000 : ℝ)=(10000238082159029/10000000000000000 : ℝ) by norm_num, show 1+2*(5295452883771149/100000000000000000000 : ℝ)=(50005295452883771149/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6328755248422123/25000000000000000000 : ℝ)+(5295452883771149/100000000000000000000 : ℝ) ≤ ((79984824020073691/80000000000000000 : ℝ)+(6249775777/6400000000000 : ℝ)*((777/5000 : ℝ)+(2733/25000 : ℝ)))^(4555/1024 : ℝ) := by
    rw [show (79984824020073691/80000000000000000 : ℝ)+(6249775777/6400000000000 : ℝ)*((777/5000 : ℝ)+(2733/25000 : ℝ))=(10000688066014973/10000000000000000 : ℝ) by norm_num, show 1+(6328755248422123/25000000000000000000 : ℝ)+(5295452883771149/100000000000000000000 : ℝ)=(100030610473877459641/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6328755248422123/25000000000000000000 : ℝ) ≤ ((79984824020073691/80000000000000000 : ℝ)+2*(6249775777/6400000000000 : ℝ)*(777/5000 : ℝ))^(4555/1024 : ℝ) := by
    rw [show (79984824020073691/80000000000000000 : ℝ)+2*(6249775777/6400000000000 : ℝ)*(777/5000 : ℝ)=(10001138049870917/10000000000000000 : ℝ) by norm_num, show 1+2*(6328755248422123/25000000000000000000 : ℝ)=(12506328755248422123/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (79984824020073691/80000000000000000 : ℝ)*(X 1 0+X 2 0)+(6249775777/6400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (2733/25000 : ℝ)) (hi := (777/5000 : ℝ)) (c := (79984824020073691/80000000000000000 : ℝ)) (alpha := (6249775777/6400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (79984824020073691/80000000000000000 : ℝ)*(X 0 1+X 2 1)+(6249775777/6400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (2733/25000 : ℝ)) (hi := (777/5000 : ℝ)) (c := (79984824020073691/80000000000000000 : ℝ)) (alpha := (6249775777/6400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (79984824020073691/80000000000000000 : ℝ)*(X 0 2+X 1 2)+(6249775777/6400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (2733/25000 : ℝ)) (hi := (777/5000 : ℝ)) (c := (79984824020073691/80000000000000000 : ℝ)) (alpha := (6249775777/6400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-115106471/625000000 : ℝ)*X 0 0+(1086241563/2000000000 : ℝ)*X 0 1+(326138713/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42805217/80000000 : ℝ)*X 1 0+(-487688481/2500000000 : ℝ)*X 1 1+(5218219679/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350652513/10000000000 : ℝ)*X 2 0+(1304554829/2500000000 : ℝ)*X 2 1+(-1950753887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4261434293/10000000000 : ℝ)*X 0 0+(4022752529/10000000000 : ℝ)*X 0 1+(4511854317/10000000000 : ℝ)*X 0 2+(4261434293/10000000000 : ℝ)*X 1 0+(4022752529/10000000000 : ℝ)*X 1 1+(4511854317/10000000000 : ℝ)*X 1 2+(4261434293/10000000000 : ℝ)*X 2 0+(4022752529/10000000000 : ℝ)*X 2 1+(4511854317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-368346369/2000000000 : ℝ)*X 0 0+(5219322671/10000000000 : ℝ)*X 0 1+(5430096513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647296687/5000000000 : ℝ)*X 1 0+(-347775331/2000000000 : ℝ)*X 1 1+(2715048253/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294593387/10000000000 : ℝ)*X 2 0+(2715048247/5000000000 : ℝ)*X 2 1+(-434719163/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((170459969/400000000 : ℝ)*X 0 0+(4509321041/10000000000 : ℝ)*X 0 1+(805060999/2000000000 : ℝ)*X 0 2+(170459969/400000000 : ℝ)*X 1 0+(4509321041/10000000000 : ℝ)*X 1 1+(805060999/2000000000 : ℝ)*X 1 2+(170459969/400000000 : ℝ)*X 2 0+(4509321041/10000000000 : ℝ)*X 2 1+(805060999/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2109281182335523233359091/500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (259066877/50000000000000 : ℝ)*(base19) + (783638609/100000000000000 : ℝ)*(base23) + (40107751/100000000000000 : ℝ)*(lower2) + (38976891/25000000000000 : ℝ)*(upper3) + (191517477/100000000000000 : ℝ)*(upper5) + (421230060216467/12500000000000 : ℝ)*(major0) + (421230060216467/12500000000000 : ℝ)*(major1) + (421230060216467/12500000000000 : ℝ)*(major2) + (2347548870711603/50000000000000 : ℝ)*(sp0) + (4695107563719809/100000000000000 : ℝ)*(sp1) + (4695107298214953/100000000000000 : ℝ)*(sp2) + (51114202432227/2500000000000 : ℝ)*(sp3) + (2585107589/25000000000000 : ℝ)*(sp4) + (4643702079/100000000000000 : ℝ)*(sp7) + (1022286370495579/50000000000000 : ℝ)*(f.failure) + (2347554040926781/50000000000000 : ℝ)*(f.sum) + (346097519301/40000000000000000000000000 : ℝ)*base66 + (3912535424907197/1000000000000000000000000000000 : ℝ)*base67 + (3302354891092803/1000000000000000000000000000000 : ℝ)*base70 + (4515334590092803/1000000000000000000000000000000 : ℝ)*base72 + (78804761861/40000000000000000000000000 : ℝ)*base74 + (1057454473907197/1000000000000000000000000000000 : ℝ)*base75 + (4268517354092803/1000000000000000000000000000000 : ℝ)*base78 + (5535140957092803/1000000000000000000000000000000 : ℝ)*base80 + (383537706301/40000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (11536569/5000000000000000000000 : ℝ)*base89 + (11536569/5000000000000000000000 : ℝ)*base91 + (11536569/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (74326340854291284510513/16000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (186618877/25000000000000 : ℝ)*(base19) + (409716459/50000000000000 : ℝ)*(base23) + (96018077/100000000000000 : ℝ)*(upper3) + (6787823/25000000000000 : ℝ)*(lower4) + (47216539/50000000000000 : ℝ)*(upper5) + (27241874340531/800000000000 : ℝ)*(major0) + (27241874340531/800000000000 : ℝ)*(major1) + (27241874340531/800000000000 : ℝ)*(major2) + (114119573/1000000000000 : ℝ)*(sp1) + (1235890667/10000000000000 : ℝ)*(sp2) + (4744421313512391/100000000000000 : ℝ)*(sp4) + (4744409155079583/100000000000000 : ℝ)*(sp5) + (1186102033793201/25000000000000 : ℝ)*(sp6) + (206604711677381/10000000000000 : ℝ)*(sp7) + (206604711677381/10000000000000 : ℝ)*(f.failure) + (4744421313512391/100000000000000 : ℝ)*(f.sum) + (39156712991/12800000000000000000000000 : ℝ)*base65 + (51620346636579/64000000000000000000000000000 : ℝ)*base68 + (322565688204579/64000000000000000000000000000 : ℝ)*base70 + (123381879219421/64000000000000000000000000000 : ℝ)*base71 + (11031450721/12800000000000000000000000 : ℝ)*base74 + (989224959564579/64000000000000000000000000000 : ℝ)*base76 + (240129373004579/64000000000000000000000000000 : ℝ)*base78 + (700200860876579/64000000000000000000000000000 : ℝ)*base80 + (107318937253/64000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (2013991/1000000000000000000000 : ℝ)*base89 + (2013991/1000000000000000000000 : ℝ)*base91 + (2013991/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1530_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (777/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2733/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5489/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1530_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1530_s5_0 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1841745483/10000000000 : ℝ)*x 0 + (678866351/1250000000 : ℝ)*x 1 + (326154289/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1841745483/10000000000 : ℝ)^4557 ≤ (5639424029481/50000000000000 : ℝ)^3533 := by
    have hnat : (1841745483 : ℕ)^4557*50000000000000^3533 ≤ 5639424029481^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1841745483 10000000000 5639424029481 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678866351/1250000000 : ℝ)^4557 ≤ (22751005039801/50000000000000 : ℝ)^3533 := by
    have hnat : (678866351 : ℕ)^4557*50000000000000^3533 ≤ 22751005039801^3533*1250000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678866351 1250000000 22751005039801 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326154289/625000000 : ℝ)^4557 ≤ (43219141842729/100000000000000 : ℝ)^3533 := by
    have hnat : (326154289 : ℕ)^4557*100000000000000^3533 ≤ 43219141842729^3533*625000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326154289 625000000 43219141842729 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1841745483/10000000000 : ℝ), (678866351/1250000000 : ℝ), (326154289/625000000 : ℝ)] ![(5639424029481/50000000000000 : ℝ), (22751005039801/50000000000000 : ℝ), (43219141842729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1841745483/10000000000 : ℝ)|^4557 ≤ (5639424029481/50000000000000 : ℝ)^3533
        have hw : |(-1841745483/10000000000 : ℝ)|=(1841745483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678866351/1250000000 : ℝ)|^4557 ≤ (22751005039801/50000000000000 : ℝ)^3533
        have hw : |(678866351/1250000000 : ℝ)|=(678866351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326154289/625000000 : ℝ)|^4557 ≤ (43219141842729/100000000000000 : ℝ)^3533
        have hw : |(326154289/625000000 : ℝ)|=(326154289/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s5_1 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675289739/5000000000 : ℝ)*x 0 + (-487630019/2500000000 : ℝ)*x 1 + (208738747/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675289739/5000000000 : ℝ)^4557 ≤ (892710969859/2000000000000 : ℝ)^3533 := by
    have hnat : (2675289739 : ℕ)^4557*2000000000000^3533 ≤ 892710969859^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675289739 5000000000 892710969859 2000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (487630019/2500000000 : ℝ)^4557 ≤ (12145309100061/100000000000000 : ℝ)^3533 := by
    have hnat : (487630019 : ℕ)^4557*100000000000000^3533 ≤ 12145309100061^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487630019 2500000000 12145309100061 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208738747/400000000 : ℝ)^4557 ≤ (43219142387531/100000000000000 : ℝ)^3533 := by
    have hnat : (208738747 : ℕ)^4557*100000000000000^3533 ≤ 43219142387531^3533*400000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208738747 400000000 43219142387531 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675289739/5000000000 : ℝ), (-487630019/2500000000 : ℝ), (208738747/400000000 : ℝ)] ![(892710969859/2000000000000 : ℝ), (12145309100061/100000000000000 : ℝ), (43219142387531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675289739/5000000000 : ℝ)|^4557 ≤ (892710969859/2000000000000 : ℝ)^3533
        have hw : |(2675289739/5000000000 : ℝ)|=(2675289739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-487630019/2500000000 : ℝ)|^4557 ≤ (12145309100061/100000000000000 : ℝ)^3533
        have hw : |(-487630019/2500000000 : ℝ)|=(487630019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208738747/400000000 : ℝ)|^4557 ≤ (43219142387531/100000000000000 : ℝ)^3533
        have hw : |(208738747/400000000 : ℝ)|=(208738747/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s5_2 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350579529/10000000000 : ℝ)*x 0 + (1043693723/2000000000 : ℝ)*x 1 + (-1950520087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350579529/10000000000 : ℝ)^4557 ≤ (22317774520857/50000000000000 : ℝ)^3533 := by
    have hnat : (5350579529 : ℕ)^4557*50000000000000^3533 ≤ 22317774520857^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350579529 10000000000 22317774520857 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043693723/2000000000 : ℝ)^4557 ≤ (43219141746587/100000000000000 : ℝ)^3533 := by
    have hnat : (1043693723 : ℕ)^4557*100000000000000^3533 ≤ 43219141746587^3533*2000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043693723 2000000000 43219141746587 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1950520087/10000000000 : ℝ)^4557 ≤ (12145309188407/100000000000000 : ℝ)^3533 := by
    have hnat : (1950520087 : ℕ)^4557*100000000000000^3533 ≤ 12145309188407^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950520087 10000000000 12145309188407 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350579529/10000000000 : ℝ), (1043693723/2000000000 : ℝ), (-1950520087/10000000000 : ℝ)] ![(22317774520857/50000000000000 : ℝ), (43219141746587/100000000000000 : ℝ), (12145309188407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350579529/10000000000 : ℝ)|^4557 ≤ (22317774520857/50000000000000 : ℝ)^3533
        have hw : |(5350579529/10000000000 : ℝ)|=(5350579529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043693723/2000000000 : ℝ)|^4557 ≤ (43219141746587/100000000000000 : ℝ)^3533
        have hw : |(1043693723/2000000000 : ℝ)|=(1043693723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1950520087/10000000000 : ℝ)|^4557 ≤ (12145309188407/100000000000000 : ℝ)^3533
        have hw : |(-1950520087/10000000000 : ℝ)|=(1950520087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s5_3 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4261459877/10000000000 : ℝ)*x 0 + (1005838529/2500000000 : ℝ)*x 1 + (4511247219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4261459877/10000000000 : ℝ)^4557 ≤ (33280520230797/100000000000000 : ℝ)^3533 := by
    have hnat : (4261459877 : ℕ)^4557*100000000000000^3533 ≤ 33280520230797^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4261459877 10000000000 33280520230797 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005838529/2500000000 : ℝ)^4557 ≤ (7725429908109/25000000000000 : ℝ)^3533 := by
    have hnat : (1005838529 : ℕ)^4557*25000000000000^3533 ≤ 7725429908109^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005838529 2500000000 7725429908109 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4511247219/10000000000 : ℝ)^4557 ≤ (7163552025727/20000000000000 : ℝ)^3533 := by
    have hnat : (4511247219 : ℕ)^4557*20000000000000^3533 ≤ 7163552025727^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511247219 10000000000 7163552025727 20000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4261459877/10000000000 : ℝ), (1005838529/2500000000 : ℝ), (4511247219/10000000000 : ℝ)] ![(33280520230797/100000000000000 : ℝ), (7725429908109/25000000000000 : ℝ), (7163552025727/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4261459877/10000000000 : ℝ)|^4557 ≤ (33280520230797/100000000000000 : ℝ)^3533
        have hw : |(4261459877/10000000000 : ℝ)|=(4261459877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005838529/2500000000 : ℝ)|^4557 ≤ (7725429908109/25000000000000 : ℝ)^3533
        have hw : |(1005838529/2500000000 : ℝ)|=(1005838529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4511247219/10000000000 : ℝ)|^4557 ≤ (7163552025727/20000000000000 : ℝ)^3533
        have hw : |(4511247219/10000000000 : ℝ)|=(4511247219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s5_4 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-368354761/2000000000 : ℝ)*x 0 + (2609783201/5000000000 : ℝ)*x 1 + (678728111/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (368354761/2000000000 : ℝ)^4557 ≤ (281976794353/2500000000000 : ℝ)^3533 := by
    have hnat : (368354761 : ℕ)^4557*2500000000000^3533 ≤ 281976794353^3533*2000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368354761 2000000000 281976794353 2500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609783201/5000000000 : ℝ)^4557 ≤ (43230869093603/100000000000000 : ℝ)^3533 := by
    have hnat : (2609783201 : ℕ)^4557*100000000000000^3533 ≤ 43230869093603^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609783201 5000000000 43230869093603 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678728111/1250000000 : ℝ)^4557 ≤ (45490059124941/100000000000000 : ℝ)^3533 := by
    have hnat : (678728111 : ℕ)^4557*100000000000000^3533 ≤ 45490059124941^3533*1250000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678728111 1250000000 45490059124941 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-368354761/2000000000 : ℝ), (2609783201/5000000000 : ℝ), (678728111/1250000000 : ℝ)] ![(281976794353/2500000000000 : ℝ), (43230869093603/100000000000000 : ℝ), (45490059124941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-368354761/2000000000 : ℝ)|^4557 ≤ (281976794353/2500000000000 : ℝ)^3533
        have hw : |(-368354761/2000000000 : ℝ)|=(368354761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609783201/5000000000 : ℝ)|^4557 ≤ (43230869093603/100000000000000 : ℝ)^3533
        have hw : |(2609783201/5000000000 : ℝ)|=(2609783201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678728111/1250000000 : ℝ)|^4557 ≤ (45490059124941/100000000000000 : ℝ)^3533
        have hw : |(678728111/1250000000 : ℝ)|=(678728111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s5_5 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647329587/5000000000 : ℝ)*x 0 + (-5434887/31250000 : ℝ)*x 1 + (5429824723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647329587/5000000000 : ℝ)^4557 ≤ (11008688806319/25000000000000 : ℝ)^3533 := by
    have hnat : (2647329587 : ℕ)^4557*25000000000000^3533 ≤ 11008688806319^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647329587 5000000000 11008688806319 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434887/31250000 : ℝ)^4557 ≤ (1309398426661/12500000000000 : ℝ)^3533 := by
    have hnat : (5434887 : ℕ)^4557*12500000000000^3533 ≤ 1309398426661^3533*31250000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434887 31250000 1309398426661 12500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429824723/10000000000 : ℝ)^4557 ≤ (45490057341947/100000000000000 : ℝ)^3533 := by
    have hnat : (5429824723 : ℕ)^4557*100000000000000^3533 ≤ 45490057341947^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429824723 10000000000 45490057341947 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647329587/5000000000 : ℝ), (-5434887/31250000 : ℝ), (5429824723/10000000000 : ℝ)] ![(11008688806319/25000000000000 : ℝ), (1309398426661/12500000000000 : ℝ), (45490057341947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647329587/5000000000 : ℝ)|^4557 ≤ (11008688806319/25000000000000 : ℝ)^3533
        have hw : |(2647329587/5000000000 : ℝ)|=(2647329587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5434887/31250000 : ℝ)|^4557 ≤ (1309398426661/12500000000000 : ℝ)^3533
        have hw : |(-5434887/31250000 : ℝ)|=(5434887/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429824723/10000000000 : ℝ)|^4557 ≤ (45490057341947/100000000000000 : ℝ)^3533
        have hw : |(5429824723/10000000000 : ℝ)|=(5429824723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s5_6 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294659093/10000000000 : ℝ)*x 0 + (1357456187/2500000000 : ℝ)*x 1 + (-1739163917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294659093/10000000000 : ℝ)^4557 ≤ (1100868858909/2500000000000 : ℝ)^3533 := by
    have hnat : (5294659093 : ℕ)^4557*2500000000000^3533 ≤ 1100868858909^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294659093 10000000000 1100868858909 2500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357456187/2500000000 : ℝ)^4557 ≤ (45490057612097/100000000000000 : ℝ)^3533 := by
    have hnat : (1357456187 : ℕ)^4557*100000000000000^3533 ≤ 45490057612097^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357456187 2500000000 45490057612097 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1739163917/10000000000 : ℝ)^4557 ≤ (1047518801149/10000000000000 : ℝ)^3533 := by
    have hnat : (1739163917 : ℕ)^4557*10000000000000^3533 ≤ 1047518801149^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1739163917 10000000000 1047518801149 10000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294659093/10000000000 : ℝ), (1357456187/2500000000 : ℝ), (-1739163917/10000000000 : ℝ)] ![(1100868858909/2500000000000 : ℝ), (45490057612097/100000000000000 : ℝ), (1047518801149/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294659093/10000000000 : ℝ)|^4557 ≤ (1100868858909/2500000000000 : ℝ)^3533
        have hw : |(5294659093/10000000000 : ℝ)|=(5294659093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357456187/2500000000 : ℝ)|^4557 ≤ (45490057612097/100000000000000 : ℝ)^3533
        have hw : |(1357456187/2500000000 : ℝ)|=(1357456187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1739163917/10000000000 : ℝ)|^4557 ≤ (1047518801149/10000000000000 : ℝ)^3533
        have hw : |(-1739163917/10000000000 : ℝ)|=(1739163917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s5_7 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133172649/312500000 : ℝ)*x 0 + (4508726183/10000000000 : ℝ)*x 1 + (2012946881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133172649/312500000 : ℝ)^4557 ≤ (16640586945857/50000000000000 : ℝ)^3533 := by
    have hnat : (133172649 : ℕ)^4557*50000000000000^3533 ≤ 16640586945857^3533*312500000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133172649 312500000 16640586945857 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508726183/10000000000 : ℝ)^4557 ≤ (7158388919591/20000000000000 : ℝ)^3533 := by
    have hnat : (4508726183 : ℕ)^4557*20000000000000^3533 ≤ 7158388919591^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508726183 10000000000 7158388919591 20000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2012946881/5000000000 : ℝ)^4557 ≤ (1932930093073/6250000000000 : ℝ)^3533 := by
    have hnat : (2012946881 : ℕ)^4557*6250000000000^3533 ≤ 1932930093073^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012946881 5000000000 1932930093073 6250000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133172649/312500000 : ℝ), (4508726183/10000000000 : ℝ), (2012946881/5000000000 : ℝ)] ![(16640586945857/50000000000000 : ℝ), (7158388919591/20000000000000 : ℝ), (1932930093073/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133172649/312500000 : ℝ)|^4557 ≤ (16640586945857/50000000000000 : ℝ)^3533
        have hw : |(133172649/312500000 : ℝ)|=(133172649/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508726183/10000000000 : ℝ)|^4557 ≤ (7158388919591/20000000000000 : ℝ)^3533
        have hw : |(4508726183/10000000000 : ℝ)|=(4508726183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2012946881/5000000000 : ℝ)|^4557 ≤ (1932930093073/6250000000000 : ℝ)^3533
        have hw : |(2012946881/5000000000 : ℝ)|=(2012946881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1530_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5489/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10983/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5489/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5489/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5489/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5489/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5489/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5489/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5489/50000 : ℝ) ^ (4555/1024 : ℝ) ≤ (2697645898934409/50000000000000000000 : ℝ) := by
    have hpowers : (5489/50000 : ℝ)^4555 ≤ (2697645898934409/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5489 : ℕ)^4555*50000000000000000000^1024 ≤ 2697645898934409^1024*50000^4555 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5489 50000 2697645898934409 50000000000000000000 4555 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5489/50000 : ℝ)) (X := (2697645898934409/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4555/1024 : ℝ) ≤ (12477355560188987/50000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4555 ≤ (12477355560188987/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4555*50000000000000000000^1024 ≤ 12477355560188987^1024*10000^4555 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 12477355560188987 50000000000000000000 4555 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (12477355560188987/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002697645898934409/25000000000000000000 : ℝ) ≤ (5000121285351221/5000000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (25002697645898934409/25000000000000000000 : ℝ)^1024 ≤ (5000121285351221/5000000000000000 : ℝ)^4555 := by
      have hnat : (25002697645898934409 : ℕ)^1024*5000000000000000^4555 ≤ 5000121285351221^4555*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002697645898934409 25000000000000000000 5000121285351221 5000000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000121285351221/5000000000000000 : ℝ)) (X := (25002697645898934409/25000000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12503793750364780849/12500000000000000000 : ℝ) ≤ (10000682211805137/10000000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (12503793750364780849/12500000000000000000 : ℝ)^1024 ≤ (10000682211805137/10000000000000000 : ℝ)^4555 := by
      have hnat : (12503793750364780849 : ℕ)^1024*10000000000000000^4555 ≤ 10000682211805137^4555*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503793750364780849 12500000000000000000 10000682211805137 10000000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000682211805137/10000000000000000 : ℝ)) (X := (12503793750364780849/12500000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012477355560188987/25000000000000000000 : ℝ) ≤ (1250140231613479/1250000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (25012477355560188987/25000000000000000000 : ℝ)^1024 ≤ (1250140231613479/1250000000000000 : ℝ)^4555 := by
      have hnat : (25012477355560188987 : ℕ)^1024*1250000000000000^4555 ≤ 1250140231613479^4555*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012477355560188987 25000000000000000000 1250140231613479 1250000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250140231613479/1250000000000000 : ℝ)) (X := (25012477355560188987/25000000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2697645898934409/50000000000000000000 : ℝ) ≤ ((11277860429739661721/11280000000000000000 : ℝ)+2*(87928220539/90240000000000 : ℝ)*(5489/50000 : ℝ))^(4555/1024 : ℝ) := by
    rw [show (11277860429739661721/11280000000000000000 : ℝ)+2*(87928220539/90240000000000 : ℝ)*(5489/50000 : ℝ)=(5000121285351221/5000000000000000 : ℝ) by norm_num, show 1+2*(2697645898934409/50000000000000000000 : ℝ)=(25002697645898934409/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12477355560188987/50000000000000000000 : ℝ)+(2697645898934409/50000000000000000000 : ℝ) ≤ ((11277860429739661721/11280000000000000000 : ℝ)+(87928220539/90240000000000 : ℝ)*((1549/10000 : ℝ)+(5489/50000 : ℝ)))^(4555/1024 : ℝ) := by
    rw [show (11277860429739661721/11280000000000000000 : ℝ)+(87928220539/90240000000000 : ℝ)*((1549/10000 : ℝ)+(5489/50000 : ℝ))=(10000682211805137/10000000000000000 : ℝ) by norm_num, show 1+(12477355560188987/50000000000000000000 : ℝ)+(2697645898934409/50000000000000000000 : ℝ)=(12503793750364780849/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12477355560188987/50000000000000000000 : ℝ) ≤ ((11277860429739661721/11280000000000000000 : ℝ)+2*(87928220539/90240000000000 : ℝ)*(1549/10000 : ℝ))^(4555/1024 : ℝ) := by
    rw [show (11277860429739661721/11280000000000000000 : ℝ)+2*(87928220539/90240000000000 : ℝ)*(1549/10000 : ℝ)=(1250140231613479/1250000000000000 : ℝ) by norm_num, show 1+2*(12477355560188987/50000000000000000000 : ℝ)=(25012477355560188987/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11277860429739661721/11280000000000000000 : ℝ)*(X 1 0+X 2 0)+(87928220539/90240000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (5489/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11277860429739661721/11280000000000000000 : ℝ)) (alpha := (87928220539/90240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11277860429739661721/11280000000000000000 : ℝ)*(X 0 1+X 2 1)+(87928220539/90240000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (5489/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11277860429739661721/11280000000000000000 : ℝ)) (alpha := (87928220539/90240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11277860429739661721/11280000000000000000 : ℝ)*(X 0 2+X 1 2)+(87928220539/90240000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (5489/50000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11277860429739661721/11280000000000000000 : ℝ)) (alpha := (87928220539/90240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1841745483/10000000000 : ℝ)*X 0 0+(678866351/1250000000 : ℝ)*X 0 1+(326154289/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675289739/5000000000 : ℝ)*X 1 0+(-487630019/2500000000 : ℝ)*X 1 1+(208738747/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350579529/10000000000 : ℝ)*X 2 0+(1043693723/2000000000 : ℝ)*X 2 1+(-1950520087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4261459877/10000000000 : ℝ)*X 0 0+(1005838529/2500000000 : ℝ)*X 0 1+(4511247219/10000000000 : ℝ)*X 0 2+(4261459877/10000000000 : ℝ)*X 1 0+(1005838529/2500000000 : ℝ)*X 1 1+(4511247219/10000000000 : ℝ)*X 1 2+(4261459877/10000000000 : ℝ)*X 2 0+(1005838529/2500000000 : ℝ)*X 2 1+(4511247219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-368354761/2000000000 : ℝ)*X 0 0+(2609783201/5000000000 : ℝ)*X 0 1+(678728111/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647329587/5000000000 : ℝ)*X 1 0+(-5434887/31250000 : ℝ)*X 1 1+(5429824723/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294659093/10000000000 : ℝ)*X 2 0+(1357456187/2500000000 : ℝ)*X 2 1+(-1739163917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((133172649/312500000 : ℝ)*X 0 0+(4508726183/10000000000 : ℝ)*X 0 1+(2012946881/5000000000 : ℝ)*X 0 2+(133172649/312500000 : ℝ)*X 1 0+(4508726183/10000000000 : ℝ)*X 1 1+(2012946881/5000000000 : ℝ)*X 1 2+(133172649/312500000 : ℝ)*X 2 0+(4508726183/10000000000 : ℝ)*X 2 1+(2012946881/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1434612691333569923267141547/188000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (648727447/50000000000000 : ℝ)*(base19) + (1234036147/100000000000000 : ℝ)*(base23) + (57937189/100000000000000 : ℝ)*(lower2) + (101127757/50000000000000 : ℝ)*(upper3) + (119719141/100000000000000 : ℝ)*(upper5) + (3378205482219507/100000000000000 : ℝ)*(major0) + (3378205482219507/100000000000000 : ℝ)*(major1) + (3378205482219507/100000000000000 : ℝ)*(major2) + (2353370889913579/50000000000000 : ℝ)*(sp0) + (941352280226451/20000000000000 : ℝ)*(sp1) + (4706761464551003/100000000000000 : ℝ)*(sp2) + (1024818969164513/50000000000000 : ℝ)*(sp3) + (20918759991/100000000000000 : ℝ)*(sp4) + (5036579439/50000000000000 : ℝ)*(sp7) + (64051500358997/3125000000000 : ℝ)*(f.failure) + (4706762698587149/100000000000000 : ℝ)*(f.sum) + (8860272994443/1504000000000000000000000000 : ℝ)*base65 + (2761266313992161151/376000000000000000000000000000000 : ℝ)*base68 + (1670132598663838849/376000000000000000000000000000000 : ℝ)*base69 + (689003699752161151/376000000000000000000000000000000 : ℝ)*base72 + (1157228263851/1504000000000000000000000000 : ℝ)*base73 + (4666620038736161151/376000000000000000000000000000000 : ℝ)*base76 + (716726934175838849/376000000000000000000000000000000 : ℝ)*base77 + (9679502678416161151/376000000000000000000000000000000 : ℝ)*base80 + (1534247102543/300800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (682433/312500000000000000000 : ℝ)*base90 + (682433/312500000000000000000 : ℝ)*base92 + (682433/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2847104634072459879627/1504000000000000000000000000 : ℝ) := by norm_num
    linear_combination (596008329/100000000000000 : ℝ)*(base19) + (20463231/4000000000000 : ℝ)*(base23) + (100961731/100000000000000 : ℝ)*(lower1) + (7617051/100000000000000 : ℝ)*(upper2) + (40811793/100000000000000 : ℝ)*(upper3) + (35254119/50000000000000 : ℝ)*(upper5) + (3413577669091717/100000000000000 : ℝ)*(major0) + (3413577669091717/100000000000000 : ℝ)*(major1) + (3413577669091717/100000000000000 : ℝ)*(major2) + (493366273/20000000000000 : ℝ)*(sp1) + (2378023003825507/50000000000000 : ℝ)*(sp4) + (118901073620283/2500000000000 : ℝ)*(sp5) + (4756045496070239/100000000000000 : ℝ)*(sp6) + (2071109267431687/100000000000000 : ℝ)*(sp7) + (2071109267431687/100000000000000 : ℝ)*(f.failure) + (2378023003825507/50000000000000 : ℝ)*(f.sum) + (12611055494311/4512000000000000000000000000 : ℝ)*base65 + (4547235843163939957/1128000000000000000000000000000000 : ℝ)*base67 + (37671187847692060043/1128000000000000000000000000000000 : ℝ)*base70 + (2310740748787939957/1128000000000000000000000000000000 : ℝ)*base71 + (18460986062791/4512000000000000000000000000 : ℝ)*base73 + (4316926421476060043/1128000000000000000000000000000000 : ℝ)*base76 + (15513691893931939957/1128000000000000000000000000000000 : ℝ)*base77 + (21230771223268060043/1128000000000000000000000000000000 : ℝ)*base80 + (9198020841991/4512000000000000000000000000 : ℝ)*base81 + (24935843/10000000000000000000000 : ℝ)*base90 + (24935843/10000000000000000000000 : ℝ)*base92 + (24935843/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1530_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5489/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10983/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1530_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1530_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3983/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10571/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10983/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1530_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1530_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1530_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3983/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10571/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10983/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1530_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

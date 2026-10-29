-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1457_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:07:03.316993+00:00
-- url     : https://prove2.me/submissions/87861d64-463e-4b17-b667-93192fbecccc

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
theorem support_rectangle_w1457_s6_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-487159217/2500000000 : ℝ)*x 0 + (2703389339/5000000000 : ℝ)*x 1 + (131187379/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (487159217/2500000000 : ℝ)^4417 ≤ (11895241246089/100000000000000 : ℝ)^3393 := by
    have hnat : (487159217 : ℕ)^4417*100000000000000^3393 ≤ 11895241246089^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487159217 2500000000 11895241246089 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703389339/5000000000 : ℝ)^4417 ≤ (11227422108553/25000000000000 : ℝ)^3393 := by
    have hnat : (2703389339 : ℕ)^4417*25000000000000^3393 ≤ 11227422108553^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703389339 5000000000 11227422108553 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131187379/250000000 : ℝ)^4417 ≤ (43195070299281/100000000000000 : ℝ)^3393 := by
    have hnat : (131187379 : ℕ)^4417*100000000000000^3393 ≤ 43195070299281^3393*250000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131187379 250000000 43195070299281 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-487159217/2500000000 : ℝ), (2703389339/5000000000 : ℝ), (131187379/250000000 : ℝ)] ![(11895241246089/100000000000000 : ℝ), (11227422108553/25000000000000 : ℝ), (43195070299281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-487159217/2500000000 : ℝ)|^4417 ≤ (11895241246089/100000000000000 : ℝ)^3393
        have hw : |(-487159217/2500000000 : ℝ)|=(487159217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703389339/5000000000 : ℝ)|^4417 ≤ (11227422108553/25000000000000 : ℝ)^3393
        have hw : |(2703389339/5000000000 : ℝ)|=(2703389339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131187379/250000000 : ℝ)|^4417 ≤ (43195070299281/100000000000000 : ℝ)^3393
        have hw : |(131187379/250000000 : ℝ)|=(131187379/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s6_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069344787/2000000000 : ℝ)*x 0 + (-253713831/1250000000 : ℝ)*x 1 + (262374781/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069344787/2000000000 : ℝ)^4417 ≤ (11065352384081/25000000000000 : ℝ)^3393 := by
    have hnat : (1069344787 : ℕ)^4417*25000000000000^3393 ≤ 11065352384081^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069344787 2000000000 11065352384081 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253713831/1250000000 : ℝ)^4417 ≤ (2508703043211/20000000000000 : ℝ)^3393 := by
    have hnat : (253713831 : ℕ)^4417*20000000000000^3393 ≤ 2508703043211^3393*1250000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253713831 1250000000 2508703043211 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262374781/500000000 : ℝ)^4417 ≤ (43195075228561/100000000000000 : ℝ)^3393 := by
    have hnat : (262374781 : ℕ)^4417*100000000000000^3393 ≤ 43195075228561^3393*500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262374781 500000000 43195075228561 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069344787/2000000000 : ℝ), (-253713831/1250000000 : ℝ), (262374781/500000000 : ℝ)] ![(11065352384081/25000000000000 : ℝ), (2508703043211/20000000000000 : ℝ), (43195075228561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069344787/2000000000 : ℝ)|^4417 ≤ (11065352384081/25000000000000 : ℝ)^3393
        have hw : |(1069344787/2000000000 : ℝ)|=(1069344787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-253713831/1250000000 : ℝ)|^4417 ≤ (2508703043211/20000000000000 : ℝ)^3393
        have hw : |(-253713831/1250000000 : ℝ)|=(253713831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262374781/500000000 : ℝ)|^4417 ≤ (43195075228561/100000000000000 : ℝ)^3393
        have hw : |(262374781/500000000 : ℝ)|=(262374781/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s6_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069344617/2000000000 : ℝ)*x 0 + (2623748133/5000000000 : ℝ)*x 1 + (-2029710927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069344617/2000000000 : ℝ)^4417 ≤ (4426140037623/10000000000000 : ℝ)^3393 := by
    have hnat : (1069344617 : ℕ)^4417*10000000000000^3393 ≤ 4426140037623^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069344617 2000000000 4426140037623 10000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623748133/5000000000 : ℝ)^4417 ≤ (8639016430197/20000000000000 : ℝ)^3393 := by
    have hnat : (2623748133 : ℕ)^4417*20000000000000^3393 ≤ 8639016430197^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623748133 5000000000 8639016430197 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2029710927/10000000000 : ℝ)^4417 ≤ (12543517460623/100000000000000 : ℝ)^3393 := by
    have hnat : (2029710927 : ℕ)^4417*100000000000000^3393 ≤ 12543517460623^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029710927 10000000000 12543517460623 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069344617/2000000000 : ℝ), (2623748133/5000000000 : ℝ), (-2029710927/10000000000 : ℝ)] ![(4426140037623/10000000000000 : ℝ), (8639016430197/20000000000000 : ℝ), (12543517460623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069344617/2000000000 : ℝ)|^4417 ≤ (4426140037623/10000000000000 : ℝ)^3393
        have hw : |(1069344617/2000000000 : ℝ)|=(1069344617/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623748133/5000000000 : ℝ)|^4417 ≤ (8639016430197/20000000000000 : ℝ)^3393
        have hw : |(2623748133/5000000000 : ℝ)|=(2623748133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2029710927/10000000000 : ℝ)|^4417 ≤ (12543517460623/100000000000000 : ℝ)^3393
        have hw : |(-2029710927/10000000000 : ℝ)|=(2029710927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s6_3 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (429742117/1000000000 : ℝ)*x 0 + (4126493847/10000000000 : ℝ)*x 1 + (4474613289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429742117/1000000000 : ℝ)^4417 ≤ (8326277431651/25000000000000 : ℝ)^3393 := by
    have hnat : (429742117 : ℕ)^4417*25000000000000^3393 ≤ 8326277431651^3393*1000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429742117 1000000000 8326277431651 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4126493847/10000000000 : ℝ)^4417 ≤ (7897769521217/25000000000000 : ℝ)^3393 := by
    have hnat : (4126493847 : ℕ)^4417*25000000000000^3393 ≤ 7897769521217^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126493847 10000000000 7897769521217 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4474613289/10000000000 : ℝ)^4417 ≤ (35103812170619/100000000000000 : ℝ)^3393 := by
    have hnat : (4474613289 : ℕ)^4417*100000000000000^3393 ≤ 35103812170619^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474613289 10000000000 35103812170619 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(429742117/1000000000 : ℝ), (4126493847/10000000000 : ℝ), (4474613289/10000000000 : ℝ)] ![(8326277431651/25000000000000 : ℝ), (7897769521217/25000000000000 : ℝ), (35103812170619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(429742117/1000000000 : ℝ)|^4417 ≤ (8326277431651/25000000000000 : ℝ)^3393
        have hw : |(429742117/1000000000 : ℝ)|=(429742117/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4126493847/10000000000 : ℝ)|^4417 ≤ (7897769521217/25000000000000 : ℝ)^3393
        have hw : |(4126493847/10000000000 : ℝ)|=(4126493847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4474613289/10000000000 : ℝ)|^4417 ≤ (35103812170619/100000000000000 : ℝ)^3393
        have hw : |(4474613289/10000000000 : ℝ)|=(4474613289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s6_4 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-194864733/1000000000 : ℝ)*x 0 + (1312018023/2500000000 : ℝ)*x 1 + (5406199221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (194864733/1000000000 : ℝ)^4417 ≤ (371728887011/3125000000000 : ℝ)^3393 := by
    have hnat : (194864733 : ℕ)^4417*3125000000000^3393 ≤ 371728887011^3393*1000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194864733 1000000000 371728887011 3125000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1312018023/2500000000 : ℝ)^4417 ≤ (43201252705127/100000000000000 : ℝ)^3393 := by
    have hnat : (1312018023 : ℕ)^4417*100000000000000^3393 ≤ 43201252705127^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312018023 2500000000 43201252705127 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406199221/10000000000 : ℝ)^4417 ≤ (44903422884513/100000000000000 : ℝ)^3393 := by
    have hnat : (5406199221 : ℕ)^4417*100000000000000^3393 ≤ 44903422884513^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406199221 10000000000 44903422884513 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-194864733/1000000000 : ℝ), (1312018023/2500000000 : ℝ), (5406199221/10000000000 : ℝ)] ![(371728887011/3125000000000 : ℝ), (43201252705127/100000000000000 : ℝ), (44903422884513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-194864733/1000000000 : ℝ)|^4417 ≤ (371728887011/3125000000000 : ℝ)^3393
        have hw : |(-194864733/1000000000 : ℝ)|=(194864733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1312018023/2500000000 : ℝ)|^4417 ≤ (43201252705127/100000000000000 : ℝ)^3393
        have hw : |(1312018023/2500000000 : ℝ)|=(1312018023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406199221/10000000000 : ℝ)|^4417 ≤ (44903422884513/100000000000000 : ℝ)^3393
        have hw : |(5406199221/10000000000 : ℝ)|=(5406199221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s6_5 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652601753/5000000000 : ℝ)*x 0 + (-374201499/2000000000 : ℝ)*x 1 + (1351549849/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652601753/5000000000 : ℝ)^4417 ≤ (43814486526791/100000000000000 : ℝ)^3393 := by
    have hnat : (2652601753 : ℕ)^4417*100000000000000^3393 ≤ 43814486526791^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652601753 5000000000 43814486526791 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (374201499/2000000000 : ℝ)^4417 ≤ (11282088676241/100000000000000 : ℝ)^3393 := by
    have hnat : (374201499 : ℕ)^4417*100000000000000^3393 ≤ 11282088676241^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374201499 2000000000 11282088676241 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351549849/2500000000 : ℝ)^4417 ≤ (22451712388361/50000000000000 : ℝ)^3393 := by
    have hnat : (1351549849 : ℕ)^4417*50000000000000^3393 ≤ 22451712388361^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351549849 2500000000 22451712388361 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652601753/5000000000 : ℝ), (-374201499/2000000000 : ℝ), (1351549849/2500000000 : ℝ)] ![(43814486526791/100000000000000 : ℝ), (11282088676241/100000000000000 : ℝ), (22451712388361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652601753/5000000000 : ℝ)|^4417 ≤ (43814486526791/100000000000000 : ℝ)^3393
        have hw : |(2652601753/5000000000 : ℝ)|=(2652601753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-374201499/2000000000 : ℝ)|^4417 ≤ (11282088676241/100000000000000 : ℝ)^3393
        have hw : |(-374201499/2000000000 : ℝ)|=(374201499/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351549849/2500000000 : ℝ)|^4417 ≤ (22451712388361/50000000000000 : ℝ)^3393
        have hw : |(1351549849/2500000000 : ℝ)|=(1351549849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s6_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305202959/10000000000 : ℝ)*x 0 + (1351550021/2500000000 : ℝ)*x 1 + (-1871007297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305202959/10000000000 : ℝ)^4417 ≤ (21907240322927/50000000000000 : ℝ)^3393 := by
    have hnat : (5305202959 : ℕ)^4417*50000000000000^3393 ≤ 21907240322927^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305202959 10000000000 21907240322927 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351550021/2500000000 : ℝ)^4417 ≤ (8980686443161/20000000000000 : ℝ)^3393 := by
    have hnat : (1351550021 : ℕ)^4417*20000000000000^3393 ≤ 8980686443161^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351550021 2500000000 8980686443161 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1871007297/10000000000 : ℝ)^4417 ≤ (2256417424397/20000000000000 : ℝ)^3393 := by
    have hnat : (1871007297 : ℕ)^4417*20000000000000^3393 ≤ 2256417424397^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871007297 10000000000 2256417424397 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305202959/10000000000 : ℝ), (1351550021/2500000000 : ℝ), (-1871007297/10000000000 : ℝ)] ![(21907240322927/50000000000000 : ℝ), (8980686443161/20000000000000 : ℝ), (2256417424397/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305202959/10000000000 : ℝ)|^4417 ≤ (21907240322927/50000000000000 : ℝ)^3393
        have hw : |(5305202959/10000000000 : ℝ)|=(5305202959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351550021/2500000000 : ℝ)|^4417 ≤ (8980686443161/20000000000000 : ℝ)^3393
        have hw : |(1351550021/2500000000 : ℝ)|=(1351550021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1871007297/10000000000 : ℝ)|^4417 ≤ (2256417424397/20000000000000 : ℝ)^3393
        have hw : |(-1871007297/10000000000 : ℝ)|=(1871007297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s6_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2148722497/5000000000 : ℝ)*x 0 + (4473354929/10000000000 : ℝ)*x 1 + (2063879557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148722497/5000000000 : ℝ)^4417 ≤ (33305350086237/100000000000000 : ℝ)^3393 := by
    have hnat : (2148722497 : ℕ)^4417*100000000000000^3393 ≤ 33305350086237^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148722497 5000000000 33305350086237 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4473354929/10000000000 : ℝ)^4417 ≤ (17545480705691/50000000000000 : ℝ)^3393 := by
    have hnat : (4473354929 : ℕ)^4417*50000000000000^3393 ≤ 17545480705691^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473354929 10000000000 17545480705691 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2063879557/5000000000 : ℝ)^4417 ≤ (632073769811/2000000000000 : ℝ)^3393 := by
    have hnat : (2063879557 : ℕ)^4417*2000000000000^3393 ≤ 632073769811^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063879557 5000000000 632073769811 2000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148722497/5000000000 : ℝ), (4473354929/10000000000 : ℝ), (2063879557/5000000000 : ℝ)] ![(33305350086237/100000000000000 : ℝ), (17545480705691/50000000000000 : ℝ), (632073769811/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148722497/5000000000 : ℝ)|^4417 ≤ (33305350086237/100000000000000 : ℝ)^3393
        have hw : |(2148722497/5000000000 : ℝ)|=(2148722497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4473354929/10000000000 : ℝ)|^4417 ≤ (17545480705691/50000000000000 : ℝ)^3393
        have hw : |(4473354929/10000000000 : ℝ)|=(4473354929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2063879557/5000000000 : ℝ)|^4417 ≤ (632073769811/2000000000000 : ℝ)^3393
        have hw : |(2063879557/5000000000 : ℝ)|=(2063879557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1457_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2849/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14771/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7387/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7387/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7387/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7387/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7387/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7387/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11393/100000 : ℝ) ^ (69/16 : ℝ) ≤ (4272890852736237/50000000000000000000 : ℝ) := by
    have hpowers : (11393/100000 : ℝ)^69 ≤ (4272890852736237/50000000000000000000 : ℝ)^16 := by
      have hnat : (11393 : ℕ)^69*50000000000000000000^16 ≤ 4272890852736237^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11393 100000 4272890852736237 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11393/100000 : ℝ)) (X := (4272890852736237/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hpowhi : (7387/50000 : ℝ) ^ (69/16 : ℝ) ≤ (2620960847029761/10000000000000000000 : ℝ) := by
    have hpowers : (7387/50000 : ℝ)^69 ≤ (2620960847029761/10000000000000000000 : ℝ)^16 := by
      have hnat : (7387 : ℕ)^69*10000000000000000000^16 ≤ 2620960847029761^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7387 50000 2620960847029761 10000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7387/50000 : ℝ)) (X := (2620960847029761/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004272890852736237/25000000000000000000 : ℝ) ≤ (1250049537511907/1250000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (25004272890852736237/25000000000000000000 : ℝ)^16 ≤ (1250049537511907/1250000000000000 : ℝ)^69 := by
      have hnat : (25004272890852736237 : ℕ)^16*1250000000000000^69 ≤ 1250049537511907^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004272890852736237 25000000000000000000 1250049537511907 1250000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250049537511907/1250000000000000 : ℝ)) (X := (25004272890852736237/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (25008688847543942521/25000000000000000000 : ℝ) ≤ (100008058145379/100000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (25008688847543942521/25000000000000000000 : ℝ)^16 ≤ (100008058145379/100000000000000 : ℝ)^69 := by
      have hnat : (25008688847543942521 : ℕ)^16*100000000000000^69 ≤ 100008058145379^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008688847543942521 25000000000000000000 100008058145379 100000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100008058145379/100000000000000 : ℝ)) (X := (25008688847543942521/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002620960847029761/5000000000000000000 : ℝ) ≤ (156268989515321/156250000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (5002620960847029761/5000000000000000000 : ℝ)^16 ≤ (156268989515321/156250000000000 : ℝ)^69 := by
      have hnat : (5002620960847029761 : ℕ)^16*156250000000000^69 ≤ 156268989515321^69*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002620960847029761 5000000000000000000 156268989515321 156250000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156268989515321/156250000000000 : ℝ)) (X := (5002620960847029761/5000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4272890852736237/50000000000000000000 : ℝ) ≤ ((2112625543408248397/2113125000000000000 : ℝ)+2*(102378610661/84525000000000 : ℝ)*(11393/100000 : ℝ))^(69/16 : ℝ) := by
    rw [show (2112625543408248397/2113125000000000000 : ℝ)+2*(102378610661/84525000000000 : ℝ)*(11393/100000 : ℝ)=(1250049537511907/1250000000000000 : ℝ) by norm_num, show 1+2*(4272890852736237/50000000000000000000 : ℝ)=(25004272890852736237/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2620960847029761/10000000000000000000 : ℝ)+(4272890852736237/50000000000000000000 : ℝ) ≤ ((2112625543408248397/2113125000000000000 : ℝ)+(102378610661/84525000000000 : ℝ)*((7387/50000 : ℝ)+(11393/100000 : ℝ)))^(69/16 : ℝ) := by
    rw [show (2112625543408248397/2113125000000000000 : ℝ)+(102378610661/84525000000000 : ℝ)*((7387/50000 : ℝ)+(11393/100000 : ℝ))=(100008058145379/100000000000000 : ℝ) by norm_num, show 1+(2620960847029761/10000000000000000000 : ℝ)+(4272890852736237/50000000000000000000 : ℝ)=(25008688847543942521/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2620960847029761/10000000000000000000 : ℝ) ≤ ((2112625543408248397/2113125000000000000 : ℝ)+2*(102378610661/84525000000000 : ℝ)*(7387/50000 : ℝ))^(69/16 : ℝ) := by
    rw [show (2112625543408248397/2113125000000000000 : ℝ)+2*(102378610661/84525000000000 : ℝ)*(7387/50000 : ℝ)=(156268989515321/156250000000000 : ℝ) by norm_num, show 1+2*(2620960847029761/10000000000000000000 : ℝ)=(5002620960847029761/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2112625543408248397/2113125000000000000 : ℝ)*(X 1 0+X 2 0)+(102378610661/84525000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (7387/50000 : ℝ)) (c := (2112625543408248397/2113125000000000000 : ℝ)) (alpha := (102378610661/84525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2112625543408248397/2113125000000000000 : ℝ)*(X 0 1+X 2 1)+(102378610661/84525000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (7387/50000 : ℝ)) (c := (2112625543408248397/2113125000000000000 : ℝ)) (alpha := (102378610661/84525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2112625543408248397/2113125000000000000 : ℝ)*(X 0 2+X 1 2)+(102378610661/84525000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (11393/100000 : ℝ)) (hi := (7387/50000 : ℝ)) (c := (2112625543408248397/2113125000000000000 : ℝ)) (alpha := (102378610661/84525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-487159217/2500000000 : ℝ)*X 0 0+(2703389339/5000000000 : ℝ)*X 0 1+(131187379/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069344787/2000000000 : ℝ)*X 1 0+(-253713831/1250000000 : ℝ)*X 1 1+(262374781/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069344617/2000000000 : ℝ)*X 2 0+(2623748133/5000000000 : ℝ)*X 2 1+(-2029710927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((429742117/1000000000 : ℝ)*X 0 0+(4126493847/10000000000 : ℝ)*X 0 1+(4474613289/10000000000 : ℝ)*X 0 2+(429742117/1000000000 : ℝ)*X 1 0+(4126493847/10000000000 : ℝ)*X 1 1+(4474613289/10000000000 : ℝ)*X 1 2+(429742117/1000000000 : ℝ)*X 2 0+(4126493847/10000000000 : ℝ)*X 2 1+(4474613289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-194864733/1000000000 : ℝ)*X 0 0+(1312018023/2500000000 : ℝ)*X 0 1+(5406199221/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652601753/5000000000 : ℝ)*X 1 0+(-374201499/2000000000 : ℝ)*X 1 1+(1351549849/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305202959/10000000000 : ℝ)*X 2 0+(1351550021/2500000000 : ℝ)*X 2 1+(-1871007297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2148722497/5000000000 : ℝ)*X 0 0+(4473354929/10000000000 : ℝ)*X 0 1+(2063879557/5000000000 : ℝ)*X 0 2+(2148722497/5000000000 : ℝ)*X 1 0+(4473354929/10000000000 : ℝ)*X 1 1+(2063879557/5000000000 : ℝ)*X 1 2+(2148722497/5000000000 : ℝ)*X 2 0+(4473354929/10000000000 : ℝ)*X 2 1+(2063879557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22245100052356294594650717/4402343750000000000000000000000 : ℝ) := by norm_num
    linear_combination (313470617/12500000000000 : ℝ)*(base19) + (1344747159/100000000000000 : ℝ)*(base23) + (52201349/50000000000000 : ℝ)*(upper2) + (127975941/20000000000000 : ℝ)*(upper3) + (192585063/100000000000000 : ℝ)*(upper4) + (571929468506811/12500000000000 : ℝ)*(major0) + (571929468506811/12500000000000 : ℝ)*(major1) + (571929468506811/12500000000000 : ℝ)*(major2) + (1569549248807597/25000000000000 : ℝ)*(sp0) + (1569561865638637/25000000000000 : ℝ)*(sp1) + (3139124312786163/50000000000000 : ℝ)*(sp2) + (287259594263997/10000000000000 : ℝ)*(sp3) + (6621886137/12500000000000 : ℝ)*(sp4) + (6353678937/25000000000000 : ℝ)*(sp7) + (2872621357355717/100000000000000 : ℝ)*(f.failure) + (1569562492579871/25000000000000 : ℝ)*(f.sum) + (186250457889/1408750000000000000000000000 : ℝ)*base66 + (28571816500161057/4402343750000000000000000000000 : ℝ)*base67 + (17232115999995193/4402343750000000000000000000000 : ℝ)*base70 + (47366252808306489/8804687500000000000000000000000 : ℝ)*base71 + (11462427249803/2817500000000000000000000000 : ℝ)*base74 + (49480884062213943/4402343750000000000000000000000 : ℝ)*base76 + (14734539708776443/4402343750000000000000000000000 : ℝ)*base78 + (23862070636911659/2201171875000000000000000000000 : ℝ)*base80 + (717900777009/88046875000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4177571/1000000000000000000000 : ℝ)*base90 + (4177571/1000000000000000000000 : ℝ)*base92 + (4177571/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6413027870269769422388019/628906250000000000000000000000 : ℝ) := by norm_num
    linear_combination (963844177/100000000000000 : ℝ)*(base19) + (460938797/100000000000000 : ℝ)*(base23) + (220872637/100000000000000 : ℝ)*(lower1) + (166284027/50000000000000 : ℝ)*(upper3) + (11450569/100000000000000 : ℝ)*(lower4) + (2304386495610353/50000000000000 : ℝ)*(major0) + (2304386495610353/50000000000000 : ℝ)*(major1) + (2304386495610353/50000000000000 : ℝ)*(major2) + (16298200839/100000000000000 : ℝ)*(sp2) + (726877161/100000000000000 : ℝ)*(sp3) + (3161996988888899/50000000000000 : ℝ)*(sp4) + (3161996506966811/50000000000000 : ℝ)*(sp5) + (3161988609319081/50000000000000 : ℝ)*(sp6) + (289355093788269/10000000000000 : ℝ)*(sp7) + (57871033295197/2000000000000 : ℝ)*(f.failure) + (3161996988888899/50000000000000 : ℝ)*(f.sum) + (7679786644199/1207500000000000000000000000 : ℝ)*base66 + (22797473782296529/5031250000000000000000000000000 : ℝ)*base68 + (14263989544609029/5031250000000000000000000000000 : ℝ)*base70 + (78052724945077779/5031250000000000000000000000000 : ℝ)*base72 + (3205935085153/2415000000000000000000000000 : ℝ)*base74 + (34297405469421529/5031250000000000000000000000000 : ℝ)*base76 + (80156385633015971/5031250000000000000000000000000 : ℝ)*base77 + (38291506842484029/5031250000000000000000000000000 : ℝ)*base80 + (9325996065839/1207500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (20811/20000000000000000000 : ℝ)*base90 + (20811/20000000000000000000 : ℝ)*base92 + (20811/20000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1457_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1457_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1457_s7_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346718319/10000000000 : ℝ)*x 0 + (5247515097/10000000000 : ℝ)*x 1 + (-507423057/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346718319/10000000000 : ℝ)^4417 ≤ (11065337253763/25000000000000 : ℝ)^3393 := by
    have hnat : (5346718319 : ℕ)^4417*25000000000000^3393 ≤ 11065337253763^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346718319 10000000000 11065337253763 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247515097/10000000000 : ℝ)^4417 ≤ (21597641970419/50000000000000 : ℝ)^3393 := by
    have hnat : (5247515097 : ℕ)^4417*50000000000000^3393 ≤ 21597641970419^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247515097 10000000000 21597641970419 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (507423057/2500000000 : ℝ)^4417 ≤ (12543367026463/100000000000000 : ℝ)^3393 := by
    have hnat : (507423057 : ℕ)^4417*100000000000000^3393 ≤ 12543367026463^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507423057 2500000000 12543367026463 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346718319/10000000000 : ℝ), (5247515097/10000000000 : ℝ), (-507423057/2500000000 : ℝ)] ![(11065337253763/25000000000000 : ℝ), (21597641970419/50000000000000 : ℝ), (12543367026463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346718319/10000000000 : ℝ)|^4417 ≤ (11065337253763/25000000000000 : ℝ)^3393
        have hw : |(5346718319/10000000000 : ℝ)|=(5346718319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247515097/10000000000 : ℝ)|^4417 ≤ (21597641970419/50000000000000 : ℝ)^3393
        have hw : |(5247515097/10000000000 : ℝ)|=(5247515097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-507423057/2500000000 : ℝ)|^4417 ≤ (12543367026463/100000000000000 : ℝ)^3393
        have hw : |(-507423057/2500000000 : ℝ)|=(507423057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s7_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1948649329/10000000000 : ℝ)*x 0 + (1049618183/2000000000 : ℝ)*x 1 + (2703089549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1948649329/10000000000 : ℝ)^4417 ≤ (11895340269799/100000000000000 : ℝ)^3393 := by
    have hnat : (1948649329 : ℕ)^4417*100000000000000^3393 ≤ 11895340269799^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948649329 10000000000 11895340269799 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049618183/2000000000 : ℝ)^4417 ≤ (43201454415933/100000000000000 : ℝ)^3393 := by
    have hnat : (1049618183 : ℕ)^4417*100000000000000^3393 ≤ 43201454415933^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049618183 2000000000 43201454415933 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703089549/5000000000 : ℝ)^4417 ≤ (44903205302283/100000000000000 : ℝ)^3393 := by
    have hnat : (2703089549 : ℕ)^4417*100000000000000^3393 ≤ 44903205302283^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703089549 5000000000 44903205302283 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1948649329/10000000000 : ℝ), (1049618183/2000000000 : ℝ), (2703089549/5000000000 : ℝ)] ![(11895340269799/100000000000000 : ℝ), (43201454415933/100000000000000 : ℝ), (44903205302283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1948649329/10000000000 : ℝ)|^4417 ≤ (11895340269799/100000000000000 : ℝ)^3393
        have hw : |(-1948649329/10000000000 : ℝ)|=(1948649329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049618183/2000000000 : ℝ)|^4417 ≤ (43201454415933/100000000000000 : ℝ)^3393
        have hw : |(1049618183/2000000000 : ℝ)|=(1049618183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703089549/5000000000 : ℝ)|^4417 ≤ (44903205302283/100000000000000 : ℝ)^3393
        have hw : |(2703089549/5000000000 : ℝ)|=(2703089549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s7_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42441669/80000000 : ℝ)*x 0 + (-374205657/2000000000 : ℝ)*x 1 + (5406179213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42441669/80000000 : ℝ)^4417 ≤ (43814541562481/100000000000000 : ℝ)^3393 := by
    have hnat : (42441669 : ℕ)^4417*100000000000000^3393 ≤ 43814541562481^3393*80000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42441669 80000000 43814541562481 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (374205657/2000000000 : ℝ)^4417 ≤ (2256450374691/20000000000000 : ℝ)^3393 := by
    have hnat : (374205657 : ℕ)^4417*20000000000000^3393 ≤ 2256450374691^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374205657 2000000000 2256450374691 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406179213/10000000000 : ℝ)^4417 ≤ (11225801636433/25000000000000 : ℝ)^3393 := by
    have hnat : (5406179213 : ℕ)^4417*25000000000000^3393 ≤ 11225801636433^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406179213 10000000000 11225801636433 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42441669/80000000 : ℝ), (-374205657/2000000000 : ℝ), (5406179213/10000000000 : ℝ)] ![(43814541562481/100000000000000 : ℝ), (2256450374691/20000000000000 : ℝ), (11225801636433/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42441669/80000000 : ℝ)|^4417 ≤ (43814541562481/100000000000000 : ℝ)^3393
        have hw : |(42441669/80000000 : ℝ)|=(42441669/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-374205657/2000000000 : ℝ)|^4417 ≤ (2256450374691/20000000000000 : ℝ)^3393
        have hw : |(-374205657/2000000000 : ℝ)|=(374205657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406179213/10000000000 : ℝ)|^4417 ≤ (11225801636433/25000000000000 : ℝ)^3393
        have hw : |(5406179213/10000000000 : ℝ)|=(5406179213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s7_3 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305208811/10000000000 : ℝ)*x 0 + (67577239/125000000 : ℝ)*x 1 + (-1871028159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305208811/10000000000 : ℝ)^4417 ≤ (8762908712443/20000000000000 : ℝ)^3393 := by
    have hnat : (5305208811 : ℕ)^4417*20000000000000^3393 ≤ 8762908712443^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305208811 10000000000 8762908712443 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67577239/125000000 : ℝ)^4417 ≤ (140322517313/312500000000 : ℝ)^3393 := by
    have hnat : (67577239 : ℕ)^4417*312500000000^3393 ≤ 140322517313^3393*125000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67577239 125000000 140322517313 312500000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1871028159/10000000000 : ℝ)^4417 ≤ (11282250884379/100000000000000 : ℝ)^3393 := by
    have hnat : (1871028159 : ℕ)^4417*100000000000000^3393 ≤ 11282250884379^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871028159 10000000000 11282250884379 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305208811/10000000000 : ℝ), (67577239/125000000 : ℝ), (-1871028159/10000000000 : ℝ)] ![(8762908712443/20000000000000 : ℝ), (140322517313/312500000000 : ℝ), (11282250884379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305208811/10000000000 : ℝ)|^4417 ≤ (8762908712443/20000000000000 : ℝ)^3393
        have hw : |(5305208811/10000000000 : ℝ)|=(5305208811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67577239/125000000 : ℝ)|^4417 ≤ (140322517313/312500000000 : ℝ)^3393
        have hw : |(67577239/125000000 : ℝ)|=(67577239/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1871028159/10000000000 : ℝ)|^4417 ≤ (11282250884379/100000000000000 : ℝ)^3393
        have hw : |(-1871028159/10000000000 : ℝ)|=(1871028159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s7_4 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268590417/625000000 : ℝ)*x 0 + (2236655703/5000000000 : ℝ)*x 1 + (4127802007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268590417/625000000 : ℝ)^4417 ≤ (6661073403109/20000000000000 : ℝ)^3393 := by
    have hnat : (268590417 : ℕ)^4417*20000000000000^3393 ≤ 6661073403109^3393*625000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268590417 625000000 6661073403109 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2236655703/5000000000 : ℝ)^4417 ≤ (35090516960641/100000000000000 : ℝ)^3393 := by
    have hnat : (2236655703 : ℕ)^4417*100000000000000^3393 ≤ 35090516960641^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236655703 5000000000 35090516960641 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4127802007/10000000000 : ℝ)^4417 ≤ (31604116008221/100000000000000 : ℝ)^3393 := by
    have hnat : (4127802007 : ℕ)^4417*100000000000000^3393 ≤ 31604116008221^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127802007 10000000000 31604116008221 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268590417/625000000 : ℝ), (2236655703/5000000000 : ℝ), (4127802007/10000000000 : ℝ)] ![(6661073403109/20000000000000 : ℝ), (35090516960641/100000000000000 : ℝ), (31604116008221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268590417/625000000 : ℝ)|^4417 ≤ (6661073403109/20000000000000 : ℝ)^3393
        have hw : |(268590417/625000000 : ℝ)|=(268590417/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2236655703/5000000000 : ℝ)|^4417 ≤ (35090516960641/100000000000000 : ℝ)^3393
        have hw : |(2236655703/5000000000 : ℝ)|=(2236655703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4127802007/10000000000 : ℝ)|^4417 ≤ (31604116008221/100000000000000 : ℝ)^3393
        have hw : |(4127802007/10000000000 : ℝ)|=(4127802007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1457_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2849/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1477/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2849/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2849/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2849/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2849/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2849/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2849/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2849/25000 : ℝ) ^ (69/16 : ℝ) ≤ (1711098047033687/20000000000000000000 : ℝ) := by
    have hpowers : (2849/25000 : ℝ)^69 ≤ (1711098047033687/20000000000000000000 : ℝ)^16 := by
      have hnat : (2849 : ℕ)^69*20000000000000000000^16 ≤ 1711098047033687^16*25000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2849 25000 1711098047033687 20000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2849/25000 : ℝ)) (X := (1711098047033687/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hpowhi : (14771/100000 : ℝ) ^ (69/16 : ℝ) ≤ (2618666459682297/10000000000000000000 : ℝ) := by
    have hpowers : (14771/100000 : ℝ)^69 ≤ (2618666459682297/10000000000000000000 : ℝ)^16 := by
      have hnat : (14771 : ℕ)^69*10000000000000000000^16 ≤ 2618666459682297^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14771 100000 2618666459682297 10000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14771/100000 : ℝ)) (X := (2618666459682297/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001711098047033687/10000000000000000000 : ℝ) ≤ (5000198375143387/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (10001711098047033687/10000000000000000000 : ℝ)^16 ≤ (5000198375143387/5000000000000000 : ℝ)^69 := by
      have hnat : (10001711098047033687 : ℕ)^16*5000000000000000^69 ≤ 5000198375143387^69*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001711098047033687 10000000000000000000 5000198375143387 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000198375143387/5000000000000000 : ℝ)) (X := (10001711098047033687/10000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (20006948430966398281/20000000000000000000 : ℝ) ≤ (10000805507713269/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (20006948430966398281/20000000000000000000 : ℝ)^16 ≤ (10000805507713269/10000000000000000 : ℝ)^69 := by
      have hnat : (20006948430966398281 : ℕ)^16*10000000000000000^69 ≤ 10000805507713269^69*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20006948430966398281 20000000000000000000 10000805507713269 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000805507713269/10000000000000000 : ℝ)) (X := (20006948430966398281/20000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002618666459682297/5000000000000000000 : ℝ) ≤ (2500303566284941/2500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (5002618666459682297/5000000000000000000 : ℝ)^16 ≤ (2500303566284941/2500000000000000 : ℝ)^69 := by
      have hnat : (5002618666459682297 : ℕ)^16*2500000000000000^69 ≤ 2500303566284941^69*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002618666459682297 5000000000000000000 2500303566284941 2500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500303566284941/2500000000000000 : ℝ)) (X := (5002618666459682297/5000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1711098047033687/20000000000000000000 : ℝ) ≤ ((3374202263295318821/3375000000000000000 : ℝ)+2*(81751485299/67500000000000 : ℝ)*(2849/25000 : ℝ))^(69/16 : ℝ) := by
    rw [show (3374202263295318821/3375000000000000000 : ℝ)+2*(81751485299/67500000000000 : ℝ)*(2849/25000 : ℝ)=(5000198375143387/5000000000000000 : ℝ) by norm_num, show 1+2*(1711098047033687/20000000000000000000 : ℝ)=(10001711098047033687/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2618666459682297/10000000000000000000 : ℝ)+(1711098047033687/20000000000000000000 : ℝ) ≤ ((3374202263295318821/3375000000000000000 : ℝ)+(81751485299/67500000000000 : ℝ)*((14771/100000 : ℝ)+(2849/25000 : ℝ)))^(69/16 : ℝ) := by
    rw [show (3374202263295318821/3375000000000000000 : ℝ)+(81751485299/67500000000000 : ℝ)*((14771/100000 : ℝ)+(2849/25000 : ℝ))=(10000805507713269/10000000000000000 : ℝ) by norm_num, show 1+(2618666459682297/10000000000000000000 : ℝ)+(1711098047033687/20000000000000000000 : ℝ)=(20006948430966398281/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2618666459682297/10000000000000000000 : ℝ) ≤ ((3374202263295318821/3375000000000000000 : ℝ)+2*(81751485299/67500000000000 : ℝ)*(14771/100000 : ℝ))^(69/16 : ℝ) := by
    rw [show (3374202263295318821/3375000000000000000 : ℝ)+2*(81751485299/67500000000000 : ℝ)*(14771/100000 : ℝ)=(2500303566284941/2500000000000000 : ℝ) by norm_num, show 1+2*(2618666459682297/10000000000000000000 : ℝ)=(5002618666459682297/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3374202263295318821/3375000000000000000 : ℝ)*(X 1 0+X 2 0)+(81751485299/67500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (2849/25000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (3374202263295318821/3375000000000000000 : ℝ)) (alpha := (81751485299/67500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3374202263295318821/3375000000000000000 : ℝ)*(X 0 1+X 2 1)+(81751485299/67500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (2849/25000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (3374202263295318821/3375000000000000000 : ℝ)) (alpha := (81751485299/67500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3374202263295318821/3375000000000000000 : ℝ)*(X 0 2+X 1 2)+(81751485299/67500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (2849/25000 : ℝ)) (hi := (14771/100000 : ℝ)) (c := (3374202263295318821/3375000000000000000 : ℝ)) (alpha := (81751485299/67500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5346718319/10000000000 : ℝ)*X 2 0+(5247515097/10000000000 : ℝ)*X 2 1+(-507423057/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s7_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1948649329/10000000000 : ℝ)*X 0 0+(1049618183/2000000000 : ℝ)*X 0 1+(2703089549/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s7_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42441669/80000000 : ℝ)*X 1 0+(-374205657/2000000000 : ℝ)*X 1 1+(5406179213/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s7_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5305208811/10000000000 : ℝ)*X 2 0+(67577239/125000000 : ℝ)*X 2 1+(-1871028159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s7_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((268590417/625000000 : ℝ)*X 0 0+(2236655703/5000000000 : ℝ)*X 0 1+(4127802007/10000000000 : ℝ)*X 0 2+(268590417/625000000 : ℝ)*X 1 0+(2236655703/5000000000 : ℝ)*X 1 1+(4127802007/10000000000 : ℝ)*X 1 2+(268590417/625000000 : ℝ)*X 2 0+(2236655703/5000000000 : ℝ)*X 2 1+(4127802007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s7_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58809477574968977194188449/28125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (108196031/50000000000000 : ℝ)*(base19) + (51380779/10000000000000 : ℝ)*(base23) + (86349499/100000000000000 : ℝ)*(lower1) + (17160257/20000000000000 : ℝ)*(upper3) + (3610197/50000000000000 : ℝ)*(lower4) + (39743997/100000000000000 : ℝ)*(upper5) + (2304963649476131/50000000000000 : ℝ)*(major0) + (2304963649476131/50000000000000 : ℝ)*(major1) + (2304963649476131/50000000000000 : ℝ)*(major2) + (495505523/6250000000000 : ℝ)*(sp0) + (1265115629596043/20000000000000 : ℝ)*(sp1) + (6325577931588153/100000000000000 : ℝ)*(sp2) + (6325569706084057/100000000000000 : ℝ)*(sp3) + (2894276380224173/100000000000000 : ℝ)*(sp4) + (2894276380224173/100000000000000 : ℝ)*(f.failure) + (1265115629596043/20000000000000 : ℝ)*(f.sum) + (9826249962037/3375000000000000000000000000 : ℝ)*base66 + (1032135525808920517/56250000000000000000000000000000 : ℝ)*base67 + (530498176671420517/56250000000000000000000000000000 : ℝ)*base69 + (3883611482078579483/56250000000000000000000000000000 : ℝ)*base72 + (2066800784963/3375000000000000000000000000 : ℝ)*base73 + (554397816227670517/56250000000000000000000000000000 : ℝ)*base75 + (626512606741079483/56250000000000000000000000000000 : ℝ)*base78 + (727984192690170517/56250000000000000000000000000000 : ℝ)*base79 + (2410180638581/1687500000000000000000000000 : ℝ)*base82 + (8586501/1000000000000000000000 : ℝ)*base89 + (8586501/1000000000000000000000 : ℝ)*base91 + (8586501/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1457_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1457_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1457_s8_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-487160191/2500000000 : ℝ)*x 0 + (1351688307/2500000000 : ℝ)*x 1 + (20498117/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (487160191/2500000000 : ℝ)^4417 ≤ (95162177651/800000000000 : ℝ)^3393 := by
    have hnat : (487160191 : ℕ)^4417*800000000000^3393 ≤ 95162177651^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487160191 2500000000 95162177651 800000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351688307/2500000000 : ℝ)^4417 ≤ (22454706622163/50000000000000 : ℝ)^3393 := by
    have hnat : (1351688307 : ℕ)^4417*50000000000000^3393 ≤ 22454706622163^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351688307 2500000000 22454706622163 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20498117/39062500 : ℝ)^4417 ≤ (43195314534561/100000000000000 : ℝ)^3393 := by
    have hnat : (20498117 : ℕ)^4417*100000000000000^3393 ≤ 43195314534561^3393*39062500^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20498117 39062500 43195314534561 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-487160191/2500000000 : ℝ), (1351688307/2500000000 : ℝ), (20498117/39062500 : ℝ)] ![(95162177651/800000000000 : ℝ), (22454706622163/50000000000000 : ℝ), (43195314534561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-487160191/2500000000 : ℝ)|^4417 ≤ (95162177651/800000000000 : ℝ)^3393
        have hw : |(-487160191/2500000000 : ℝ)|=(487160191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351688307/2500000000 : ℝ)|^4417 ≤ (22454706622163/50000000000000 : ℝ)^3393
        have hw : |(1351688307/2500000000 : ℝ)|=(1351688307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20498117/39062500 : ℝ)|^4417 ≤ (43195314534561/100000000000000 : ℝ)^3393
        have hw : |(20498117/39062500 : ℝ)|=(20498117/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s8_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346716481/10000000000 : ℝ)*x 0 + (-2029690887/10000000000 : ℝ)*x 1 + (20498117/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346716481/10000000000 : ℝ)^4417 ≤ (44261329207703/100000000000000 : ℝ)^3393 := by
    have hnat : (5346716481 : ℕ)^4417*100000000000000^3393 ≤ 44261329207703^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346716481 10000000000 44261329207703 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2029690887/10000000000 : ℝ)^4417 ≤ (12543356238083/100000000000000 : ℝ)^3393 := by
    have hnat : (2029690887 : ℕ)^4417*100000000000000^3393 ≤ 12543356238083^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029690887 10000000000 12543356238083 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20498117/39062500 : ℝ)^4417 ≤ (43195314534561/100000000000000 : ℝ)^3393 := by
    have hnat : (20498117 : ℕ)^4417*100000000000000^3393 ≤ 43195314534561^3393*39062500^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20498117 39062500 43195314534561 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346716481/10000000000 : ℝ), (-2029690887/10000000000 : ℝ), (20498117/39062500 : ℝ)] ![(44261329207703/100000000000000 : ℝ), (12543356238083/100000000000000 : ℝ), (43195314534561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346716481/10000000000 : ℝ)|^4417 ≤ (44261329207703/100000000000000 : ℝ)^3393
        have hw : |(5346716481/10000000000 : ℝ)|=(5346716481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2029690887/10000000000 : ℝ)|^4417 ≤ (12543356238083/100000000000000 : ℝ)^3393
        have hw : |(-2029690887/10000000000 : ℝ)|=(2029690887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20498117/39062500 : ℝ)|^4417 ≤ (43195314534561/100000000000000 : ℝ)^3393
        have hw : |(20498117/39062500 : ℝ)|=(20498117/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s8_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346716481/10000000000 : ℝ)*x 0 + (20498117/39062500 : ℝ)*x 1 + (-2029690887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346716481/10000000000 : ℝ)^4417 ≤ (44261329207703/100000000000000 : ℝ)^3393 := by
    have hnat : (5346716481 : ℕ)^4417*100000000000000^3393 ≤ 44261329207703^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346716481 10000000000 44261329207703 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20498117/39062500 : ℝ)^4417 ≤ (43195314534561/100000000000000 : ℝ)^3393 := by
    have hnat : (20498117 : ℕ)^4417*100000000000000^3393 ≤ 43195314534561^3393*39062500^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20498117 39062500 43195314534561 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2029690887/10000000000 : ℝ)^4417 ≤ (12543356238083/100000000000000 : ℝ)^3393 := by
    have hnat : (2029690887 : ℕ)^4417*100000000000000^3393 ≤ 12543356238083^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029690887 10000000000 12543356238083 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346716481/10000000000 : ℝ), (20498117/39062500 : ℝ), (-2029690887/10000000000 : ℝ)] ![(44261329207703/100000000000000 : ℝ), (43195314534561/100000000000000 : ℝ), (12543356238083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346716481/10000000000 : ℝ)|^4417 ≤ (44261329207703/100000000000000 : ℝ)^3393
        have hw : |(5346716481/10000000000 : ℝ)|=(5346716481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20498117/39062500 : ℝ)|^4417 ≤ (43195314534561/100000000000000 : ℝ)^3393
        have hw : |(20498117/39062500 : ℝ)|=(20498117/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2029690887/10000000000 : ℝ)|^4417 ≤ (12543356238083/100000000000000 : ℝ)^3393
        have hw : |(-2029690887/10000000000 : ℝ)|=(2029690887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s8_3 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107435567/250000000 : ℝ)*x 0 + (2063272661/5000000000 : ℝ)*x 1 + (894912313/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107435567/250000000 : ℝ)^4417 ≤ (33305124960937/100000000000000 : ℝ)^3393 := by
    have hnat : (107435567 : ℕ)^4417*100000000000000^3393 ≤ 33305124960937^3393*250000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107435567 250000000 33305124960937 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063272661/5000000000 : ℝ)^4417 ≤ (6318318218531/20000000000000 : ℝ)^3393 := by
    have hnat : (2063272661 : ℕ)^4417*20000000000000^3393 ≤ 6318318218531^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063272661 5000000000 6318318218531 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (894912313/2000000000 : ℝ)^4417 ≤ (35103283927731/100000000000000 : ℝ)^3393 := by
    have hnat : (894912313 : ℕ)^4417*100000000000000^3393 ≤ 35103283927731^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894912313 2000000000 35103283927731 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107435567/250000000 : ℝ), (2063272661/5000000000 : ℝ), (894912313/2000000000 : ℝ)] ![(33305124960937/100000000000000 : ℝ), (6318318218531/20000000000000 : ℝ), (35103283927731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107435567/250000000 : ℝ)|^4417 ≤ (33305124960937/100000000000000 : ℝ)^3393
        have hw : |(107435567/250000000 : ℝ)|=(107435567/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2063272661/5000000000 : ℝ)|^4417 ≤ (6318318218531/20000000000000 : ℝ)^3393
        have hw : |(2063272661/5000000000 : ℝ)|=(2063272661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(894912313/2000000000 : ℝ)|^4417 ≤ (35103283927731/100000000000000 : ℝ)^3393
        have hw : |(894912313/2000000000 : ℝ)|=(894912313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s8_4 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-12179073/62500000 : ℝ)*x 0 + (2624047103/5000000000 : ℝ)*x 1 + (1351543527/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12179073/62500000 : ℝ)^4417 ≤ (1189535895249/10000000000000 : ℝ)^3393 := by
    have hnat : (12179073 : ℕ)^4417*10000000000000^3393 ≤ 1189535895249^3393*62500000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12179073 62500000 1189535895249 10000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2624047103/5000000000 : ℝ)^4417 ≤ (4320148968293/10000000000000 : ℝ)^3393 := by
    have hnat : (2624047103 : ℕ)^4417*10000000000000^3393 ≤ 4320148968293^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2624047103 5000000000 4320148968293 10000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351543527/2500000000 : ℝ)^4417 ≤ (44903151347377/100000000000000 : ℝ)^3393 := by
    have hnat : (1351543527 : ℕ)^4417*100000000000000^3393 ≤ 44903151347377^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351543527 2500000000 44903151347377 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12179073/62500000 : ℝ), (2624047103/5000000000 : ℝ), (1351543527/2500000000 : ℝ)] ![(1189535895249/10000000000000 : ℝ), (4320148968293/10000000000000 : ℝ), (44903151347377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12179073/62500000 : ℝ)|^4417 ≤ (1189535895249/10000000000000 : ℝ)^3393
        have hw : |(-12179073/62500000 : ℝ)|=(12179073/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2624047103/5000000000 : ℝ)|^4417 ≤ (4320148968293/10000000000000 : ℝ)^3393
        have hw : |(2624047103/5000000000 : ℝ)|=(2624047103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351543527/2500000000 : ℝ)|^4417 ≤ (44903151347377/100000000000000 : ℝ)^3393
        have hw : |(1351543527/2500000000 : ℝ)|=(1351543527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s8_5 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2148723467/5000000000 : ℝ)*x 0 + (2236651921/5000000000 : ℝ)*x 1 + (4127809491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148723467/5000000000 : ℝ)^4417 ≤ (16652684829429/50000000000000 : ℝ)^3393 := by
    have hnat : (2148723467 : ℕ)^4417*50000000000000^3393 ≤ 16652684829429^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148723467 5000000000 16652684829429 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2236651921/5000000000 : ℝ)^4417 ≤ (35090439718273/100000000000000 : ℝ)^3393 := by
    have hnat : (2236651921 : ℕ)^4417*100000000000000^3393 ≤ 35090439718273^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236651921 5000000000 35090439718273 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4127809491/10000000000 : ℝ)^4417 ≤ (15802095300967/50000000000000 : ℝ)^3393 := by
    have hnat : (4127809491 : ℕ)^4417*50000000000000^3393 ≤ 15802095300967^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127809491 10000000000 15802095300967 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148723467/5000000000 : ℝ), (2236651921/5000000000 : ℝ), (4127809491/10000000000 : ℝ)] ![(16652684829429/50000000000000 : ℝ), (35090439718273/100000000000000 : ℝ), (15802095300967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148723467/5000000000 : ℝ)|^4417 ≤ (16652684829429/50000000000000 : ℝ)^3393
        have hw : |(2148723467/5000000000 : ℝ)|=(2148723467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2236651921/5000000000 : ℝ)|^4417 ≤ (35090439718273/100000000000000 : ℝ)^3393
        have hw : |(2236651921/5000000000 : ℝ)|=(2236651921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4127809491/10000000000 : ℝ)|^4417 ≤ (15802095300967/50000000000000 : ℝ)^3393
        have hw : |(4127809491/10000000000 : ℝ)|=(4127809491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1457_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11397/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1477/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2849/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2849/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2849/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2849/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2849/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2849/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2849/25000 : ℝ) ^ (69/16 : ℝ) ≤ (1711098047033687/20000000000000000000 : ℝ) := by
    have hpowers : (2849/25000 : ℝ)^69 ≤ (1711098047033687/20000000000000000000 : ℝ)^16 := by
      have hnat : (2849 : ℕ)^69*20000000000000000000^16 ≤ 1711098047033687^16*25000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2849 25000 1711098047033687 20000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2849/25000 : ℝ)) (X := (1711098047033687/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hpowhi : (1477/10000 : ℝ) ^ (69/16 : ℝ) ≤ (26179020068418349/100000000000000000000 : ℝ) := by
    have hpowers : (1477/10000 : ℝ)^69 ≤ (26179020068418349/100000000000000000000 : ℝ)^16 := by
      have hnat : (1477 : ℕ)^69*100000000000000000000^16 ≤ 26179020068418349^16*10000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1477 10000 26179020068418349 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1477/10000 : ℝ)) (X := (26179020068418349/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001711098047033687/10000000000000000000 : ℝ) ≤ (5000198375143387/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (10001711098047033687/10000000000000000000 : ℝ)^16 ≤ (5000198375143387/5000000000000000 : ℝ)^69 := by
      have hnat : (10001711098047033687 : ℕ)^16*5000000000000000^69 ≤ 5000198375143387^69*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001711098047033687 10000000000000000000 5000198375143387 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000198375143387/5000000000000000 : ℝ)) (X := (10001711098047033687/10000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126085453446987087/3125000000000000000 : ℝ) ≤ (78131291644501/78125000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (3126085453446987087/3125000000000000000 : ℝ)^16 ≤ (78131291644501/78125000000000 : ℝ)^69 := by
      have hnat : (3126085453446987087 : ℕ)^16*78125000000000^69 ≤ 78131291644501^69*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126085453446987087 3125000000000000000 78131291644501 78125000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78131291644501/78125000000000 : ℝ)) (X := (3126085453446987087/3125000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026179020068418349/50000000000000000000 : ℝ) ≤ (5000606955352741/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (50026179020068418349/50000000000000000000 : ℝ)^16 ≤ (5000606955352741/5000000000000000 : ℝ)^69 := by
      have hnat : (50026179020068418349 : ℕ)^16*5000000000000000^69 ≤ 5000606955352741^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026179020068418349 50000000000000000000 5000606955352741 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000606955352741/5000000000000000 : ℝ)) (X := (50026179020068418349/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1711098047033687/20000000000000000000 : ℝ) ≤ ((1204715224119142111/1205000000000000000 : ℝ)+2*(204290104677/168700000000000 : ℝ)*(2849/25000 : ℝ))^(69/16 : ℝ) := by
    rw [show (1204715224119142111/1205000000000000000 : ℝ)+2*(204290104677/168700000000000 : ℝ)*(2849/25000 : ℝ)=(5000198375143387/5000000000000000 : ℝ) by norm_num, show 1+2*(1711098047033687/20000000000000000000 : ℝ)=(10001711098047033687/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26179020068418349/100000000000000000000 : ℝ)+(1711098047033687/20000000000000000000 : ℝ) ≤ ((1204715224119142111/1205000000000000000 : ℝ)+(204290104677/168700000000000 : ℝ)*((1477/10000 : ℝ)+(2849/25000 : ℝ)))^(69/16 : ℝ) := by
    rw [show (1204715224119142111/1205000000000000000 : ℝ)+(204290104677/168700000000000 : ℝ)*((1477/10000 : ℝ)+(2849/25000 : ℝ))=(78131291644501/78125000000000 : ℝ) by norm_num, show 1+(26179020068418349/100000000000000000000 : ℝ)+(1711098047033687/20000000000000000000 : ℝ)=(3126085453446987087/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26179020068418349/100000000000000000000 : ℝ) ≤ ((1204715224119142111/1205000000000000000 : ℝ)+2*(204290104677/168700000000000 : ℝ)*(1477/10000 : ℝ))^(69/16 : ℝ) := by
    rw [show (1204715224119142111/1205000000000000000 : ℝ)+2*(204290104677/168700000000000 : ℝ)*(1477/10000 : ℝ)=(5000606955352741/5000000000000000 : ℝ) by norm_num, show 1+2*(26179020068418349/100000000000000000000 : ℝ)=(50026179020068418349/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1204715224119142111/1205000000000000000 : ℝ)*(X 1 0+X 2 0)+(204290104677/168700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (2849/25000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (1204715224119142111/1205000000000000000 : ℝ)) (alpha := (204290104677/168700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1204715224119142111/1205000000000000000 : ℝ)*(X 0 1+X 2 1)+(204290104677/168700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (2849/25000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (1204715224119142111/1205000000000000000 : ℝ)) (alpha := (204290104677/168700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1204715224119142111/1205000000000000000 : ℝ)*(X 0 2+X 1 2)+(204290104677/168700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (2849/25000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (1204715224119142111/1205000000000000000 : ℝ)) (alpha := (204290104677/168700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-487160191/2500000000 : ℝ)*X 0 0+(1351688307/2500000000 : ℝ)*X 0 1+(20498117/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346716481/10000000000 : ℝ)*X 1 0+(-2029690887/10000000000 : ℝ)*X 1 1+(20498117/39062500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346716481/10000000000 : ℝ)*X 2 0+(20498117/39062500 : ℝ)*X 2 1+(-2029690887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((107435567/250000000 : ℝ)*X 0 0+(2063272661/5000000000 : ℝ)*X 0 1+(894912313/2000000000 : ℝ)*X 0 2+(107435567/250000000 : ℝ)*X 1 0+(2063272661/5000000000 : ℝ)*X 1 1+(894912313/2000000000 : ℝ)*X 1 2+(107435567/250000000 : ℝ)*X 2 0+(2063272661/5000000000 : ℝ)*X 2 1+(894912313/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-12179073/62500000 : ℝ)*X 0 0+(2624047103/5000000000 : ℝ)*X 0 1+(1351543527/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2148723467/5000000000 : ℝ)*X 0 0+(2236651921/5000000000 : ℝ)*X 0 1+(4127809491/10000000000 : ℝ)*X 0 2+(2148723467/5000000000 : ℝ)*X 1 0+(2236651921/5000000000 : ℝ)*X 1 1+(4127809491/10000000000 : ℝ)*X 1 2+(2148723467/5000000000 : ℝ)*X 2 0+(2236651921/5000000000 : ℝ)*X 2 1+(4127809491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (475695032793590177303694579/210875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (409975353/100000000000000 : ℝ)*(base19) + (95339647/25000000000000 : ℝ)*(base23) + (15300573/100000000000000 : ℝ)*(lower2) + (14156603/25000000000000 : ℝ)*(upper3) + (17950229/50000000000000 : ℝ)*(upper5) + (4576735326147391/100000000000000 : ℝ)*(major0) + (4576735326147391/100000000000000 : ℝ)*(major1) + (4576735326147391/100000000000000 : ℝ)*(major2) + (6280024586858667/100000000000000 : ℝ)*(sp0) + (6280032888403947/100000000000000 : ℝ)*(sp1) + (785004114627589/12500000000000 : ℝ)*(sp2) + (1795895599699/62500000000 : ℝ)*(sp3) + (8711520633/100000000000000 : ℝ)*(sp4) + (1079800809/25000000000000 : ℝ)*(sp5) + (718359319680409/25000000000000 : ℝ)*(f.failure) + (62800332983793/1000000000000 : ℝ)*(f.sum) + (8741128982447/8435000000000000000000000000 : ℝ)*base65 + (592203121679473193/843500000000000000000000000000000 : ℝ)*base68 + (8695969935567526807/843500000000000000000000000000000 : ℝ)*base69 + (7756250450713026807/843500000000000000000000000000000 : ℝ)*base71 + (20236233136899/4217500000000000000000000000 : ℝ)*base74 + (1350353394241526807/843500000000000000000000000000000 : ℝ)*base75 + (8550486706235526807/843500000000000000000000000000000 : ℝ)*base77 + (8773141656095526807/843500000000000000000000000000000 : ℝ)*base79 + (29190913647713/8435000000000000000000000000 : ℝ)*base82 + (1104433/250000000000000000000 : ℝ)*base89 + (1104433/250000000000000000000 : ℝ)*base91 + (1104433/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1457_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2849/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1457_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1457_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1457_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1457_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1457_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11397/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1457_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

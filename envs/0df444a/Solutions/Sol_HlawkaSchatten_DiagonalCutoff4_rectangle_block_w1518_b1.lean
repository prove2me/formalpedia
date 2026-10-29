-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1518_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:56:34.007653+00:00
-- url     : https://prove2.me/submissions/a44f0cdf-0e4e-4eb7-ac9f-24674e72a30b

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
theorem support_rectangle_w1518_s3_0 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1858725543/10000000000 : ℝ)*x 0 + (339719441/625000000 : ℝ)*x 1 + (2607591827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1858725543/10000000000 : ℝ)^4533 ≤ (11375144244313/100000000000000 : ℝ)^3509 := by
    have hnat : (1858725543 : ℕ)^4533*100000000000000^3509 ≤ 11375144244313^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858725543 10000000000 11375144244313 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339719441/625000000 : ℝ)^4533 ≤ (5687062119031/12500000000000 : ℝ)^3509 := by
    have hnat : (339719441 : ℕ)^4533*12500000000000^3509 ≤ 5687062119031^3509*625000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339719441 625000000 5687062119031 12500000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607591827/5000000000 : ℝ)^4533 ≤ (10782089698141/25000000000000 : ℝ)^3509 := by
    have hnat : (2607591827 : ℕ)^4533*25000000000000^3509 ≤ 10782089698141^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607591827 5000000000 10782089698141 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1858725543/10000000000 : ℝ), (339719441/625000000 : ℝ), (2607591827/5000000000 : ℝ)] ![(11375144244313/100000000000000 : ℝ), (5687062119031/12500000000000 : ℝ), (10782089698141/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1858725543/10000000000 : ℝ)|^4533 ≤ (11375144244313/100000000000000 : ℝ)^3509
        have hw : |(-1858725543/10000000000 : ℝ)|=(1858725543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339719441/625000000 : ℝ)|^4533 ≤ (5687062119031/12500000000000 : ℝ)^3509
        have hw : |(339719441/625000000 : ℝ)|=(339719441/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607591827/5000000000 : ℝ)|^4533 ≤ (10782089698141/25000000000000 : ℝ)^3509
        have hw : |(2607591827/5000000000 : ℝ)|=(2607591827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s3_1 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352055949/10000000000 : ℝ)*x 0 + (-1971624831/10000000000 : ℝ)*x 1 + (5215183917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352055949/10000000000 : ℝ)^4533 ≤ (11149034720567/25000000000000 : ℝ)^3509 := by
    have hnat : (5352055949 : ℕ)^4533*25000000000000^3509 ≤ 11149034720567^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352055949 10000000000 11149034720567 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1971624831/10000000000 : ℝ)^4533 ≤ (12275499494259/100000000000000 : ℝ)^3509 := by
    have hnat : (1971624831 : ℕ)^4533*100000000000000^3509 ≤ 12275499494259^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971624831 10000000000 12275499494259 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215183917/10000000000 : ℝ)^4533 ≤ (43128361602209/100000000000000 : ℝ)^3509 := by
    have hnat : (5215183917 : ℕ)^4533*100000000000000^3509 ≤ 43128361602209^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215183917 10000000000 43128361602209 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352055949/10000000000 : ℝ), (-1971624831/10000000000 : ℝ), (5215183917/10000000000 : ℝ)] ![(11149034720567/25000000000000 : ℝ), (12275499494259/100000000000000 : ℝ), (43128361602209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352055949/10000000000 : ℝ)|^4533 ≤ (11149034720567/25000000000000 : ℝ)^3509
        have hw : |(5352055949/10000000000 : ℝ)|=(5352055949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1971624831/10000000000 : ℝ)|^4533 ≤ (12275499494259/100000000000000 : ℝ)^3509
        have hw : |(-1971624831/10000000000 : ℝ)|=(1971624831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215183917/10000000000 : ℝ)|^4533 ≤ (43128361602209/100000000000000 : ℝ)^3509
        have hw : |(5215183917/10000000000 : ℝ)|=(5215183917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s3_2 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338014007/2500000000 : ℝ)*x 0 + (2607591913/5000000000 : ℝ)*x 1 + (-1971624847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338014007/2500000000 : ℝ)^4533 ≤ (8919227946527/20000000000000 : ℝ)^3509 := by
    have hnat : (1338014007 : ℕ)^4533*20000000000000^3509 ≤ 8919227946527^3509*2500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338014007 2500000000 8919227946527 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607591913/5000000000 : ℝ)^4533 ≤ (862567212601/2000000000000 : ℝ)^3509 := by
    have hnat : (2607591913 : ℕ)^4533*2000000000000^3509 ≤ 862567212601^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607591913 5000000000 862567212601 2000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1971624847/10000000000 : ℝ)^4533 ≤ (6137749811473/50000000000000 : ℝ)^3509 := by
    have hnat : (1971624847 : ℕ)^4533*50000000000000^3509 ≤ 6137749811473^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971624847 10000000000 6137749811473 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338014007/2500000000 : ℝ), (2607591913/5000000000 : ℝ), (-1971624847/10000000000 : ℝ)] ![(8919227946527/20000000000000 : ℝ), (862567212601/2000000000000 : ℝ), (6137749811473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338014007/2500000000 : ℝ)|^4533 ≤ (8919227946527/20000000000000 : ℝ)^3509
        have hw : |(1338014007/2500000000 : ℝ)|=(1338014007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607591913/5000000000 : ℝ)|^4533 ≤ (862567212601/2000000000000 : ℝ)^3509
        have hw : |(2607591913/5000000000 : ℝ)|=(2607591913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1971624847/10000000000 : ℝ)|^4533 ≤ (6137749811473/50000000000000 : ℝ)^3509
        have hw : |(-1971624847/10000000000 : ℝ)|=(1971624847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s3_3 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2133347931/5000000000 : ℝ)*x 0 + (804412581/2000000000 : ℝ)*x 1 + (2261893701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133347931/5000000000 : ℝ)^4533 ≤ (1663851893823/5000000000000 : ℝ)^3509 := by
    have hnat : (2133347931 : ℕ)^4533*5000000000000^3509 ≤ 1663851893823^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133347931 5000000000 1663851893823 5000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (804412581/2000000000 : ℝ)^4533 ≤ (3083320827543/10000000000000 : ℝ)^3509 := by
    have hnat : (804412581 : ℕ)^4533*10000000000000^3509 ≤ 3083320827543^3509*2000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804412581 2000000000 3083320827543 10000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2261893701/5000000000 : ℝ)^4533 ≤ (8972438459203/25000000000000 : ℝ)^3509 := by
    have hnat : (2261893701 : ℕ)^4533*25000000000000^3509 ≤ 8972438459203^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2261893701 5000000000 8972438459203 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133347931/5000000000 : ℝ), (804412581/2000000000 : ℝ), (2261893701/5000000000 : ℝ)] ![(1663851893823/5000000000000 : ℝ), (3083320827543/10000000000000 : ℝ), (8972438459203/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133347931/5000000000 : ℝ)|^4533 ≤ (1663851893823/5000000000000 : ℝ)^3509
        have hw : |(2133347931/5000000000 : ℝ)|=(2133347931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(804412581/2000000000 : ℝ)|^4533 ≤ (3083320827543/10000000000000 : ℝ)^3509
        have hw : |(804412581/2000000000 : ℝ)|=(804412581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2261893701/5000000000 : ℝ)|^4533 ≤ (8972438459203/25000000000000 : ℝ)^3509
        have hw : |(2261893701/5000000000 : ℝ)|=(2261893701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s3_4 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-929378249/5000000000 : ℝ)*x 0 + (2608174897/5000000000 : ℝ)*x 1 + (1086867241/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (929378249/5000000000 : ℝ)^4533 ≤ (11375388967917/100000000000000 : ℝ)^3509 := by
    have hnat : (929378249 : ℕ)^4533*100000000000000^3509 ≤ 11375388967917^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929378249 5000000000 11375388967917 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608174897/5000000000 : ℝ)^4533 ≤ (5392602142853/12500000000000 : ℝ)^3509 := by
    have hnat : (2608174897 : ℕ)^4533*12500000000000^3509 ≤ 5392602142853^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608174897 5000000000 5392602142853 12500000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086867241/2000000000 : ℝ)^4533 ≤ (35534213963/78125000000 : ℝ)^3509 := by
    have hnat : (1086867241 : ℕ)^4533*78125000000^3509 ≤ 35534213963^3509*2000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086867241 2000000000 35534213963 78125000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-929378249/5000000000 : ℝ), (2608174897/5000000000 : ℝ), (1086867241/2000000000 : ℝ)] ![(11375388967917/100000000000000 : ℝ), (5392602142853/12500000000000 : ℝ), (35534213963/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-929378249/5000000000 : ℝ)|^4533 ≤ (11375388967917/100000000000000 : ℝ)^3509
        have hw : |(-929378249/5000000000 : ℝ)|=(929378249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608174897/5000000000 : ℝ)|^4533 ≤ (5392602142853/12500000000000 : ℝ)^3509
        have hw : |(2608174897/5000000000 : ℝ)|=(2608174897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086867241/2000000000 : ℝ)|^4533 ≤ (35534213963/78125000000 : ℝ)^3509
        have hw : |(1086867241/2000000000 : ℝ)|=(1086867241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s3_5 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647082281/5000000000 : ℝ)*x 0 + (-109529493/625000000 : ℝ)*x 1 + (2717168129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647082281/5000000000 : ℝ)^4533 ≤ (10993493610351/25000000000000 : ℝ)^3509 := by
    have hnat : (2647082281 : ℕ)^4533*25000000000000^3509 ≤ 10993493610351^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647082281 5000000000 10993493610351 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109529493/625000000 : ℝ)^4533 ≤ (2108446218953/20000000000000 : ℝ)^3509 := by
    have hnat : (109529493 : ℕ)^4533*20000000000000^3509 ≤ 2108446218953^3509*625000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109529493 625000000 2108446218953 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717168129/5000000000 : ℝ)^4533 ≤ (9096758889137/20000000000000 : ℝ)^3509 := by
    have hnat : (2717168129 : ℕ)^4533*20000000000000^3509 ≤ 9096758889137^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717168129 5000000000 9096758889137 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647082281/5000000000 : ℝ), (-109529493/625000000 : ℝ), (2717168129/5000000000 : ℝ)] ![(10993493610351/25000000000000 : ℝ), (2108446218953/20000000000000 : ℝ), (9096758889137/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647082281/5000000000 : ℝ)|^4533 ≤ (10993493610351/25000000000000 : ℝ)^3509
        have hw : |(2647082281/5000000000 : ℝ)|=(2647082281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109529493/625000000 : ℝ)|^4533 ≤ (2108446218953/20000000000000 : ℝ)^3509
        have hw : |(-109529493/625000000 : ℝ)|=(109529493/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717168129/5000000000 : ℝ)|^4533 ≤ (9096758889137/20000000000000 : ℝ)^3509
        have hw : |(2717168129/5000000000 : ℝ)|=(2717168129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s3_6 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294164573/10000000000 : ℝ)*x 0 + (1358584031/2500000000 : ℝ)*x 1 + (-87623603/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294164573/10000000000 : ℝ)^4533 ≤ (8794794911887/20000000000000 : ℝ)^3509 := by
    have hnat : (5294164573 : ℕ)^4533*20000000000000^3509 ≤ 8794794911887^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294164573 10000000000 8794794911887 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358584031/2500000000 : ℝ)^4533 ≤ (9096758599371/20000000000000 : ℝ)^3509 := by
    have hnat : (1358584031 : ℕ)^4533*20000000000000^3509 ≤ 9096758599371^3509*2500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358584031 2500000000 9096758599371 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (87623603/500000000 : ℝ)^4533 ≤ (5271116215699/50000000000000 : ℝ)^3509 := by
    have hnat : (87623603 : ℕ)^4533*50000000000000^3509 ≤ 5271116215699^3509*500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87623603 500000000 5271116215699 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294164573/10000000000 : ℝ), (1358584031/2500000000 : ℝ), (-87623603/500000000 : ℝ)] ![(8794794911887/20000000000000 : ℝ), (9096758599371/20000000000000 : ℝ), (5271116215699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294164573/10000000000 : ℝ)|^4533 ≤ (8794794911887/20000000000000 : ℝ)^3509
        have hw : |(5294164573/10000000000 : ℝ)|=(5294164573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358584031/2500000000 : ℝ)|^4533 ≤ (9096758599371/20000000000000 : ℝ)^3509
        have hw : |(1358584031/2500000000 : ℝ)|=(1358584031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-87623603/500000000 : ℝ)|^4533 ≤ (5271116215699/50000000000000 : ℝ)^3509
        have hw : |(-87623603/500000000 : ℝ)|=(87623603/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s3_7 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (853353373/2000000000 : ℝ)*x 0 + (904226403/2000000000 : ℝ)*x 1 + (4024738233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853353373/2000000000 : ℝ)^4533 ≤ (33277753250339/100000000000000 : ℝ)^3509 := by
    have hnat : (853353373 : ℕ)^4533*100000000000000^3509 ≤ 33277753250339^3509*2000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853353373 2000000000 33277753250339 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904226403/2000000000 : ℝ)^4533 ≤ (448281772331/1250000000000 : ℝ)^3509 := by
    have hnat : (904226403 : ℕ)^4533*1250000000000^3509 ≤ 448281772331^3509*2000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904226403 2000000000 448281772331 1250000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4024738233/10000000000 : ℝ)^4533 ≤ (7714926237703/25000000000000 : ℝ)^3509 := by
    have hnat : (4024738233 : ℕ)^4533*25000000000000^3509 ≤ 7714926237703^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4024738233 10000000000 7714926237703 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(853353373/2000000000 : ℝ), (904226403/2000000000 : ℝ), (4024738233/10000000000 : ℝ)] ![(33277753250339/100000000000000 : ℝ), (448281772331/1250000000000 : ℝ), (7714926237703/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(853353373/2000000000 : ℝ)|^4533 ≤ (33277753250339/100000000000000 : ℝ)^3509
        have hw : |(853353373/2000000000 : ℝ)|=(853353373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(904226403/2000000000 : ℝ)|^4533 ≤ (448281772331/1250000000000 : ℝ)^3509
        have hw : |(904226403/2000000000 : ℝ)|=(904226403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4024738233/10000000000 : ℝ)|^4533 ≤ (7714926237703/25000000000000 : ℝ)^3509
        have hw : |(4024738233/10000000000 : ℝ)|=(4024738233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1518_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7987/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (68/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7773/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7987/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10487/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7987/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10487/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7987/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10487/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7987/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10487/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7987/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10487/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7987/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10487/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10487/100000 : ℝ) ^ (4531/1024 : ℝ) ≤ (72509208754931/1562500000000000000 : ℝ) := by
    have hpowers : (10487/100000 : ℝ)^4531 ≤ (72509208754931/1562500000000000000 : ℝ)^1024 := by
      have hnat : (10487 : ℕ)^4531*1562500000000000000^1024 ≤ 72509208754931^1024*100000^4531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10487 100000 72509208754931 1562500000000000000 4531 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10487/100000 : ℝ)) (X := (72509208754931/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7987/50000 : ℝ) ^ (4531/1024 : ℝ) ≤ (29871781071092197/100000000000000000000 : ℝ) := by
    have hpowers : (7987/50000 : ℝ)^4531 ≤ (29871781071092197/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7987 : ℕ)^4531*100000000000000000000^1024 ≤ 29871781071092197^1024*50000^4531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7987 50000 29871781071092197 100000000000000000000 4531 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7987/50000 : ℝ)) (X := (29871781071092197/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (781322509208754931/781250000000000000 : ℝ) ≤ (10000209745876507/10000000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (781322509208754931/781250000000000000 : ℝ)^1024 ≤ (10000209745876507/10000000000000000 : ℝ)^4531 := by
      have hnat : (781322509208754931 : ℕ)^1024*10000000000000000^4531 ≤ 10000209745876507^4531*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781322509208754931 781250000000000000 10000209745876507 10000000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000209745876507/10000000000000000 : ℝ)) (X := (781322509208754931/781250000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034512370431407781/100000000000000000000 : ℝ) ≤ (10000779870846959/10000000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (100034512370431407781/100000000000000000000 : ℝ)^1024 ≤ (10000779870846959/10000000000000000 : ℝ)^4531 := by
      have hnat : (100034512370431407781 : ℕ)^1024*10000000000000000^4531 ≤ 10000779870846959^4531*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034512370431407781 100000000000000000000 10000779870846959 10000000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000779870846959/10000000000000000 : ℝ)) (X := (100034512370431407781/100000000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029871781071092197/50000000000000000000 : ℝ) ≤ (10001349995817411/10000000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (50029871781071092197/50000000000000000000 : ℝ)^1024 ≤ (10001349995817411/10000000000000000 : ℝ)^4531 := by
      have hnat : (50029871781071092197 : ℕ)^1024*10000000000000000^4531 ≤ 10001349995817411^4531*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029871781071092197 50000000000000000000 10001349995817411 10000000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001349995817411/10000000000000000 : ℝ)) (X := (50029871781071092197/50000000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(72509208754931/1562500000000000000 : ℝ) ≤ ((54859193074494133661/54870000000000000000 : ℝ)+2*(142531242613/137175000000000 : ℝ)*(10487/100000 : ℝ))^(4531/1024 : ℝ) := by
    rw [show (54859193074494133661/54870000000000000000 : ℝ)+2*(142531242613/137175000000000 : ℝ)*(10487/100000 : ℝ)=(10000209745876507/10000000000000000 : ℝ) by norm_num, show 1+2*(72509208754931/1562500000000000000 : ℝ)=(781322509208754931/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29871781071092197/100000000000000000000 : ℝ)+(72509208754931/1562500000000000000 : ℝ) ≤ ((54859193074494133661/54870000000000000000 : ℝ)+(142531242613/137175000000000 : ℝ)*((7987/50000 : ℝ)+(10487/100000 : ℝ)))^(4531/1024 : ℝ) := by
    rw [show (54859193074494133661/54870000000000000000 : ℝ)+(142531242613/137175000000000 : ℝ)*((7987/50000 : ℝ)+(10487/100000 : ℝ))=(10000779870846959/10000000000000000 : ℝ) by norm_num, show 1+(29871781071092197/100000000000000000000 : ℝ)+(72509208754931/1562500000000000000 : ℝ)=(100034512370431407781/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29871781071092197/100000000000000000000 : ℝ) ≤ ((54859193074494133661/54870000000000000000 : ℝ)+2*(142531242613/137175000000000 : ℝ)*(7987/50000 : ℝ))^(4531/1024 : ℝ) := by
    rw [show (54859193074494133661/54870000000000000000 : ℝ)+2*(142531242613/137175000000000 : ℝ)*(7987/50000 : ℝ)=(10001349995817411/10000000000000000 : ℝ) by norm_num, show 1+2*(29871781071092197/100000000000000000000 : ℝ)=(50029871781071092197/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54859193074494133661/54870000000000000000 : ℝ)*(X 1 0+X 2 0)+(142531242613/137175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (10487/100000 : ℝ)) (hi := (7987/50000 : ℝ)) (c := (54859193074494133661/54870000000000000000 : ℝ)) (alpha := (142531242613/137175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54859193074494133661/54870000000000000000 : ℝ)*(X 0 1+X 2 1)+(142531242613/137175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (10487/100000 : ℝ)) (hi := (7987/50000 : ℝ)) (c := (54859193074494133661/54870000000000000000 : ℝ)) (alpha := (142531242613/137175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54859193074494133661/54870000000000000000 : ℝ)*(X 0 2+X 1 2)+(142531242613/137175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (10487/100000 : ℝ)) (hi := (7987/50000 : ℝ)) (c := (54859193074494133661/54870000000000000000 : ℝ)) (alpha := (142531242613/137175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1858725543/10000000000 : ℝ)*X 0 0+(339719441/625000000 : ℝ)*X 0 1+(2607591827/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352055949/10000000000 : ℝ)*X 1 0+(-1971624831/10000000000 : ℝ)*X 1 1+(5215183917/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338014007/2500000000 : ℝ)*X 2 0+(2607591913/5000000000 : ℝ)*X 2 1+(-1971624847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2133347931/5000000000 : ℝ)*X 0 0+(804412581/2000000000 : ℝ)*X 0 1+(2261893701/5000000000 : ℝ)*X 0 2+(2133347931/5000000000 : ℝ)*X 1 0+(804412581/2000000000 : ℝ)*X 1 1+(2261893701/5000000000 : ℝ)*X 1 2+(2133347931/5000000000 : ℝ)*X 2 0+(804412581/2000000000 : ℝ)*X 2 1+(2261893701/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-929378249/5000000000 : ℝ)*X 0 0+(2608174897/5000000000 : ℝ)*X 0 1+(1086867241/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647082281/5000000000 : ℝ)*X 1 0+(-109529493/625000000 : ℝ)*X 1 1+(2717168129/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294164573/10000000000 : ℝ)*X 2 0+(1358584031/2500000000 : ℝ)*X 2 1+(-87623603/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((853353373/2000000000 : ℝ)*X 0 0+(904226403/2000000000 : ℝ)*X 0 1+(4024738233/10000000000 : ℝ)*X 0 2+(853353373/2000000000 : ℝ)*X 1 0+(904226403/2000000000 : ℝ)*X 1 1+(4024738233/10000000000 : ℝ)*X 1 2+(853353373/2000000000 : ℝ)*X 2 0+(904226403/2000000000 : ℝ)*X 2 1+(4024738233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6714268090889655234979499459/914500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (538133851/50000000000000 : ℝ)*(base19) + (21567699/2000000000000 : ℝ)*(base23) + (34722857/100000000000000 : ℝ)*(lower2) + (223216403/100000000000000 : ℝ)*(upper3) + (17145553/10000000000000 : ℝ)*(upper5) + (3265940917165919/100000000000000 : ℝ)*(major0) + (3265940917165919/100000000000000 : ℝ)*(major1) + (3265940917165919/100000000000000 : ℝ)*(major2) + (907743834881499/20000000000000 : ℝ)*(sp0) + (4538736857980997/100000000000000 : ℝ)*(sp1) + (1134684213965937/25000000000000 : ℝ)*(sp2) + (7785680431433/390625000000 : ℝ)*(sp3) + (4689960301/25000000000000 : ℝ)*(sp4) + (4732451311/50000000000000 : ℝ)*(sp7) + (199314365534947/10000000000000 : ℝ)*(f.failure) + (4538737934248699/100000000000000 : ℝ)*(f.sum) + (28561970021227/27435000000000000000000000000 : ℝ)*base66 + (12901127335367766847/1829000000000000000000000000000000 : ℝ)*base68 + (725913123441766847/1829000000000000000000000000000000 : ℝ)*base70 + (1261970667135233153/1829000000000000000000000000000000 : ℝ)*base71 + (18186207590017/27435000000000000000000000000 : ℝ)*base74 + (1894548464912766847/1829000000000000000000000000000000 : ℝ)*base76 + (10639829438603766847/1829000000000000000000000000000000 : ℝ)*base78 + (22673904559624233153/1829000000000000000000000000000000 : ℝ)*base79 + (1473088606339/13717500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1927277/500000000000000000000 : ℝ)*base89 + (1927277/500000000000000000000 : ℝ)*base91 + (1927277/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14978430720968480406237639/11431250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29628853/4000000000000 : ℝ)*(base19) + (237424921/25000000000000 : ℝ)*(base23) + (87569357/100000000000000 : ℝ)*(upper3) + (12572291/12500000000000 : ℝ)*(lower4) + (19930591/100000000000000 : ℝ)*(upper5) + (41262299812049/1250000000000 : ℝ)*(major0) + (41262299812049/1250000000000 : ℝ)*(major1) + (41262299812049/1250000000000 : ℝ)*(major2) + (2509053873/20000000000000 : ℝ)*(sp1) + (6705512767/50000000000000 : ℝ)*(sp2) + (917487626268527/20000000000000 : ℝ)*(sp4) + (917484969070389/20000000000000 : ℝ)*(sp5) + (4587423770617417/100000000000000 : ℝ)*(sp6) + (40290595898167/2000000000000 : ℝ)*(sp7) + (40290595898167/2000000000000 : ℝ)*(f.failure) + (917487626268527/20000000000000 : ℝ)*(f.sum) + (765485743109/685875000000000000000000000 : ℝ)*base66 + (86522870256860463/22862500000000000000000000000000 : ℝ)*base67 + (23149760471452037/22862500000000000000000000000000 : ℝ)*base70 + (17606804502702037/22862500000000000000000000000000 : ℝ)*base72 + (2055112234057/5487000000000000000000000000 : ℝ)*base74 + (31159551805297963/22862500000000000000000000000000 : ℝ)*base75 + (107509274296727037/22862500000000000000000000000000 : ℝ)*base78 + (26665197168864537/22862500000000000000000000000000 : ℝ)*base80 + (1386556157851/342937500000000000000000000 : ℝ)*base82 + (326297/100000000000000000000 : ℝ)*base89 + (326297/100000000000000000000 : ℝ)*base91 + (326297/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1518_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7987/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7773/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1518_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1518_s4_0 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-74365447/400000000 : ℝ)*x 0 + (5432815071/10000000000 : ℝ)*x 1 + (260880407/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (74365447/400000000 : ℝ)^4533 ≤ (4444683871/39062500000 : ℝ)^3509 := by
    have hnat : (74365447 : ℕ)^4533*39062500000^3509 ≤ 4444683871^3509*400000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74365447 400000000 4444683871 39062500000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432815071/10000000000 : ℝ)^4533 ≤ (454673477977/1000000000000 : ℝ)^3509 := by
    have hnat : (5432815071 : ℕ)^4533*1000000000000^3509 ≤ 454673477977^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432815071 10000000000 454673477977 1000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260880407/500000000 : ℝ)^4533 ≤ (5394282684899/12500000000000 : ℝ)^3509 := by
    have hnat : (260880407 : ℕ)^4533*12500000000000^3509 ≤ 5394282684899^3509*500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260880407 500000000 5394282684899 12500000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-74365447/400000000 : ℝ), (5432815071/10000000000 : ℝ), (260880407/500000000 : ℝ)] ![(4444683871/39062500000 : ℝ), (454673477977/1000000000000 : ℝ), (5394282684899/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-74365447/400000000 : ℝ)|^4533 ≤ (4444683871/39062500000 : ℝ)^3509
        have hw : |(-74365447/400000000 : ℝ)|=(74365447/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432815071/10000000000 : ℝ)|^4533 ≤ (454673477977/1000000000000 : ℝ)^3509
        have hw : |(5432815071/10000000000 : ℝ)|=(5432815071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260880407/500000000 : ℝ)|^4533 ≤ (5394282684899/12500000000000 : ℝ)^3509
        have hw : |(260880407/500000000 : ℝ)|=(260880407/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s4_1 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070269787/2000000000 : ℝ)*x 0 + (-196934989/1000000000 : ℝ)*x 1 + (5217608571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070269787/2000000000 : ℝ)^4533 ≤ (44588528637809/100000000000000 : ℝ)^3509 := by
    have hnat : (1070269787 : ℕ)^4533*100000000000000^3509 ≤ 44588528637809^3509*2000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070269787 2000000000 44588528637809 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196934989/1000000000 : ℝ)^4533 ≤ (245144105197/2000000000000 : ℝ)^3509 := by
    have hnat : (196934989 : ℕ)^4533*2000000000000^3509 ≤ 245144105197^3509*1000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196934989 1000000000 245144105197 2000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217608571/10000000000 : ℝ)^4533 ≤ (8630853216843/20000000000000 : ℝ)^3509 := by
    have hnat : (5217608571 : ℕ)^4533*20000000000000^3509 ≤ 8630853216843^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217608571 10000000000 8630853216843 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070269787/2000000000 : ℝ), (-196934989/1000000000 : ℝ), (5217608571/10000000000 : ℝ)] ![(44588528637809/100000000000000 : ℝ), (245144105197/2000000000000 : ℝ), (8630853216843/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070269787/2000000000 : ℝ)|^4533 ≤ (44588528637809/100000000000000 : ℝ)^3509
        have hw : |(1070269787/2000000000 : ℝ)|=(1070269787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-196934989/1000000000 : ℝ)|^4533 ≤ (245144105197/2000000000000 : ℝ)^3509
        have hw : |(-196934989/1000000000 : ℝ)|=(196934989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217608571/10000000000 : ℝ)|^4533 ≤ (8630853216843/20000000000000 : ℝ)^3509
        have hw : |(5217608571/10000000000 : ℝ)|=(5217608571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s4_2 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351349249/10000000000 : ℝ)*x 0 + (5217608287/10000000000 : ℝ)*x 1 + (-246168731/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351349249/10000000000 : ℝ)^4533 ≤ (2786783251101/6250000000000 : ℝ)^3509 := by
    have hnat : (5351349249 : ℕ)^4533*6250000000000^3509 ≤ 2786783251101^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351349249 10000000000 2786783251101 6250000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217608287/10000000000 : ℝ)^4533 ≤ (21577131524907/50000000000000 : ℝ)^3509 := by
    have hnat : (5217608287 : ℕ)^4533*50000000000000^3509 ≤ 21577131524907^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217608287 10000000000 21577131524907 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (246168731/1250000000 : ℝ)^4533 ≤ (12257204922159/100000000000000 : ℝ)^3509 := by
    have hnat : (246168731 : ℕ)^4533*100000000000000^3509 ≤ 12257204922159^3509*1250000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246168731 1250000000 12257204922159 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351349249/10000000000 : ℝ), (5217608287/10000000000 : ℝ), (-246168731/1250000000 : ℝ)] ![(2786783251101/6250000000000 : ℝ), (21577131524907/50000000000000 : ℝ), (12257204922159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351349249/10000000000 : ℝ)|^4533 ≤ (2786783251101/6250000000000 : ℝ)^3509
        have hw : |(5351349249/10000000000 : ℝ)|=(5351349249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217608287/10000000000 : ℝ)|^4533 ≤ (21577131524907/50000000000000 : ℝ)^3509
        have hw : |(5217608287/10000000000 : ℝ)|=(5217608287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-246168731/1250000000 : ℝ)|^4533 ≤ (12257204922159/100000000000000 : ℝ)^3509
        have hw : |(-246168731/1250000000 : ℝ)|=(246168731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s4_3 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (426695193/1000000000 : ℝ)*x 0 + (1006966053/2500000000 : ℝ)*x 1 + (4517927711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426695193/1000000000 : ℝ)^4533 ≤ (33279617845163/100000000000000 : ℝ)^3509 := by
    have hnat : (426695193 : ℕ)^4533*100000000000000^3509 ≤ 33279617845163^3509*1000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426695193 1000000000 33279617845163 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006966053/2500000000 : ℝ)^4533 ≤ (6178134284757/20000000000000 : ℝ)^3509 := by
    have hnat : (1006966053 : ℕ)^4533*20000000000000^3509 ≤ 6178134284757^3509*2500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006966053 2500000000 6178134284757 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4517927711/10000000000 : ℝ)^4533 ≤ (8957427679437/25000000000000 : ℝ)^3509 := by
    have hnat : (4517927711 : ℕ)^4533*25000000000000^3509 ≤ 8957427679437^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517927711 10000000000 8957427679437 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(426695193/1000000000 : ℝ), (1006966053/2500000000 : ℝ), (4517927711/10000000000 : ℝ)] ![(33279617845163/100000000000000 : ℝ), (6178134284757/20000000000000 : ℝ), (8957427679437/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(426695193/1000000000 : ℝ)|^4533 ≤ (33279617845163/100000000000000 : ℝ)^3509
        have hw : |(426695193/1000000000 : ℝ)|=(426695193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1006966053/2500000000 : ℝ)|^4533 ≤ (6178134284757/20000000000000 : ℝ)^3509
        have hw : |(1006966053/2500000000 : ℝ)|=(1006966053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4517927711/10000000000 : ℝ)|^4533 ≤ (8957427679437/25000000000000 : ℝ)^3509
        have hw : |(4517927711/10000000000 : ℝ)|=(4517927711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s4_4 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-371833007/2000000000 : ℝ)*x 0 + (5218720817/10000000000 : ℝ)*x 1 + (1357923567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (371833007/2000000000 : ℝ)^4533 ≤ (11378618885413/100000000000000 : ℝ)^3509 := by
    have hnat : (371833007 : ℕ)^4533*100000000000000^3509 ≤ 11378618885413^3509*2000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371833007 2000000000 11378618885413 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218720817/10000000000 : ℝ)^4533 ≤ (5395768782103/12500000000000 : ℝ)^3509 := by
    have hnat : (5218720817 : ℕ)^4533*12500000000000^3509 ≤ 5395768782103^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218720817 10000000000 5395768782103 12500000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357923567/2500000000 : ℝ)^4533 ≤ (5681903856153/12500000000000 : ℝ)^3509 := by
    have hnat : (1357923567 : ℕ)^4533*12500000000000^3509 ≤ 5681903856153^3509*2500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357923567 2500000000 5681903856153 12500000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-371833007/2000000000 : ℝ), (5218720817/10000000000 : ℝ), (1357923567/2500000000 : ℝ)] ![(11378618885413/100000000000000 : ℝ), (5395768782103/12500000000000 : ℝ), (5681903856153/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-371833007/2000000000 : ℝ)|^4533 ≤ (11378618885413/100000000000000 : ℝ)^3509
        have hw : |(-371833007/2000000000 : ℝ)|=(371833007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218720817/10000000000 : ℝ)|^4533 ≤ (5395768782103/12500000000000 : ℝ)^3509
        have hw : |(5218720817/10000000000 : ℝ)|=(5218720817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357923567/2500000000 : ℝ)|^4533 ≤ (5681903856153/12500000000000 : ℝ)^3509
        have hw : |(1357923567/2500000000 : ℝ)|=(1357923567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s4_5 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294804267/10000000000 : ℝ)*x 0 + (-438815889/2500000000 : ℝ)*x 1 + (1357923567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294804267/10000000000 : ℝ)^4533 ≤ (43980838611481/100000000000000 : ℝ)^3509 := by
    have hnat : (5294804267 : ℕ)^4533*100000000000000^3509 ≤ 43980838611481^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294804267 10000000000 43980838611481 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438815889/2500000000 : ℝ)^4533 ≤ (528196526639/5000000000000 : ℝ)^3509 := by
    have hnat : (438815889 : ℕ)^4533*5000000000000^3509 ≤ 528196526639^3509*2500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438815889 2500000000 528196526639 5000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357923567/2500000000 : ℝ)^4533 ≤ (5681903856153/12500000000000 : ℝ)^3509 := by
    have hnat : (1357923567 : ℕ)^4533*12500000000000^3509 ≤ 5681903856153^3509*2500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357923567 2500000000 5681903856153 12500000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294804267/10000000000 : ℝ), (-438815889/2500000000 : ℝ), (1357923567/2500000000 : ℝ)] ![(43980838611481/100000000000000 : ℝ), (528196526639/5000000000000 : ℝ), (5681903856153/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294804267/10000000000 : ℝ)|^4533 ≤ (43980838611481/100000000000000 : ℝ)^3509
        have hw : |(5294804267/10000000000 : ℝ)|=(5294804267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-438815889/2500000000 : ℝ)|^4533 ≤ (528196526639/5000000000000 : ℝ)^3509
        have hw : |(-438815889/2500000000 : ℝ)|=(438815889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357923567/2500000000 : ℝ)|^4533 ≤ (5681903856153/12500000000000 : ℝ)^3509
        have hw : |(1357923567/2500000000 : ℝ)|=(1357923567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s4_6 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294804287/10000000000 : ℝ)*x 0 + (339480891/625000000 : ℝ)*x 1 + (-219407943/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294804287/10000000000 : ℝ)^4533 ≤ (43980838826089/100000000000000 : ℝ)^3509 := by
    have hnat : (5294804287 : ℕ)^4533*100000000000000^3509 ≤ 43980838826089^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294804287 10000000000 43980838826089 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339480891/625000000 : ℝ)^4533 ≤ (5681903839937/12500000000000 : ℝ)^3509 := by
    have hnat : (339480891 : ℕ)^4533*12500000000000^3509 ≤ 5681903839937^3509*625000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339480891 625000000 5681903839937 12500000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219407943/1250000000 : ℝ)^4533 ≤ (2640982609871/25000000000000 : ℝ)^3509 := by
    have hnat : (219407943 : ℕ)^4533*25000000000000^3509 ≤ 2640982609871^3509*1250000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219407943 1250000000 2640982609871 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294804287/10000000000 : ℝ), (339480891/625000000 : ℝ), (-219407943/1250000000 : ℝ)] ![(43980838826089/100000000000000 : ℝ), (5681903839937/12500000000000 : ℝ), (2640982609871/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294804287/10000000000 : ℝ)|^4533 ≤ (43980838826089/100000000000000 : ℝ)^3509
        have hw : |(5294804287/10000000000 : ℝ)|=(5294804287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339480891/625000000 : ℝ)|^4533 ≤ (5681903839937/12500000000000 : ℝ)^3509
        have hw : |(339480891/625000000 : ℝ)|=(339480891/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219407943/1250000000 : ℝ)|^4533 ≤ (2640982609871/25000000000000 : ℝ)^3509
        have hw : |(-219407943/1250000000 : ℝ)|=(219407943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s4_7 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (853403643/2000000000 : ℝ)*x 0 + (2257697073/5000000000 : ℝ)*x 1 + (806083249/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853403643/2000000000 : ℝ)^4533 ≤ (33280285695541/100000000000000 : ℝ)^3509 := by
    have hnat : (853403643 : ℕ)^4533*100000000000000^3509 ≤ 33280285695541^3509*2000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853403643 2000000000 33280285695541 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257697073/5000000000 : ℝ)^4533 ≤ (3580375680239/10000000000000 : ℝ)^3509 := by
    have hnat : (2257697073 : ℕ)^4533*10000000000000^3509 ≤ 3580375680239^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257697073 5000000000 3580375680239 10000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806083249/2000000000 : ℝ)^4533 ≤ (6183191498403/20000000000000 : ℝ)^3509 := by
    have hnat : (806083249 : ℕ)^4533*20000000000000^3509 ≤ 6183191498403^3509*2000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806083249 2000000000 6183191498403 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(853403643/2000000000 : ℝ), (2257697073/5000000000 : ℝ), (806083249/2000000000 : ℝ)] ![(33280285695541/100000000000000 : ℝ), (3580375680239/10000000000000 : ℝ), (6183191498403/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(853403643/2000000000 : ℝ)|^4533 ≤ (33280285695541/100000000000000 : ℝ)^3509
        have hw : |(853403643/2000000000 : ℝ)|=(853403643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2257697073/5000000000 : ℝ)|^4533 ≤ (3580375680239/10000000000000 : ℝ)^3509
        have hw : |(2257697073/5000000000 : ℝ)|=(2257697073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806083249/2000000000 : ℝ)|^4533 ≤ (6183191498403/20000000000000 : ℝ)^3509
        have hw : |(806083249/2000000000 : ℝ)|=(806083249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1518_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7773/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h) :
    (2733/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7773/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (68/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7773/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (68/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7773/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (68/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7773/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (68/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7773/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (68/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7773/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (68/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (68/625 : ℝ) ^ (4531/1024 : ℝ) ≤ (54609854622439/1000000000000000000 : ℝ) := by
    have hpowers : (68/625 : ℝ)^4531 ≤ (54609854622439/1000000000000000000 : ℝ)^1024 := by
      have hnat : (68 : ℕ)^4531*1000000000000000000^1024 ≤ 54609854622439^1024*625^4531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68 625 54609854622439 1000000000000000000 4531 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68/625 : ℝ)) (X := (54609854622439/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7773/50000 : ℝ) ^ (4531/1024 : ℝ) ≤ (26489299420831861/100000000000000000000 : ℝ) := by
    have hpowers : (7773/50000 : ℝ)^4531 ≤ (26489299420831861/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7773 : ℕ)^4531*100000000000000000000^1024 ≤ 26489299420831861^1024*50000^4531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7773 50000 26489299420831861 100000000000000000000 4531 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7773/50000 : ℝ)) (X := (26489299420831861/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (500054609854622439/500000000000000000 : ℝ) ≤ (5000123412332009/5000000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (500054609854622439/500000000000000000 : ℝ)^1024 ≤ (5000123412332009/5000000000000000 : ℝ)^4531 := by
      have hnat : (500054609854622439 : ℕ)^1024*5000000000000000^4531 ≤ 5000123412332009^4531*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500054609854622439 500000000000000000 5000123412332009 5000000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000123412332009/5000000000000000 : ℝ)) (X := (500054609854622439/500000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100031950284883075761/100000000000000000000 : ℝ) ≤ (10000721982941681/10000000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (100031950284883075761/100000000000000000000 : ℝ)^1024 ≤ (10000721982941681/10000000000000000 : ℝ)^4531 := by
      have hnat : (100031950284883075761 : ℕ)^1024*10000000000000000^4531 ≤ 10000721982941681^4531*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100031950284883075761 100000000000000000000 10000721982941681 10000000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000721982941681/10000000000000000 : ℝ)) (X := (100031950284883075761/100000000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026489299420831861/50000000000000000000 : ℝ) ≤ (625074821326209/625000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (50026489299420831861/50000000000000000000 : ℝ)^1024 ≤ (625074821326209/625000000000000 : ℝ)^4531 := by
      have hnat : (50026489299420831861 : ℕ)^1024*625000000000000^4531 ≤ 625074821326209^4531*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026489299420831861 50000000000000000000 625074821326209 625000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625074821326209/625000000000000 : ℝ)) (X := (50026489299420831861/50000000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(54609854622439/1000000000000000000 : ℝ) ≤ ((11662703059940090277/11665000000000000000 : ℝ)+2*(475158277663/466600000000000 : ℝ)*(68/625 : ℝ))^(4531/1024 : ℝ) := by
    rw [show (11662703059940090277/11665000000000000000 : ℝ)+2*(475158277663/466600000000000 : ℝ)*(68/625 : ℝ)=(5000123412332009/5000000000000000 : ℝ) by norm_num, show 1+2*(54609854622439/1000000000000000000 : ℝ)=(500054609854622439/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26489299420831861/100000000000000000000 : ℝ)+(54609854622439/1000000000000000000 : ℝ) ≤ ((11662703059940090277/11665000000000000000 : ℝ)+(475158277663/466600000000000 : ℝ)*((7773/50000 : ℝ)+(68/625 : ℝ)))^(4531/1024 : ℝ) := by
    rw [show (11662703059940090277/11665000000000000000 : ℝ)+(475158277663/466600000000000 : ℝ)*((7773/50000 : ℝ)+(68/625 : ℝ))=(10000721982941681/10000000000000000 : ℝ) by norm_num, show 1+(26489299420831861/100000000000000000000 : ℝ)+(54609854622439/1000000000000000000 : ℝ)=(100031950284883075761/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26489299420831861/100000000000000000000 : ℝ) ≤ ((11662703059940090277/11665000000000000000 : ℝ)+2*(475158277663/466600000000000 : ℝ)*(7773/50000 : ℝ))^(4531/1024 : ℝ) := by
    rw [show (11662703059940090277/11665000000000000000 : ℝ)+2*(475158277663/466600000000000 : ℝ)*(7773/50000 : ℝ)=(625074821326209/625000000000000 : ℝ) by norm_num, show 1+2*(26489299420831861/100000000000000000000 : ℝ)=(50026489299420831861/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11662703059940090277/11665000000000000000 : ℝ)*(X 1 0+X 2 0)+(475158277663/466600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (68/625 : ℝ)) (hi := (7773/50000 : ℝ)) (c := (11662703059940090277/11665000000000000000 : ℝ)) (alpha := (475158277663/466600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11662703059940090277/11665000000000000000 : ℝ)*(X 0 1+X 2 1)+(475158277663/466600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (68/625 : ℝ)) (hi := (7773/50000 : ℝ)) (c := (11662703059940090277/11665000000000000000 : ℝ)) (alpha := (475158277663/466600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11662703059940090277/11665000000000000000 : ℝ)*(X 0 2+X 1 2)+(475158277663/466600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (68/625 : ℝ)) (hi := (7773/50000 : ℝ)) (c := (11662703059940090277/11665000000000000000 : ℝ)) (alpha := (475158277663/466600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-74365447/400000000 : ℝ)*X 0 0+(5432815071/10000000000 : ℝ)*X 0 1+(260880407/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070269787/2000000000 : ℝ)*X 1 0+(-196934989/1000000000 : ℝ)*X 1 1+(5217608571/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351349249/10000000000 : ℝ)*X 2 0+(5217608287/10000000000 : ℝ)*X 2 1+(-246168731/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((426695193/1000000000 : ℝ)*X 0 0+(1006966053/2500000000 : ℝ)*X 0 1+(4517927711/10000000000 : ℝ)*X 0 2+(426695193/1000000000 : ℝ)*X 1 0+(1006966053/2500000000 : ℝ)*X 1 1+(4517927711/10000000000 : ℝ)*X 1 2+(426695193/1000000000 : ℝ)*X 2 0+(1006966053/2500000000 : ℝ)*X 2 1+(4517927711/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-371833007/2000000000 : ℝ)*X 0 0+(5218720817/10000000000 : ℝ)*X 0 1+(1357923567/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294804267/10000000000 : ℝ)*X 1 0+(-438815889/2500000000 : ℝ)*X 1 1+(1357923567/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294804287/10000000000 : ℝ)*X 2 0+(339480891/625000000 : ℝ)*X 2 1+(-219407943/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((853403643/2000000000 : ℝ)*X 0 0+(2257697073/5000000000 : ℝ)*X 0 1+(806083249/2000000000 : ℝ)*X 0 2+(853403643/2000000000 : ℝ)*X 1 0+(2257697073/5000000000 : ℝ)*X 1 1+(806083249/2000000000 : ℝ)*X 1 2+(853403643/2000000000 : ℝ)*X 2 0+(2257697073/5000000000 : ℝ)*X 2 1+(806083249/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2311141388549063555383027683/291625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (506956653/100000000000000 : ℝ)*(base19) + (334996499/50000000000000 : ℝ)*(base23) + (83385577/50000000000000 : ℝ)*(upper3) + (29330169/50000000000000 : ℝ)*(upper4) + (174759897/100000000000000 : ℝ)*(upper5) + (1671818379906507/50000000000000 : ℝ)*(major0) + (1671818379906507/50000000000000 : ℝ)*(major1) + (1671818379906507/50000000000000 : ℝ)*(major2) + (464670036716827/10000000000000 : ℝ)*(sp0) + (72604886715987/1562500000000 : ℝ)*(sp1) + (4646712586786823/100000000000000 : ℝ)*(sp2) + (2040555476591379/100000000000000 : ℝ)*(sp3) + (257792231/2000000000000 : ℝ)*(sp4) + (4522086637/100000000000000 : ℝ)*(sp7) + (1992734373709/97656250000 : ℝ)*(f.failure) + (4646713256779821/100000000000000 : ℝ)*(f.sum) + (7080904704127/1458125000000000000000000000 : ℝ)*base65 + (3237899040300757439/583250000000000000000000000000000 : ℝ)*base67 + (661890340122757439/583250000000000000000000000000000 : ℝ)*base69 + (705461581687007439/583250000000000000000000000000000 : ℝ)*base71 + (39791068776191/11665000000000000000000000000 : ℝ)*base73 + (1034118846233242561/583250000000000000000000000000000 : ℝ)*base76 + (81955755924257439/583250000000000000000000000000000 : ℝ)*base77 + (5224806892892492561/583250000000000000000000000000000 : ℝ)*base80 + (20521236615809/11665000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (171999/19531250000000000000 : ℝ)*base90 + (171999/19531250000000000000 : ℝ)*base92 + (171999/19531250000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19522892367487481962681413/3645312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (42856579/5000000000000 : ℝ)*(base19) + (966140891/100000000000000 : ℝ)*(base23) + (10808207/10000000000000 : ℝ)*(upper3) + (20470737/50000000000000 : ℝ)*(lower4) + (29552227/25000000000000 : ℝ)*(upper5) + (21116781794901/625000000000 : ℝ)*(major0) + (21116781794901/625000000000 : ℝ)*(major1) + (21116781794901/625000000000 : ℝ)*(major2) + (13241512353/100000000000000 : ℝ)*(sp1) + (227307151/1562500000000 : ℝ)*(sp2) + (2347710323895087/50000000000000 : ℝ)*(sp4) + (7336572733041/156250000000 : ℝ)*(sp5) + (2347702566995809/50000000000000 : ℝ)*(sp6) + (1030974674028811/50000000000000 : ℝ)*(sp7) + (1030974674028811/50000000000000 : ℝ)*(f.failure) + (2347710323895087/50000000000000 : ℝ)*(f.sum) + (286676295459/72906250000000000000000000 : ℝ)*base65 + (61735702237053673/7290625000000000000000000000000 : ℝ)*base68 + (38195005986958827/7290625000000000000000000000000 : ℝ)*base69 + (99279392409859/56958007812500000000000000000 : ℝ)*base71 + (1527509345271/1166500000000000000000000000 : ℝ)*base73 + (1917902265329619/911328125000000000000000000000 : ℝ)*base75 + (22994392532177577/7290625000000000000000000000000 : ℝ)*base77 + (12144898835465077/7290625000000000000000000000000 : ℝ)*base79 + (143940541357/46660000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1684101/2500000000000000000000 : ℝ)*base89 + (1684101/2500000000000000000000 : ℝ)*base91 + (1684101/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1518_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7773/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (68/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2733/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1518_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1518_s5_0 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1859186119/10000000000 : ℝ)*x 0 + (5432486973/10000000000 : ℝ)*x 1 + (5217903167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1859186119/10000000000 : ℝ)^4533 ≤ (1422348197797/12500000000000 : ℝ)^3509 := by
    have hnat : (1859186119 : ℕ)^4533*12500000000000^3509 ≤ 1422348197797^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859186119 10000000000 1422348197797 12500000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432486973/10000000000 : ℝ)^4533 ≤ (22731900335071/50000000000000 : ℝ)^3509 := by
    have hnat : (5432486973 : ℕ)^4533*50000000000000^3509 ≤ 22731900335071^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432486973 10000000000 22731900335071 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217903167/10000000000 : ℝ)^4533 ≤ (43157413723917/100000000000000 : ℝ)^3509 := by
    have hnat : (5217903167 : ℕ)^4533*100000000000000^3509 ≤ 43157413723917^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217903167 10000000000 43157413723917 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1859186119/10000000000 : ℝ), (5432486973/10000000000 : ℝ), (5217903167/10000000000 : ℝ)] ![(1422348197797/12500000000000 : ℝ), (22731900335071/50000000000000 : ℝ), (43157413723917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1859186119/10000000000 : ℝ)|^4533 ≤ (1422348197797/12500000000000 : ℝ)^3509
        have hw : |(-1859186119/10000000000 : ℝ)|=(1859186119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432486973/10000000000 : ℝ)|^4533 ≤ (22731900335071/50000000000000 : ℝ)^3509
        have hw : |(5432486973/10000000000 : ℝ)|=(5432486973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217903167/10000000000 : ℝ)|^4533 ≤ (43157413723917/100000000000000 : ℝ)^3509
        have hw : |(5217903167/10000000000 : ℝ)|=(5217903167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s5_1 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334453969/625000000 : ℝ)*x 0 + (-1969073317/10000000000 : ℝ)*x 1 + (1043580551/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334453969/625000000 : ℝ)^4533 ≤ (44587609084947/100000000000000 : ℝ)^3509 := by
    have hnat : (334453969 : ℕ)^4533*100000000000000^3509 ≤ 44587609084947^3509*625000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334453969 625000000 44587609084947 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1969073317/10000000000 : ℝ)^4533 ≤ (12254981582321/100000000000000 : ℝ)^3509 := by
    have hnat : (1969073317 : ℕ)^4533*100000000000000^3509 ≤ 12254981582321^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1969073317 10000000000 12254981582321 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043580551/2000000000 : ℝ)^4533 ≤ (43157409321827/100000000000000 : ℝ)^3509 := by
    have hnat : (1043580551 : ℕ)^4533*100000000000000^3509 ≤ 43157409321827^3509*2000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043580551 2000000000 43157409321827 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334453969/625000000 : ℝ), (-1969073317/10000000000 : ℝ), (1043580551/2000000000 : ℝ)] ![(44587609084947/100000000000000 : ℝ), (12254981582321/100000000000000 : ℝ), (43157409321827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334453969/625000000 : ℝ)|^4533 ≤ (44587609084947/100000000000000 : ℝ)^3509
        have hw : |(334453969/625000000 : ℝ)|=(334453969/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1969073317/10000000000 : ℝ)|^4533 ≤ (12254981582321/100000000000000 : ℝ)^3509
        have hw : |(-1969073317/10000000000 : ℝ)|=(1969073317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043580551/2000000000 : ℝ)|^4533 ≤ (43157409321827/100000000000000 : ℝ)^3509
        have hw : |(1043580551/2000000000 : ℝ)|=(1043580551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s5_2 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351264937/10000000000 : ℝ)*x 0 + (5217900731/10000000000 : ℝ)*x 1 + (-246134261/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351264937/10000000000 : ℝ)^4533 ≤ (278672653183/625000000000 : ℝ)^3509 := by
    have hnat : (5351264937 : ℕ)^4533*625000000000^3509 ≤ 278672653183^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351264937 10000000000 278672653183 625000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217900731/10000000000 : ℝ)^4533 ≤ (1726295507841/4000000000000 : ℝ)^3509 := by
    have hnat : (5217900731 : ℕ)^4533*4000000000000^3509 ≤ 1726295507841^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217900731 10000000000 1726295507841 4000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (246134261/1250000000 : ℝ)^4533 ≤ (2393552301/19531250000 : ℝ)^3509 := by
    have hnat : (246134261 : ℕ)^4533*19531250000^3509 ≤ 2393552301^3509*1250000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246134261 1250000000 2393552301 19531250000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351264937/10000000000 : ℝ), (5217900731/10000000000 : ℝ), (-246134261/1250000000 : ℝ)] ![(278672653183/625000000000 : ℝ), (1726295507841/4000000000000 : ℝ), (2393552301/19531250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351264937/10000000000 : ℝ)|^4533 ≤ (278672653183/625000000000 : ℝ)^3509
        have hw : |(5351264937/10000000000 : ℝ)|=(5351264937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217900731/10000000000 : ℝ)|^4533 ≤ (1726295507841/4000000000000 : ℝ)^3509
        have hw : |(5217900731/10000000000 : ℝ)|=(5217900731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-246134261/1250000000 : ℝ)|^4533 ≤ (2393552301/19531250000 : ℝ)^3509
        have hw : |(-246134261/1250000000 : ℝ)|=(246134261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s5_3 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4266987361/10000000000 : ℝ)*x 0 + (4028554531/10000000000 : ℝ)*x 1 + (4517225261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4266987361/10000000000 : ℝ)^4533 ≤ (16639987413807/50000000000000 : ℝ)^3509 := by
    have hnat : (4266987361 : ℕ)^4533*50000000000000^3509 ≤ 16639987413807^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4266987361 10000000000 16639987413807 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4028554531/10000000000 : ℝ)^4533 ≤ (6179502157073/20000000000000 : ℝ)^3509 := by
    have hnat : (4028554531 : ℕ)^4533*20000000000000^3509 ≤ 6179502157073^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028554531 10000000000 6179502157073 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4517225261/10000000000 : ℝ)^4533 ≤ (447781429667/1250000000000 : ℝ)^3509 := by
    have hnat : (4517225261 : ℕ)^4533*1250000000000^3509 ≤ 447781429667^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517225261 10000000000 447781429667 1250000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4266987361/10000000000 : ℝ), (4028554531/10000000000 : ℝ), (4517225261/10000000000 : ℝ)] ![(16639987413807/50000000000000 : ℝ), (6179502157073/20000000000000 : ℝ), (447781429667/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4266987361/10000000000 : ℝ)|^4533 ≤ (16639987413807/50000000000000 : ℝ)^3509
        have hw : |(4266987361/10000000000 : ℝ)|=(4266987361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4028554531/10000000000 : ℝ)|^4533 ≤ (6179502157073/20000000000000 : ℝ)^3509
        have hw : |(4028554531/10000000000 : ℝ)|=(4028554531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4517225261/10000000000 : ℝ)|^4533 ≤ (447781429667/1250000000000 : ℝ)^3509
        have hw : |(4517225261/10000000000 : ℝ)|=(4517225261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s5_4 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-929606673/5000000000 : ℝ)*x 0 + (5219006527/10000000000 : ℝ)*x 1 + (1086275307/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (929606673/5000000000 : ℝ)^4533 ≤ (1137900084871/10000000000000 : ℝ)^3509 := by
    have hnat : (929606673 : ℕ)^4533*10000000000000^3509 ≤ 1137900084871^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929606673 5000000000 1137900084871 10000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219006527/10000000000 : ℝ)^4533 ≤ (10792300785579/25000000000000 : ℝ)^3509 := by
    have hnat : (5219006527 : ℕ)^4533*25000000000000^3509 ≤ 10792300785579^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219006527 10000000000 10792300785579 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086275307/2000000000 : ℝ)^4533 ≤ (45451795985447/100000000000000 : ℝ)^3509 := by
    have hnat : (1086275307 : ℕ)^4533*100000000000000^3509 ≤ 45451795985447^3509*2000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086275307 2000000000 45451795985447 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-929606673/5000000000 : ℝ), (5219006527/10000000000 : ℝ), (1086275307/2000000000 : ℝ)] ![(1137900084871/10000000000000 : ℝ), (10792300785579/25000000000000 : ℝ), (45451795985447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-929606673/5000000000 : ℝ)|^4533 ≤ (1137900084871/10000000000000 : ℝ)^3509
        have hw : |(-929606673/5000000000 : ℝ)|=(929606673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219006527/10000000000 : ℝ)|^4533 ≤ (10792300785579/25000000000000 : ℝ)^3509
        have hw : |(5219006527/10000000000 : ℝ)|=(5219006527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086275307/2000000000 : ℝ)|^4533 ≤ (45451795985447/100000000000000 : ℝ)^3509
        have hw : |(1086275307/2000000000 : ℝ)|=(1086275307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s5_5 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294881407/10000000000 : ℝ)*x 0 + (-877799447/5000000000 : ℝ)*x 1 + (5431376523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294881407/10000000000 : ℝ)^4533 ≤ (10995416589091/25000000000000 : ℝ)^3509 := by
    have hnat : (5294881407 : ℕ)^4533*25000000000000^3509 ≤ 10995416589091^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294881407 10000000000 10995416589091 25000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (877799447/5000000000 : ℝ)^4533 ≤ (10566537769279/100000000000000 : ℝ)^3509 := by
    have hnat : (877799447 : ℕ)^4533*100000000000000^3509 ≤ 10566537769279^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877799447 5000000000 10566537769279 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431376523/10000000000 : ℝ)^4533 ≤ (22725897927861/50000000000000 : ℝ)^3509 := by
    have hnat : (5431376523 : ℕ)^4533*50000000000000^3509 ≤ 22725897927861^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431376523 10000000000 22725897927861 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294881407/10000000000 : ℝ), (-877799447/5000000000 : ℝ), (5431376523/10000000000 : ℝ)] ![(10995416589091/25000000000000 : ℝ), (10566537769279/100000000000000 : ℝ), (22725897927861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294881407/10000000000 : ℝ)|^4533 ≤ (10995416589091/25000000000000 : ℝ)^3509
        have hw : |(5294881407/10000000000 : ℝ)|=(5294881407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-877799447/5000000000 : ℝ)|^4533 ≤ (10566537769279/100000000000000 : ℝ)^3509
        have hw : |(-877799447/5000000000 : ℝ)|=(877799447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431376523/10000000000 : ℝ)|^4533 ≤ (22725897927861/50000000000000 : ℝ)^3509
        have hw : |(5431376523/10000000000 : ℝ)|=(5431376523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s5_6 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058976283/2000000000 : ℝ)*x 0 + (5431376507/10000000000 : ℝ)*x 1 + (-877799453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058976283/2000000000 : ℝ)^4533 ≤ (1374427076319/3125000000000 : ℝ)^3509 := by
    have hnat : (1058976283 : ℕ)^4533*3125000000000^3509 ≤ 1374427076319^3509*2000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058976283 2000000000 1374427076319 3125000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431376507/10000000000 : ℝ)^4533 ≤ (22725897841377/50000000000000 : ℝ)^3509 := by
    have hnat : (5431376507 : ℕ)^4533*50000000000000^3509 ≤ 22725897841377^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431376507 10000000000 22725897841377 50000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (877799453/5000000000 : ℝ)^4533 ≤ (10566537862581/100000000000000 : ℝ)^3509 := by
    have hnat : (877799453 : ℕ)^4533*100000000000000^3509 ≤ 10566537862581^3509*5000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      877799453 5000000000 10566537862581 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058976283/2000000000 : ℝ), (5431376507/10000000000 : ℝ), (-877799453/5000000000 : ℝ)] ![(1374427076319/3125000000000 : ℝ), (22725897841377/50000000000000 : ℝ), (10566537862581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058976283/2000000000 : ℝ)|^4533 ≤ (1374427076319/3125000000000 : ℝ)^3509
        have hw : |(1058976283/2000000000 : ℝ)|=(1058976283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431376507/10000000000 : ℝ)|^4533 ≤ (22725897841377/50000000000000 : ℝ)^3509
        have hw : |(5431376507/10000000000 : ℝ)|=(5431376507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-877799453/5000000000 : ℝ)|^4533 ≤ (10566537862581/100000000000000 : ℝ)^3509
        have hw : |(-877799453/5000000000 : ℝ)|=(877799453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1518_s5_7 (p : ℝ) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4267048077/10000000000 : ℝ)*x 0 + (1128675877/2500000000 : ℝ)*x 1 + (4031099771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4267048077/10000000000 : ℝ)^4533 ≤ (33280586569247/100000000000000 : ℝ)^3509 := by
    have hnat : (4267048077 : ℕ)^4533*100000000000000^3509 ≤ 33280586569247^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4267048077 10000000000 33280586569247 100000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128675877/2500000000 : ℝ)^4533 ≤ (447458532789/1250000000000 : ℝ)^3509 := by
    have hnat : (1128675877 : ℕ)^4533*1250000000000^3509 ≤ 447458532789^3509*2500000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128675877 2500000000 447458532789 1250000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4031099771/10000000000 : ℝ)^4533 ≤ (6184546160353/20000000000000 : ℝ)^3509 := by
    have hnat : (4031099771 : ℕ)^4533*20000000000000^3509 ≤ 6184546160353^3509*10000000000^4533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4031099771 10000000000 6184546160353 20000000000000 4533 3509 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4533/1024 : ℝ)) 4533 3509 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4267048077/10000000000 : ℝ), (1128675877/2500000000 : ℝ), (4031099771/10000000000 : ℝ)] ![(33280586569247/100000000000000 : ℝ), (447458532789/1250000000000 : ℝ), (6184546160353/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4267048077/10000000000 : ℝ)|^4533 ≤ (33280586569247/100000000000000 : ℝ)^3509
        have hw : |(4267048077/10000000000 : ℝ)|=(4267048077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1128675877/2500000000 : ℝ)|^4533 ≤ (447458532789/1250000000000 : ℝ)^3509
        have hw : |(1128675877/2500000000 : ℝ)|=(1128675877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4031099771/10000000000 : ℝ)|^4533 ≤ (6184546160353/20000000000000 : ℝ)^3509
        have hw : |(4031099771/10000000000 : ℝ)|=(4031099771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1518_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2733/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5469/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (2733/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2733/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2733/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2733/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2733/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (2733/25000 : ℝ) ^ (4531/1024 : ℝ) ≤ (2788711516505127/50000000000000000000 : ℝ) := by
    have hpowers : (2733/25000 : ℝ)^4531 ≤ (2788711516505127/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2733 : ℕ)^4531*50000000000000000000^1024 ≤ 2788711516505127^1024*25000^4531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2733 25000 2788711516505127 50000000000000000000 4531 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2733/25000 : ℝ)) (X := (2788711516505127/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4531/1024 : ℝ) ≤ (3258710122621613/12500000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4531 ≤ (3258710122621613/12500000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4531*12500000000000000000^1024 ≤ 3258710122621613^1024*10000^4531 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 3258710122621613 12500000000000000000 4531 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (3258710122621613/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002788711516505127/25000000000000000000 : ℝ) ≤ (1000025208716177/1000000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (25002788711516505127/25000000000000000000 : ℝ)^1024 ≤ (1000025208716177/1000000000000000 : ℝ)^4531 := by
      have hnat : (25002788711516505127 : ℕ)^1024*1000000000000000^4531 ≤ 1000025208716177^4531*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002788711516505127 25000000000000000000 1000025208716177 1000000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000025208716177/1000000000000000 : ℝ)) (X := (25002788711516505127/25000000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50015823552006991579/50000000000000000000 : ℝ) ≤ (1250089391597513/1250000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (50015823552006991579/50000000000000000000 : ℝ)^1024 ≤ (1250089391597513/1250000000000000 : ℝ)^4531 := by
      have hnat : (50015823552006991579 : ℕ)^1024*1250000000000000^4531 ≤ 1250089391597513^4531*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015823552006991579 50000000000000000000 1250089391597513 1250000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250089391597513/1250000000000000 : ℝ)) (X := (50015823552006991579/50000000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253258710122621613/6250000000000000000 : ℝ) ≤ (5000589089199219/5000000000000000 : ℝ) ^ (4531/1024 : ℝ) := by
    have hpowers : (6253258710122621613/6250000000000000000 : ℝ)^1024 ≤ (5000589089199219/5000000000000000 : ℝ)^4531 := by
      have hnat : (6253258710122621613 : ℕ)^1024*5000000000000000^4531 ≤ 5000589089199219^4531*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253258710122621613 6250000000000000000 5000589089199219 5000000000000000 1024 4531 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000589089199219/5000000000000000 : ℝ)) (X := (6253258710122621613/6250000000000000000 : ℝ)) (by norm_num) 4531 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2788711516505127/50000000000000000000 : ℝ) ≤ ((11392756245971023271/11395000000000000000 : ℝ)+2*(231522809167/227900000000000 : ℝ)*(2733/25000 : ℝ))^(4531/1024 : ℝ) := by
    rw [show (11392756245971023271/11395000000000000000 : ℝ)+2*(231522809167/227900000000000 : ℝ)*(2733/25000 : ℝ)=(1000025208716177/1000000000000000 : ℝ) by norm_num, show 1+2*(2788711516505127/50000000000000000000 : ℝ)=(25002788711516505127/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3258710122621613/12500000000000000000 : ℝ)+(2788711516505127/50000000000000000000 : ℝ) ≤ ((11392756245971023271/11395000000000000000 : ℝ)+(231522809167/227900000000000 : ℝ)*((1549/10000 : ℝ)+(2733/25000 : ℝ)))^(4531/1024 : ℝ) := by
    rw [show (11392756245971023271/11395000000000000000 : ℝ)+(231522809167/227900000000000 : ℝ)*((1549/10000 : ℝ)+(2733/25000 : ℝ))=(1250089391597513/1250000000000000 : ℝ) by norm_num, show 1+(3258710122621613/12500000000000000000 : ℝ)+(2788711516505127/50000000000000000000 : ℝ)=(50015823552006991579/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3258710122621613/12500000000000000000 : ℝ) ≤ ((11392756245971023271/11395000000000000000 : ℝ)+2*(231522809167/227900000000000 : ℝ)*(1549/10000 : ℝ))^(4531/1024 : ℝ) := by
    rw [show (11392756245971023271/11395000000000000000 : ℝ)+2*(231522809167/227900000000000 : ℝ)*(1549/10000 : ℝ)=(5000589089199219/5000000000000000 : ℝ) by norm_num, show 1+2*(3258710122621613/12500000000000000000 : ℝ)=(6253258710122621613/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11392756245971023271/11395000000000000000 : ℝ)*(X 1 0+X 2 0)+(231522809167/227900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (2733/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11392756245971023271/11395000000000000000 : ℝ)) (alpha := (231522809167/227900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11392756245971023271/11395000000000000000 : ℝ)*(X 0 1+X 2 1)+(231522809167/227900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (2733/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11392756245971023271/11395000000000000000 : ℝ)) (alpha := (231522809167/227900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11392756245971023271/11395000000000000000 : ℝ)*(X 0 2+X 1 2)+(231522809167/227900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4531/1024 : ℝ)) (lo := (2733/25000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (11392756245971023271/11395000000000000000 : ℝ)) (alpha := (231522809167/227900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1859186119/10000000000 : ℝ)*X 0 0+(5432486973/10000000000 : ℝ)*X 0 1+(5217903167/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334453969/625000000 : ℝ)*X 1 0+(-1969073317/10000000000 : ℝ)*X 1 1+(1043580551/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351264937/10000000000 : ℝ)*X 2 0+(5217900731/10000000000 : ℝ)*X 2 1+(-246134261/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4266987361/10000000000 : ℝ)*X 0 0+(4028554531/10000000000 : ℝ)*X 0 1+(4517225261/10000000000 : ℝ)*X 0 2+(4266987361/10000000000 : ℝ)*X 1 0+(4028554531/10000000000 : ℝ)*X 1 1+(4517225261/10000000000 : ℝ)*X 1 2+(4266987361/10000000000 : ℝ)*X 2 0+(4028554531/10000000000 : ℝ)*X 2 1+(4517225261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-929606673/5000000000 : ℝ)*X 0 0+(5219006527/10000000000 : ℝ)*X 0 1+(1086275307/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294881407/10000000000 : ℝ)*X 1 0+(-877799447/5000000000 : ℝ)*X 1 1+(5431376523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058976283/2000000000 : ℝ)*X 2 0+(5431376507/10000000000 : ℝ)*X 2 1+(-877799453/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4267048077/10000000000 : ℝ)*X 0 0+(1128675877/2500000000 : ℝ)*X 0 1+(4031099771/10000000000 : ℝ)*X 0 2+(4267048077/10000000000 : ℝ)*X 1 0+(1128675877/2500000000 : ℝ)*X 1 1+(4031099771/10000000000 : ℝ)*X 1 2+(4267048077/10000000000 : ℝ)*X 2 0+(1128675877/2500000000 : ℝ)*X 2 1+(4031099771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1518_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (117184822291259776419803877/284875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3163589089/100000000000000 : ℝ)*(base19) + (1976264477/50000000000000 : ℝ)*(base23) + (258164317/100000000000000 : ℝ)*(lower2) + (165107361/12500000000000 : ℝ)*(upper3) + (6270473/50000000000000 : ℝ)*(lower4) + (110404619/25000000000000 : ℝ)*(upper5) + (1676670083182043/50000000000000 : ℝ)*(major0) + (1676670083182043/50000000000000 : ℝ)*(major1) + (1676670083182043/50000000000000 : ℝ)*(major2) + (4660198509842319/100000000000000 : ℝ)*(sp0) + (4660195346253229/100000000000000 : ℝ)*(sp1) + (932038911462673/20000000000000 : ℝ)*(sp2) + (2046417514062437/100000000000000 : ℝ)*(sp3) + (64295111567/100000000000000 : ℝ)*(sp7) + (2046481809174003/100000000000000 : ℝ)*(f.failure) + (4660198509842319/100000000000000 : ℝ)*(f.sum) + (15950327333363/11395000000000000000000000000 : ℝ)*base66 + (2344253299141127347/569750000000000000000000000000000 : ℝ)*base68 + (6595247509576877347/569750000000000000000000000000000 : ℝ)*base70 + (7322717610390627347/569750000000000000000000000000000 : ℝ)*base72 + (3652691429297/2848750000000000000000000000 : ℝ)*base74 + (4057593328711377347/569750000000000000000000000000000 : ℝ)*base76 + (1372321873973377347/569750000000000000000000000000000 : ℝ)*base78 + (1420095683244127347/569750000000000000000000000000000 : ℝ)*base80 + (1508005786399/356093750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (21177827/5000000000000000000000 : ℝ)*base90 + (21177827/5000000000000000000000 : ℝ)*base92 + (21177827/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (207419295073199848958101017/71218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92477689/20000000000000 : ℝ)*(base19) + (51435763/10000000000000 : ℝ)*(base23) + (154614961/100000000000000 : ℝ)*(lower1) + (50982407/100000000000000 : ℝ)*(upper3) + (11481049/50000000000000 : ℝ)*(lower4) + (803017/1250000000000 : ℝ)*(upper5) + (847070107145409/25000000000000 : ℝ)*(major0) + (847070107145409/25000000000000 : ℝ)*(major1) + (847070107145409/25000000000000 : ℝ)*(major2) + (4367153/3125000000000 : ℝ)*(sp2) + (4708755551703867/100000000000000 : ℝ)*(sp4) + (2354377544657711/50000000000000 : ℝ)*(sp5) + (4708754897597341/100000000000000 : ℝ)*(sp6) + (2067805208378539/100000000000000 : ℝ)*(sp7) + (2067805208378539/100000000000000 : ℝ)*(f.failure) + (4708755551703867/100000000000000 : ℝ)*(f.sum) + (73412277770417/11395000000000000000000000000 : ℝ)*base65 + (5901021832409912161/284875000000000000000000000000000 : ℝ)*base68 + (2144665977328287161/284875000000000000000000000000000 : ℝ)*base70 + (33358135662227912161/284875000000000000000000000000000 : ℝ)*base72 + (5499688146667/2848750000000000000000000000 : ℝ)*base74 + (9620649626894337839/284875000000000000000000000000000 : ℝ)*base75 + (272017704143787161/284875000000000000000000000000000 : ℝ)*base78 + (2312671082930662161/284875000000000000000000000000000 : ℝ)*base80 + (11262942116087/11395000000000000000000000000 : ℝ)*base81 + (2260251/5000000000000000000000 : ℝ)*base90 + (2260251/5000000000000000000000 : ℝ)*base92 + (2260251/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1518_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2733/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5469/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1518_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1518_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7987/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5469/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1518_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1518_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1518_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4531/1024 : ℝ) ≤ p) (hpb : p ≤ (4533/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (81929391/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7987/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10487/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5469/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1518_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

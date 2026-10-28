-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1279_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:22:26.572963+00:00
-- url     : https://prove2.me/submissions/26b3e298-f128-4f42-aa24-63a43f37e078

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
theorem support_rectangle_w1279_s9_0 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674980223/5000000000 : ℝ)*x 0 + (655318873/1250000000 : ℝ)*x 1 + (-2188034629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674980223/5000000000 : ℝ)^4239 ≤ (2739733652697/6250000000000 : ℝ)^3215 := by
    have hnat : (2674980223 : ℕ)^4239*6250000000000^3215 ≤ 2739733652697^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674980223 5000000000 2739733652697 6250000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655318873/1250000000 : ℝ)^4239 ≤ (42679078907823/100000000000000 : ℝ)^3215 := by
    have hnat : (655318873 : ℕ)^4239*100000000000000^3215 ≤ 42679078907823^3215*1250000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655318873 1250000000 42679078907823 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2188034629/10000000000 : ℝ)^4239 ≤ (13485182626123/100000000000000 : ℝ)^3215 := by
    have hnat : (2188034629 : ℕ)^4239*100000000000000^3215 ≤ 13485182626123^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188034629 10000000000 13485182626123 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674980223/5000000000 : ℝ), (655318873/1250000000 : ℝ), (-2188034629/10000000000 : ℝ)] ![(2739733652697/6250000000000 : ℝ), (42679078907823/100000000000000 : ℝ), (13485182626123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674980223/5000000000 : ℝ)|^4239 ≤ (2739733652697/6250000000000 : ℝ)^3215
        have hw : |(2674980223/5000000000 : ℝ)|=(2674980223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655318873/1250000000 : ℝ)|^4239 ≤ (42679078907823/100000000000000 : ℝ)^3215
        have hw : |(655318873/1250000000 : ℝ)|=(655318873/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2188034629/10000000000 : ℝ)|^4239 ≤ (13485182626123/100000000000000 : ℝ)^3215
        have hw : |(-2188034629/10000000000 : ℝ)|=(2188034629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s9_1 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-419938679/2000000000 : ℝ)*x 0 + (5243167737/10000000000 : ℝ)*x 1 + (54152389/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419938679/2000000000 : ℝ)^4239 ≤ (12771966968151/100000000000000 : ℝ)^3215 := by
    have hnat : (419938679 : ℕ)^4239*100000000000000^3215 ≤ 12771966968151^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419938679 2000000000 12771966968151 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243167737/10000000000 : ℝ)^4239 ≤ (5335712394407/12500000000000 : ℝ)^3215 := by
    have hnat : (5243167737 : ℕ)^4239*12500000000000^3215 ≤ 5335712394407^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243167737 10000000000 5335712394407 12500000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54152389/100000000 : ℝ)^4239 ≤ (11135583465361/25000000000000 : ℝ)^3215 := by
    have hnat : (54152389 : ℕ)^4239*25000000000000^3215 ≤ 11135583465361^3215*100000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54152389 100000000 11135583465361 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-419938679/2000000000 : ℝ), (5243167737/10000000000 : ℝ), (54152389/100000000 : ℝ)] ![(12771966968151/100000000000000 : ℝ), (5335712394407/12500000000000 : ℝ), (11135583465361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-419938679/2000000000 : ℝ)|^4239 ≤ (12771966968151/100000000000000 : ℝ)^3215
        have hw : |(-419938679/2000000000 : ℝ)|=(419938679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243167737/10000000000 : ℝ)|^4239 ≤ (5335712394407/12500000000000 : ℝ)^3215
        have hw : |(5243167737/10000000000 : ℝ)|=(5243167737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54152389/100000000 : ℝ)|^4239 ≤ (11135583465361/25000000000000 : ℝ)^3215
        have hw : |(54152389/100000000 : ℝ)|=(54152389/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s9_2 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652831591/5000000000 : ℝ)*x 0 + (-2015346379/10000000000 : ℝ)*x 1 + (54152389/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652831591/5000000000 : ℝ)^4239 ≤ (867156197873/2000000000000 : ℝ)^3215 := by
    have hnat : (2652831591 : ℕ)^4239*2000000000000^3215 ≤ 867156197873^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652831591 5000000000 867156197873 2000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015346379/10000000000 : ℝ)^4239 ≤ (604992811637/5000000000000 : ℝ)^3215 := by
    have hnat : (2015346379 : ℕ)^4239*5000000000000^3215 ≤ 604992811637^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015346379 10000000000 604992811637 5000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54152389/100000000 : ℝ)^4239 ≤ (11135583465361/25000000000000 : ℝ)^3215 := by
    have hnat : (54152389 : ℕ)^4239*25000000000000^3215 ≤ 11135583465361^3215*100000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54152389 100000000 11135583465361 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652831591/5000000000 : ℝ), (-2015346379/10000000000 : ℝ), (54152389/100000000 : ℝ)] ![(867156197873/2000000000000 : ℝ), (604992811637/5000000000000 : ℝ), (11135583465361/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652831591/5000000000 : ℝ)|^4239 ≤ (867156197873/2000000000000 : ℝ)^3215
        have hw : |(2652831591/5000000000 : ℝ)|=(2652831591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2015346379/10000000000 : ℝ)|^4239 ≤ (604992811637/5000000000000 : ℝ)^3215
        have hw : |(-2015346379/10000000000 : ℝ)|=(2015346379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54152389/100000000 : ℝ)|^4239 ≤ (11135583465361/25000000000000 : ℝ)^3215
        have hw : |(54152389/100000000 : ℝ)|=(54152389/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s9_3 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652831591/5000000000 : ℝ)*x 0 + (54152389/100000000 : ℝ)*x 1 + (-2015346379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652831591/5000000000 : ℝ)^4239 ≤ (867156197873/2000000000000 : ℝ)^3215 := by
    have hnat : (2652831591 : ℕ)^4239*2000000000000^3215 ≤ 867156197873^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652831591 5000000000 867156197873 2000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54152389/100000000 : ℝ)^4239 ≤ (11135583465361/25000000000000 : ℝ)^3215 := by
    have hnat : (54152389 : ℕ)^4239*25000000000000^3215 ≤ 11135583465361^3215*100000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54152389 100000000 11135583465361 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015346379/10000000000 : ℝ)^4239 ≤ (604992811637/5000000000000 : ℝ)^3215 := by
    have hnat : (2015346379 : ℕ)^4239*5000000000000^3215 ≤ 604992811637^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015346379 10000000000 604992811637 5000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652831591/5000000000 : ℝ), (54152389/100000000 : ℝ), (-2015346379/10000000000 : ℝ)] ![(867156197873/2000000000000 : ℝ), (11135583465361/25000000000000 : ℝ), (604992811637/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652831591/5000000000 : ℝ)|^4239 ≤ (867156197873/2000000000000 : ℝ)^3215
        have hw : |(2652831591/5000000000 : ℝ)|=(2652831591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54152389/100000000 : ℝ)|^4239 ≤ (11135583465361/25000000000000 : ℝ)^3215
        have hw : |(54152389/100000000 : ℝ)|=(54152389/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2015346379/10000000000 : ℝ)|^4239 ≤ (604992811637/5000000000000 : ℝ)^3215
        have hw : |(-2015346379/10000000000 : ℝ)|=(2015346379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_s9_4 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (542924597/1250000000 : ℝ)*x 0 + (4522795531/10000000000 : ℝ)*x 1 + (2085452181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542924597/1250000000 : ℝ)^4239 ≤ (16651205151609/50000000000000 : ℝ)^3215 := by
    have hnat : (542924597 : ℕ)^4239*50000000000000^3215 ≤ 16651205151609^3215*1250000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542924597 1250000000 16651205151609 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4522795531/10000000000 : ℝ)^4239 ≤ (17563928563269/50000000000000 : ℝ)^3215 := by
    have hnat : (4522795531 : ℕ)^4239*50000000000000^3215 ≤ 17563928563269^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522795531 10000000000 17563928563269 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085452181/5000000000 : ℝ)^4239 ≤ (15784866274261/50000000000000 : ℝ)^3215 := by
    have hnat : (2085452181 : ℕ)^4239*50000000000000^3215 ≤ 15784866274261^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085452181 5000000000 15784866274261 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542924597/1250000000 : ℝ), (4522795531/10000000000 : ℝ), (2085452181/5000000000 : ℝ)] ![(16651205151609/50000000000000 : ℝ), (17563928563269/50000000000000 : ℝ), (15784866274261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542924597/1250000000 : ℝ)|^4239 ≤ (16651205151609/50000000000000 : ℝ)^3215
        have hw : |(542924597/1250000000 : ℝ)|=(542924597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4522795531/10000000000 : ℝ)|^4239 ≤ (17563928563269/50000000000000 : ℝ)^3215
        have hw : |(4522795531/10000000000 : ℝ)|=(4522795531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085452181/5000000000 : ℝ)|^4239 ≤ (15784866274261/50000000000000 : ℝ)^3215
        have hw : |(2085452181/5000000000 : ℝ)|=(2085452181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1279_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2199/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2199/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7331/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14663/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2199/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14663/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2199/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14663/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2199/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14663/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2199/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14663/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2199/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14663/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2199/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2199/20000 : ℝ) ^ (2119/512 : ℝ) ≤ (10760233112095753/100000000000000000000 : ℝ) := by
    have hpowers : (2199/20000 : ℝ)^2119 ≤ (10760233112095753/100000000000000000000 : ℝ)^512 := by
      have hnat : (2199 : ℕ)^2119*100000000000000000000^512 ≤ 10760233112095753^512*20000^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2199 20000 10760233112095753 100000000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2199/20000 : ℝ)) (X := (10760233112095753/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14663/100000 : ℝ) ^ (2119/512 : ℝ) ≤ (35421740364723377/100000000000000000000 : ℝ) := by
    have hpowers : (14663/100000 : ℝ)^2119 ≤ (35421740364723377/100000000000000000000 : ℝ)^512 := by
      have hnat : (14663 : ℕ)^2119*100000000000000000000^512 ≤ 35421740364723377^512*100000^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14663 100000 35421740364723377 100000000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14663/100000 : ℝ)) (X := (35421740364723377/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010760233112095753/50000000000000000000 : ℝ) ≤ (1000051994241049/1000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (50010760233112095753/50000000000000000000 : ℝ)^512 ≤ (1000051994241049/1000000000000000 : ℝ)^2119 := by
      have hnat : (50010760233112095753 : ℕ)^512*1000000000000000^2119 ≤ 1000051994241049^2119*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010760233112095753 50000000000000000000 1000051994241049 1000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000051994241049/1000000000000000 : ℝ)) (X := (50010760233112095753/50000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004618197347681913/10000000000000000000 : ℝ) ≤ (2500278917306251/2500000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (10004618197347681913/10000000000000000000 : ℝ)^512 ≤ (2500278917306251/2500000000000000 : ℝ)^2119 := by
      have hnat : (10004618197347681913 : ℕ)^512*2500000000000000^2119 ≤ 2500278917306251^2119*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004618197347681913 10000000000000000000 2500278917306251 2500000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500278917306251/2500000000000000 : ℝ)) (X := (10004618197347681913/10000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035421740364723377/50000000000000000000 : ℝ) ≤ (5000855698019759/5000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (50035421740364723377/50000000000000000000 : ℝ)^512 ≤ (5000855698019759/5000000000000000 : ℝ)^2119 := by
      have hnat : (50035421740364723377 : ℕ)^512*5000000000000000^2119 ≤ 5000855698019759^2119*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035421740364723377 50000000000000000000 5000855698019759 5000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000855698019759/5000000000000000 : ℝ)) (X := (50035421740364723377/50000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10760233112095753/100000000000000000000 : ℝ) ≤ ((1833440355805525723/1834000000000000000 : ℝ)+2*(297863407257/183400000000000 : ℝ)*(2199/20000 : ℝ))^(2119/512 : ℝ) := by
    rw [show (1833440355805525723/1834000000000000000 : ℝ)+2*(297863407257/183400000000000 : ℝ)*(2199/20000 : ℝ)=(1000051994241049/1000000000000000 : ℝ) by norm_num, show 1+2*(10760233112095753/100000000000000000000 : ℝ)=(50010760233112095753/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35421740364723377/100000000000000000000 : ℝ)+(10760233112095753/100000000000000000000 : ℝ) ≤ ((1833440355805525723/1834000000000000000 : ℝ)+(297863407257/183400000000000 : ℝ)*((14663/100000 : ℝ)+(2199/20000 : ℝ)))^(2119/512 : ℝ) := by
    rw [show (1833440355805525723/1834000000000000000 : ℝ)+(297863407257/183400000000000 : ℝ)*((14663/100000 : ℝ)+(2199/20000 : ℝ))=(2500278917306251/2500000000000000 : ℝ) by norm_num, show 1+(35421740364723377/100000000000000000000 : ℝ)+(10760233112095753/100000000000000000000 : ℝ)=(10004618197347681913/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35421740364723377/100000000000000000000 : ℝ) ≤ ((1833440355805525723/1834000000000000000 : ℝ)+2*(297863407257/183400000000000 : ℝ)*(14663/100000 : ℝ))^(2119/512 : ℝ) := by
    rw [show (1833440355805525723/1834000000000000000 : ℝ)+2*(297863407257/183400000000000 : ℝ)*(14663/100000 : ℝ)=(5000855698019759/5000000000000000 : ℝ) by norm_num, show 1+2*(35421740364723377/100000000000000000000 : ℝ)=(50035421740364723377/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1833440355805525723/1834000000000000000 : ℝ)*(X 1 0+X 2 0)+(297863407257/183400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (2199/20000 : ℝ)) (hi := (14663/100000 : ℝ)) (c := (1833440355805525723/1834000000000000000 : ℝ)) (alpha := (297863407257/183400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1833440355805525723/1834000000000000000 : ℝ)*(X 0 1+X 2 1)+(297863407257/183400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (2199/20000 : ℝ)) (hi := (14663/100000 : ℝ)) (c := (1833440355805525723/1834000000000000000 : ℝ)) (alpha := (297863407257/183400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1833440355805525723/1834000000000000000 : ℝ)*(X 0 2+X 1 2)+(297863407257/183400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (2199/20000 : ℝ)) (hi := (14663/100000 : ℝ)) (c := (1833440355805525723/1834000000000000000 : ℝ)) (alpha := (297863407257/183400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2674980223/5000000000 : ℝ)*X 2 0+(655318873/1250000000 : ℝ)*X 2 1+(-2188034629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s9_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-419938679/2000000000 : ℝ)*X 0 0+(5243167737/10000000000 : ℝ)*X 0 1+(54152389/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2652831591/5000000000 : ℝ)*X 1 0+(-2015346379/10000000000 : ℝ)*X 1 1+(54152389/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2652831591/5000000000 : ℝ)*X 2 0+(54152389/100000000 : ℝ)*X 2 1+(-2015346379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((542924597/1250000000 : ℝ)*X 0 0+(4522795531/10000000000 : ℝ)*X 0 1+(2085452181/5000000000 : ℝ)*X 0 2+(542924597/1250000000 : ℝ)*X 1 0+(4522795531/10000000000 : ℝ)*X 1 1+(2085452181/5000000000 : ℝ)*X 1 2+(542924597/1250000000 : ℝ)*X 2 0+(4522795531/10000000000 : ℝ)*X 2 1+(2085452181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (680094826665981569841/327500000000000000000000000 : ℝ) := by norm_num
    linear_combination (372803371/100000000000000 : ℝ)*(base19) + (2031203/500000000000 : ℝ)*(base23) + (128469311/100000000000000 : ℝ)*(lower1) + (42452131/100000000000000 : ℝ)*(upper3) + (15164793/100000000000000 : ℝ)*(lower4) + (42824807/100000000000000 : ℝ)*(upper5) + (2163331325417129/50000000000000 : ℝ)*(major0) + (2163331325417129/50000000000000 : ℝ)*(major1) + (2163331325417129/50000000000000 : ℝ)*(major2) + (116299437/20000000000000 : ℝ)*(sp0) + (72644265947507/1250000000000 : ℝ)*(sp1) + (5811540902997189/100000000000000 : ℝ)*(sp2) + (726442536007847/12500000000000 : ℝ)*(sp3) + (2841783956647099/100000000000000 : ℝ)*(sp4) + (2841783956647099/100000000000000 : ℝ)*(f.failure) + (72644265947507/1250000000000 : ℝ)*(f.sum) + (988535855841/655000000000000000000000000 : ℝ)*base66 + (29523042394934181/13100000000000000000000000000000 : ℝ)*base67 + (183940831003034181/13100000000000000000000000000000 : ℝ)*base69 + (71125579827365819/13100000000000000000000000000000 : ℝ)*base72 + (579577168489/655000000000000000000000000 : ℝ)*base73 + (533584178893034181/13100000000000000000000000000000 : ℝ)*base75 + (3155736533765819/13100000000000000000000000000000 : ℝ)*base78 + (30915559337065819/13100000000000000000000000000000 : ℝ)*base80 + (101819896727/81875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (32654739/10000000000000000000000 : ℝ)*base90 + (32654739/10000000000000000000000 : ℝ)*base92 + (32654739/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1279_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2199/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2199/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7331/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1279_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1279_box_0 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-963621547/5000000000 : ℝ)*x 0 + (5392541029/10000000000 : ℝ)*x 1 + (1078508311/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (963621547/5000000000 : ℝ)^4239 ≤ (2281464755487/20000000000000 : ℝ)^3215 := by
    have hnat : (963621547 : ℕ)^4239*20000000000000^3215 ≤ 2281464755487^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963621547 5000000000 2281464755487 20000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392541029/10000000000 : ℝ)^4239 ≤ (22148167628833/50000000000000 : ℝ)^3215 := by
    have hnat : (5392541029 : ℕ)^4239*50000000000000^3215 ≤ 22148167628833^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392541029 10000000000 22148167628833 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078508311/2000000000 : ℝ)^4239 ≤ (22148170477309/50000000000000 : ℝ)^3215 := by
    have hnat : (1078508311 : ℕ)^4239*50000000000000^3215 ≤ 22148170477309^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078508311 2000000000 22148170477309 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-963621547/5000000000 : ℝ), (5392541029/10000000000 : ℝ), (1078508311/2000000000 : ℝ)] ![(2281464755487/20000000000000 : ℝ), (22148167628833/50000000000000 : ℝ), (22148170477309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-963621547/5000000000 : ℝ)|^4239 ≤ (2281464755487/20000000000000 : ℝ)^3215
        have hw : |(-963621547/5000000000 : ℝ)|=(963621547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392541029/10000000000 : ℝ)|^4239 ≤ (22148167628833/50000000000000 : ℝ)^3215
        have hw : |(5392541029/10000000000 : ℝ)|=(5392541029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078508311/2000000000 : ℝ)|^4239 ≤ (22148170477309/50000000000000 : ℝ)^3215
        have hw : |(1078508311/2000000000 : ℝ)|=(1078508311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_box_1 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642063531/5000000000 : ℝ)*x 0 + (-41508643/200000000 : ℝ)*x 1 + (1078508321/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642063531/5000000000 : ℝ)^4239 ≤ (43125912176109/100000000000000 : ℝ)^3215 := by
    have hnat : (2642063531 : ℕ)^4239*100000000000000^3215 ≤ 43125912176109^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642063531 5000000000 43125912176109 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41508643/200000000 : ℝ)^4239 ≤ (12577746308219/100000000000000 : ℝ)^3215 := by
    have hnat : (41508643 : ℕ)^4239*100000000000000^3215 ≤ 12577746308219^3215*200000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41508643 200000000 12577746308219 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078508321/2000000000 : ℝ)^4239 ≤ (44296341496153/100000000000000 : ℝ)^3215 := by
    have hnat : (1078508321 : ℕ)^4239*100000000000000^3215 ≤ 44296341496153^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078508321 2000000000 44296341496153 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642063531/5000000000 : ℝ), (-41508643/200000000 : ℝ), (1078508321/2000000000 : ℝ)] ![(43125912176109/100000000000000 : ℝ), (12577746308219/100000000000000 : ℝ), (44296341496153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642063531/5000000000 : ℝ)|^4239 ≤ (43125912176109/100000000000000 : ℝ)^3215
        have hw : |(2642063531/5000000000 : ℝ)|=(2642063531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41508643/200000000 : ℝ)|^4239 ≤ (12577746308219/100000000000000 : ℝ)^3215
        have hw : |(-41508643/200000000 : ℝ)|=(41508643/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078508321/2000000000 : ℝ)|^4239 ≤ (44296341496153/100000000000000 : ℝ)^3215
        have hw : |(1078508321/2000000000 : ℝ)|=(1078508321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_box_2 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42273019/80000000 : ℝ)*x 0 + (2696270701/5000000000 : ℝ)*x 1 + (-518858001/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42273019/80000000 : ℝ)^4239 ≤ (21562957772131/50000000000000 : ℝ)^3215 := by
    have hnat : (42273019 : ℕ)^4239*50000000000000^3215 ≤ 21562957772131^3215*80000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42273019 80000000 21562957772131 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696270701/5000000000 : ℝ)^4239 ≤ (553704241219/1250000000000 : ℝ)^3215 := by
    have hnat : (2696270701 : ℕ)^4239*1250000000000^3215 ≤ 553704241219^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696270701 5000000000 553704241219 1250000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518858001/2500000000 : ℝ)^4239 ≤ (6288872570799/50000000000000 : ℝ)^3215 := by
    have hnat : (518858001 : ℕ)^4239*50000000000000^3215 ≤ 6288872570799^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518858001 2500000000 6288872570799 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42273019/80000000 : ℝ), (2696270701/5000000000 : ℝ), (-518858001/2500000000 : ℝ)] ![(21562957772131/50000000000000 : ℝ), (553704241219/1250000000000 : ℝ), (6288872570799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42273019/80000000 : ℝ)|^4239 ≤ (21562957772131/50000000000000 : ℝ)^3215
        have hw : |(42273019/80000000 : ℝ)|=(42273019/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696270701/5000000000 : ℝ)|^4239 ≤ (553704241219/1250000000000 : ℝ)^3215
        have hw : |(2696270701/5000000000 : ℝ)|=(2696270701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-518858001/2500000000 : ℝ)|^4239 ≤ (6288872570799/50000000000000 : ℝ)^3215
        have hw : |(-518858001/2500000000 : ℝ)|=(518858001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_box_3 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2246563613/5000000000 : ℝ)*x 0 + (4272527117/10000000000 : ℝ)*x 1 + (2136263541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2246563613/5000000000 : ℝ)^4239 ≤ (8706088132627/25000000000000 : ℝ)^3215 := by
    have hnat : (2246563613 : ℕ)^4239*25000000000000^3215 ≤ 8706088132627^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246563613 5000000000 8706088132627 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4272527117/10000000000 : ℝ)^4239 ≤ (1591202339/4882812500 : ℝ)^3215 := by
    have hnat : (4272527117 : ℕ)^4239*4882812500^3215 ≤ 1591202339^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4272527117 10000000000 1591202339 4882812500 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2136263541/5000000000 : ℝ)^4239 ≤ (16293911775369/50000000000000 : ℝ)^3215 := by
    have hnat : (2136263541 : ℕ)^4239*50000000000000^3215 ≤ 16293911775369^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136263541 5000000000 16293911775369 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2246563613/5000000000 : ℝ), (4272527117/10000000000 : ℝ), (2136263541/5000000000 : ℝ)] ![(8706088132627/25000000000000 : ℝ), (1591202339/4882812500 : ℝ), (16293911775369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2246563613/5000000000 : ℝ)|^4239 ≤ (8706088132627/25000000000000 : ℝ)^3215
        have hw : |(2246563613/5000000000 : ℝ)|=(2246563613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4272527117/10000000000 : ℝ)|^4239 ≤ (1591202339/4882812500 : ℝ)^3215
        have hw : |(4272527117/10000000000 : ℝ)|=(4272527117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2136263541/5000000000 : ℝ)|^4239 ≤ (16293911775369/50000000000000 : ℝ)^3215
        have hw : |(2136263541/5000000000 : ℝ)|=(2136263541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_box_4 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2274884211/10000000000 : ℝ)*x 0 + (5263336103/10000000000 : ℝ)*x 1 + (1052667133/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2274884211/10000000000 : ℝ)^4239 ≤ (3548839356249/25000000000000 : ℝ)^3215 := by
    have hnat : (2274884211 : ℕ)^4239*25000000000000^3215 ≤ 3548839356249^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274884211 10000000000 3548839356249 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263336103/10000000000 : ℝ)^4239 ≤ (10725580908341/25000000000000 : ℝ)^3215 := by
    have hnat : (5263336103 : ℕ)^4239*25000000000000^3215 ≤ 10725580908341^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263336103 10000000000 10725580908341 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052667133/2000000000 : ℝ)^4239 ≤ (670348733219/1562500000000 : ℝ)^3215 := by
    have hnat : (1052667133 : ℕ)^4239*1562500000000^3215 ≤ 670348733219^3215*2000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052667133 2000000000 670348733219 1562500000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2274884211/10000000000 : ℝ), (5263336103/10000000000 : ℝ), (1052667133/2000000000 : ℝ)] ![(3548839356249/25000000000000 : ℝ), (10725580908341/25000000000000 : ℝ), (670348733219/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2274884211/10000000000 : ℝ)|^4239 ≤ (3548839356249/25000000000000 : ℝ)^3215
        have hw : |(-2274884211/10000000000 : ℝ)|=(2274884211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263336103/10000000000 : ℝ)|^4239 ≤ (10725580908341/25000000000000 : ℝ)^3215
        have hw : |(5263336103/10000000000 : ℝ)|=(5263336103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052667133/2000000000 : ℝ)|^4239 ≤ (670348733219/1562500000000 : ℝ)^3215
        have hw : |(1052667133/2000000000 : ℝ)|=(1052667133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_box_5 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537512433/1000000000 : ℝ)*x 0 + (-2126808483/10000000000 : ℝ)*x 1 + (5263335939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537512433/1000000000 : ℝ)^4239 ≤ (44107797202613/100000000000000 : ℝ)^3215 := by
    have hnat : (537512433 : ℕ)^4239*100000000000000^3215 ≤ 44107797202613^3215*1000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537512433 1000000000 44107797202613 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126808483/10000000000 : ℝ)^4239 ≤ (6494940451453/50000000000000 : ℝ)^3215 := by
    have hnat : (2126808483 : ℕ)^4239*50000000000000^3215 ≤ 6494940451453^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126808483 10000000000 6494940451453 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263335939/10000000000 : ℝ)^4239 ≤ (8580464374159/20000000000000 : ℝ)^3215 := by
    have hnat : (5263335939 : ℕ)^4239*20000000000000^3215 ≤ 8580464374159^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263335939 10000000000 8580464374159 20000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537512433/1000000000 : ℝ), (-2126808483/10000000000 : ℝ), (5263335939/10000000000 : ℝ)] ![(44107797202613/100000000000000 : ℝ), (6494940451453/50000000000000 : ℝ), (8580464374159/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537512433/1000000000 : ℝ)|^4239 ≤ (44107797202613/100000000000000 : ℝ)^3215
        have hw : |(537512433/1000000000 : ℝ)|=(537512433/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2126808483/10000000000 : ℝ)|^4239 ≤ (6494940451453/50000000000000 : ℝ)^3215
        have hw : |(-2126808483/10000000000 : ℝ)|=(2126808483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263335939/10000000000 : ℝ)|^4239 ≤ (8580464374159/20000000000000 : ℝ)^3215
        have hw : |(5263335939/10000000000 : ℝ)|=(5263335939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_box_6 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375123871/10000000000 : ℝ)*x 0 + (2631668129/5000000000 : ℝ)*x 1 + (-1063404337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375123871/10000000000 : ℝ)^4239 ≤ (44107792236439/100000000000000 : ℝ)^3215 := by
    have hnat : (5375123871 : ℕ)^4239*100000000000000^3215 ≤ 44107792236439^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375123871 10000000000 44107792236439 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631668129/5000000000 : ℝ)^4239 ≤ (21451162649603/50000000000000 : ℝ)^3215 := by
    have hnat : (2631668129 : ℕ)^4239*50000000000000^3215 ≤ 21451162649603^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631668129 5000000000 21451162649603 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063404337/5000000000 : ℝ)^4239 ≤ (6494941220517/50000000000000 : ℝ)^3215 := by
    have hnat : (1063404337 : ℕ)^4239*50000000000000^3215 ≤ 6494941220517^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063404337 5000000000 6494941220517 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375123871/10000000000 : ℝ), (2631668129/5000000000 : ℝ), (-1063404337/5000000000 : ℝ)] ![(44107792236439/100000000000000 : ℝ), (21451162649603/50000000000000 : ℝ), (6494941220517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375123871/10000000000 : ℝ)|^4239 ≤ (44107792236439/100000000000000 : ℝ)^3215
        have hw : |(5375123871/10000000000 : ℝ)|=(5375123871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631668129/5000000000 : ℝ)|^4239 ≤ (21451162649603/50000000000000 : ℝ)^3215
        have hw : |(2631668129/5000000000 : ℝ)|=(2631668129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1063404337/5000000000 : ℝ)|^4239 ≤ (6494941220517/50000000000000 : ℝ)^3215
        have hw : |(-1063404337/5000000000 : ℝ)|=(1063404337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_box_7 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (524097761/1250000000 : ℝ)*x 0 + (4422643667/10000000000 : ℝ)*x 1 + (4422643987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524097761/1250000000 : ℝ)^4239 ≤ (15894125342539/50000000000000 : ℝ)^3215 := by
    have hnat : (524097761 : ℕ)^4239*50000000000000^3215 ≤ 15894125342539^3215*1250000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524097761 1250000000 15894125342539 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4422643667/10000000000 : ℝ)^4239 ≤ (8526468256823/25000000000000 : ℝ)^3215 := by
    have hnat : (4422643667 : ℕ)^4239*25000000000000^3215 ≤ 8526468256823^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4422643667 10000000000 8526468256823 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4422643987/10000000000 : ℝ)^4239 ≤ (2131617267563/6250000000000 : ℝ)^3215 := by
    have hnat : (4422643987 : ℕ)^4239*6250000000000^3215 ≤ 2131617267563^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4422643987 10000000000 2131617267563 6250000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524097761/1250000000 : ℝ), (4422643667/10000000000 : ℝ), (4422643987/10000000000 : ℝ)] ![(15894125342539/50000000000000 : ℝ), (8526468256823/25000000000000 : ℝ), (2131617267563/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524097761/1250000000 : ℝ)|^4239 ≤ (15894125342539/50000000000000 : ℝ)^3215
        have hw : |(524097761/1250000000 : ℝ)|=(524097761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4422643667/10000000000 : ℝ)|^4239 ≤ (8526468256823/25000000000000 : ℝ)^3215
        have hw : |(4422643667/10000000000 : ℝ)|=(4422643667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4422643987/10000000000 : ℝ)|^4239 ≤ (2131617267563/6250000000000 : ℝ)^3215
        have hw : |(4422643987/10000000000 : ℝ)|=(4422643987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_box_8 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2202061071/10000000000 : ℝ)*x 0 + (2587348119/5000000000 : ℝ)*x 1 + (5406582467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2202061071/10000000000 : ℝ)^4239 ≤ (6799639928161/50000000000000 : ℝ)^3215 := by
    have hnat : (2202061071 : ℕ)^4239*50000000000000^3215 ≤ 6799639928161^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2202061071 10000000000 6799639928161 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587348119/5000000000 : ℝ)^4239 ≤ (10488060786657/25000000000000 : ℝ)^3215 := by
    have hnat : (2587348119 : ℕ)^4239*25000000000000^3215 ≤ 10488060786657^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587348119 5000000000 10488060786657 25000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406582467/10000000000 : ℝ)^4239 ≤ (22224238487199/50000000000000 : ℝ)^3215 := by
    have hnat : (5406582467 : ℕ)^4239*50000000000000^3215 ≤ 22224238487199^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406582467 10000000000 22224238487199 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2202061071/10000000000 : ℝ), (2587348119/5000000000 : ℝ), (5406582467/10000000000 : ℝ)] ![(6799639928161/50000000000000 : ℝ), (10488060786657/25000000000000 : ℝ), (22224238487199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2202061071/10000000000 : ℝ)|^4239 ≤ (6799639928161/50000000000000 : ℝ)^3215
        have hw : |(-2202061071/10000000000 : ℝ)|=(2202061071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587348119/5000000000 : ℝ)|^4239 ≤ (10488060786657/25000000000000 : ℝ)^3215
        have hw : |(2587348119/5000000000 : ℝ)|=(2587348119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406582467/10000000000 : ℝ)|^4239 ≤ (22224238487199/50000000000000 : ℝ)^3215
        have hw : |(5406582467/10000000000 : ℝ)|=(5406582467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_box_9 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5274232483/10000000000 : ℝ)*x 0 + (-2069712293/10000000000 : ℝ)*x 1 + (540658171/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274232483/10000000000 : ℝ)^4239 ≤ (5377433704833/12500000000000 : ℝ)^3215 := by
    have hnat : (5274232483 : ℕ)^4239*12500000000000^3215 ≤ 5377433704833^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274232483 10000000000 5377433704833 12500000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069712293/10000000000 : ℝ)^4239 ≤ (6266030785657/50000000000000 : ℝ)^3215 := by
    have hnat : (2069712293 : ℕ)^4239*50000000000000^3215 ≤ 6266030785657^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069712293 10000000000 6266030785657 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540658171/1000000000 : ℝ)^4239 ≤ (1111211719219/2500000000000 : ℝ)^3215 := by
    have hnat : (540658171 : ℕ)^4239*2500000000000^3215 ≤ 1111211719219^3215*1000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540658171 1000000000 1111211719219 2500000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274232483/10000000000 : ℝ), (-2069712293/10000000000 : ℝ), (540658171/1000000000 : ℝ)] ![(5377433704833/12500000000000 : ℝ), (6266030785657/50000000000000 : ℝ), (1111211719219/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274232483/10000000000 : ℝ)|^4239 ≤ (5377433704833/12500000000000 : ℝ)^3215
        have hw : |(5274232483/10000000000 : ℝ)|=(5274232483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2069712293/10000000000 : ℝ)|^4239 ≤ (6266030785657/50000000000000 : ℝ)^3215
        have hw : |(-2069712293/10000000000 : ℝ)|=(2069712293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540658171/1000000000 : ℝ)|^4239 ≤ (1111211719219/2500000000000 : ℝ)^3215
        have hw : |(540658171/1000000000 : ℝ)|=(540658171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_box_10 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637116347/5000000000 : ℝ)*x 0 + (1351645443/2500000000 : ℝ)*x 1 + (-1034855963/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637116347/5000000000 : ℝ)^4239 ≤ (43019471907853/100000000000000 : ℝ)^3215 := by
    have hnat : (2637116347 : ℕ)^4239*100000000000000^3215 ≤ 43019471907853^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637116347 5000000000 43019471907853 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351645443/2500000000 : ℝ)^4239 ≤ (2222423472041/5000000000000 : ℝ)^3215 := by
    have hnat : (1351645443 : ℕ)^4239*5000000000000^3215 ≤ 2222423472041^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351645443 2500000000 2222423472041 5000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034855963/5000000000 : ℝ)^4239 ≤ (12532058641359/100000000000000 : ℝ)^3215 := by
    have hnat : (1034855963 : ℕ)^4239*100000000000000^3215 ≤ 12532058641359^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034855963 5000000000 12532058641359 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637116347/5000000000 : ℝ), (1351645443/2500000000 : ℝ), (-1034855963/5000000000 : ℝ)] ![(43019471907853/100000000000000 : ℝ), (2222423472041/5000000000000 : ℝ), (12532058641359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637116347/5000000000 : ℝ)|^4239 ≤ (43019471907853/100000000000000 : ℝ)^3215
        have hw : |(2637116347/5000000000 : ℝ)|=(2637116347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351645443/2500000000 : ℝ)|^4239 ≤ (2222423472041/5000000000000 : ℝ)^3215
        have hw : |(1351645443/2500000000 : ℝ)|=(1351645443/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1034855963/5000000000 : ℝ)|^4239 ≤ (12532058641359/100000000000000 : ℝ)^3215
        have hw : |(-1034855963/5000000000 : ℝ)|=(1034855963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_box_11 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4525205611/10000000000 : ℝ)*x 0 + (1064050201/2500000000 : ℝ)*x 1 + (1064049901/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4525205611/10000000000 : ℝ)^4239 ≤ (17576269992433/50000000000000 : ℝ)^3215 := by
    have hnat : (4525205611 : ℕ)^4239*50000000000000^3215 ≤ 17576269992433^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525205611 10000000000 17576269992433 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1064050201/2500000000 : ℝ)^4239 ≤ (32423736026953/100000000000000 : ℝ)^3215 := by
    have hnat : (1064050201 : ℕ)^4239*100000000000000^3215 ≤ 32423736026953^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064050201 2500000000 32423736026953 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1064049901/2500000000 : ℝ)^4239 ≤ (32423723973691/100000000000000 : ℝ)^3215 := by
    have hnat : (1064049901 : ℕ)^4239*100000000000000^3215 ≤ 32423723973691^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064049901 2500000000 32423723973691 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4525205611/10000000000 : ℝ), (1064050201/2500000000 : ℝ), (1064049901/2500000000 : ℝ)] ![(17576269992433/50000000000000 : ℝ), (32423736026953/100000000000000 : ℝ), (32423723973691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4525205611/10000000000 : ℝ)|^4239 ≤ (17576269992433/50000000000000 : ℝ)^3215
        have hw : |(4525205611/10000000000 : ℝ)|=(4525205611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1064050201/2500000000 : ℝ)|^4239 ≤ (32423736026953/100000000000000 : ℝ)^3215
        have hw : |(1064050201/2500000000 : ℝ)|=(1064050201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1064049901/2500000000 : ℝ)|^4239 ≤ (32423723973691/100000000000000 : ℝ)^3215
        have hw : |(1064049901/2500000000 : ℝ)|=(1064049901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_box_12 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2000532797/10000000000 : ℝ)*x 0 + (2739412503/5000000000 : ℝ)*x 1 + (5252327369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2000532797/10000000000 : ℝ)^4239 ≤ (11982727481997/100000000000000 : ℝ)^3215 := by
    have hnat : (2000532797 : ℕ)^4239*100000000000000^3215 ≤ 11982727481997^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000532797 10000000000 11982727481997 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2739412503/5000000000 : ℝ)^4239 ≤ (22616612182079/50000000000000 : ℝ)^3215 := by
    have hnat : (2739412503 : ℕ)^4239*50000000000000^3215 ≤ 22616612182079^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739412503 5000000000 22616612182079 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252327369/10000000000 : ℝ)^4239 ≤ (21392024069087/50000000000000 : ℝ)^3215 := by
    have hnat : (5252327369 : ℕ)^4239*50000000000000^3215 ≤ 21392024069087^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252327369 10000000000 21392024069087 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2000532797/10000000000 : ℝ), (2739412503/5000000000 : ℝ), (5252327369/10000000000 : ℝ)] ![(11982727481997/100000000000000 : ℝ), (22616612182079/50000000000000 : ℝ), (21392024069087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2000532797/10000000000 : ℝ)|^4239 ≤ (11982727481997/100000000000000 : ℝ)^3215
        have hw : |(-2000532797/10000000000 : ℝ)|=(2000532797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2739412503/5000000000 : ℝ)|^4239 ≤ (22616612182079/50000000000000 : ℝ)^3215
        have hw : |(2739412503/5000000000 : ℝ)|=(2739412503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252327369/10000000000 : ℝ)|^4239 ≤ (21392024069087/50000000000000 : ℝ)^3215
        have hw : |(5252327369/10000000000 : ℝ)|=(5252327369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_box_13 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345718617/2500000000 : ℝ)*x 0 + (-26638491/125000000 : ℝ)*x 1 + (1313081787/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345718617/2500000000 : ℝ)^4239 ≤ (44191669474781/100000000000000 : ℝ)^3215 := by
    have hnat : (1345718617 : ℕ)^4239*100000000000000^3215 ≤ 44191669474781^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345718617 2500000000 44191669474781 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26638491/125000000 : ℝ)^4239 ≤ (13024284745559/100000000000000 : ℝ)^3215 := by
    have hnat : (26638491 : ℕ)^4239*100000000000000^3215 ≤ 13024284745559^3215*125000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26638491 125000000 13024284745559 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313081787/2500000000 : ℝ)^4239 ≤ (42784045764589/100000000000000 : ℝ)^3215 := by
    have hnat : (1313081787 : ℕ)^4239*100000000000000^3215 ≤ 42784045764589^3215*2500000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313081787 2500000000 42784045764589 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345718617/2500000000 : ℝ), (-26638491/125000000 : ℝ), (1313081787/2500000000 : ℝ)] ![(44191669474781/100000000000000 : ℝ), (13024284745559/100000000000000 : ℝ), (42784045764589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345718617/2500000000 : ℝ)|^4239 ≤ (44191669474781/100000000000000 : ℝ)^3215
        have hw : |(1345718617/2500000000 : ℝ)|=(1345718617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26638491/125000000 : ℝ)|^4239 ≤ (13024284745559/100000000000000 : ℝ)^3215
        have hw : |(-26638491/125000000 : ℝ)|=(26638491/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313081787/2500000000 : ℝ)|^4239 ≤ (42784045764589/100000000000000 : ℝ)^3215
        have hw : |(1313081787/2500000000 : ℝ)|=(1313081787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_box_14 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5382874361/10000000000 : ℝ)*x 0 + (5252327471/10000000000 : ℝ)*x 1 + (-2131078993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382874361/10000000000 : ℝ)^4239 ≤ (44191668316557/100000000000000 : ℝ)^3215 := by
    have hnat : (5382874361 : ℕ)^4239*100000000000000^3215 ≤ 44191668316557^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382874361 10000000000 44191668316557 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252327471/10000000000 : ℝ)^4239 ≤ (1711361969347/4000000000000 : ℝ)^3215 := by
    have hnat : (5252327471 : ℕ)^4239*4000000000000^3215 ≤ 1711361969347^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252327471 10000000000 1711361969347 4000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2131078993/10000000000 : ℝ)^4239 ≤ (6512141216431/50000000000000 : ℝ)^3215 := by
    have hnat : (2131078993 : ℕ)^4239*50000000000000^3215 ≤ 6512141216431^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131078993 10000000000 6512141216431 50000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382874361/10000000000 : ℝ), (5252327471/10000000000 : ℝ), (-2131078993/10000000000 : ℝ)] ![(44191668316557/100000000000000 : ℝ), (1711361969347/4000000000000 : ℝ), (6512141216431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382874361/10000000000 : ℝ)|^4239 ≤ (44191668316557/100000000000000 : ℝ)^3215
        have hw : |(5382874361/10000000000 : ℝ)|=(5382874361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252327471/10000000000 : ℝ)|^4239 ≤ (1711361969347/4000000000000 : ℝ)^3215
        have hw : |(5252327471/10000000000 : ℝ)|=(5252327471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2131078993/10000000000 : ℝ)|^4239 ≤ (6512141216431/50000000000000 : ℝ)^3215
        have hw : |(-2131078993/10000000000 : ℝ)|=(2131078993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1279_box_15 (p : ℝ) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4166745621/10000000000 : ℝ)*x 0 + (4435424489/10000000000 : ℝ)*x 1 + (2217711827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4166745621/10000000000 : ℝ)^4239 ≤ (31528235615293/100000000000000 : ℝ)^3215 := by
    have hnat : (4166745621 : ℕ)^4239*100000000000000^3215 ≤ 31528235615293^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166745621 10000000000 31528235615293 100000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4435424489/10000000000 : ℝ)^4239 ≤ (1069871451091/3125000000000 : ℝ)^3215 := by
    have hnat : (4435424489 : ℕ)^4239*3125000000000^3215 ≤ 1069871451091^3215*10000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4435424489 10000000000 1069871451091 3125000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2217711827/5000000000 : ℝ)^4239 ≤ (1711793896847/5000000000000 : ℝ)^3215 := by
    have hnat : (2217711827 : ℕ)^4239*5000000000000^3215 ≤ 1711793896847^3215*5000000000^4239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217711827 5000000000 1711793896847 5000000000000 4239 3215 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4239/1024 : ℝ)) 4239 3215 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4166745621/10000000000 : ℝ), (4435424489/10000000000 : ℝ), (2217711827/5000000000 : ℝ)] ![(31528235615293/100000000000000 : ℝ), (1069871451091/3125000000000 : ℝ), (1711793896847/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4166745621/10000000000 : ℝ)|^4239 ≤ (31528235615293/100000000000000 : ℝ)^3215
        have hw : |(4166745621/10000000000 : ℝ)|=(4166745621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4435424489/10000000000 : ℝ)|^4239 ≤ (1069871451091/3125000000000 : ℝ)^3215
        have hw : |(4435424489/10000000000 : ℝ)|=(4435424489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2217711827/5000000000 : ℝ)|^4239 ≤ (1711793896847/5000000000000 : ℝ)^3215
        have hw : |(2217711827/5000000000 : ℝ)|=(2217711827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1279_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7331/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2199/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15709/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58821/100000 : ℝ) ∧ (79577/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84103/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7331/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2199/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7331/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2199/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7331/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2199/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7331/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2199/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7331/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2199/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7331/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2199/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2199/20000 : ℝ) ^ (2119/512 : ℝ) ≤ (10760233112095753/100000000000000000000 : ℝ) := by
    have hpowers : (2199/20000 : ℝ)^2119 ≤ (10760233112095753/100000000000000000000 : ℝ)^512 := by
      have hnat : (2199 : ℕ)^2119*100000000000000000000^512 ≤ 10760233112095753^512*20000^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2199 20000 10760233112095753 100000000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2199/20000 : ℝ)) (X := (10760233112095753/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7331/50000 : ℝ) ^ (2119/512 : ℝ) ≤ (1416469742062613/4000000000000000000 : ℝ) := by
    have hpowers : (7331/50000 : ℝ)^2119 ≤ (1416469742062613/4000000000000000000 : ℝ)^512 := by
      have hnat : (7331 : ℕ)^2119*4000000000000000000^512 ≤ 1416469742062613^512*50000^2119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7331 50000 1416469742062613 4000000000000000000 2119 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7331/50000 : ℝ)) (X := (1416469742062613/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010760233112095753/50000000000000000000 : ℝ) ≤ (1000051994241049/1000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (50010760233112095753/50000000000000000000 : ℝ)^512 ≤ (1000051994241049/1000000000000000 : ℝ)^2119 := by
      have hnat : (50010760233112095753 : ℕ)^512*1000000000000000^2119 ≤ 1000051994241049^2119*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010760233112095753 50000000000000000000 1000051994241049 1000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000051994241049/1000000000000000 : ℝ)) (X := (50010760233112095753/50000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023085988331830539/50000000000000000000 : ℝ) ≤ (10001115427763153/10000000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (50023085988331830539/50000000000000000000 : ℝ)^512 ≤ (10001115427763153/10000000000000000 : ℝ)^2119 := by
      have hnat : (50023085988331830539 : ℕ)^512*10000000000000000^2119 ≤ 10001115427763153^2119*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023085988331830539 50000000000000000000 10001115427763153 10000000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001115427763153/10000000000000000 : ℝ)) (X := (50023085988331830539/50000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001416469742062613/2000000000000000000 : ℝ) ≤ (1250213864139477/1250000000000000 : ℝ) ^ (2119/512 : ℝ) := by
    have hpowers : (2001416469742062613/2000000000000000000 : ℝ)^512 ≤ (1250213864139477/1250000000000000 : ℝ)^2119 := by
      have hnat : (2001416469742062613 : ℕ)^512*1250000000000000^2119 ≤ 1250213864139477^2119*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001416469742062613 2000000000000000000 1250213864139477 1250000000000000 512 2119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250213864139477/1250000000000000 : ℝ)) (X := (2001416469742062613/2000000000000000000 : ℝ)) (by norm_num) 2119 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10760233112095753/100000000000000000000 : ℝ) ≤ ((1832940595295710373/1833500000000000000 : ℝ)+2*(595485352663/366700000000000 : ℝ)*(2199/20000 : ℝ))^(2119/512 : ℝ) := by
    rw [show (1832940595295710373/1833500000000000000 : ℝ)+2*(595485352663/366700000000000 : ℝ)*(2199/20000 : ℝ)=(1000051994241049/1000000000000000 : ℝ) by norm_num, show 1+2*(10760233112095753/100000000000000000000 : ℝ)=(50010760233112095753/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1416469742062613/4000000000000000000 : ℝ)+(10760233112095753/100000000000000000000 : ℝ) ≤ ((1832940595295710373/1833500000000000000 : ℝ)+(595485352663/366700000000000 : ℝ)*((7331/50000 : ℝ)+(2199/20000 : ℝ)))^(2119/512 : ℝ) := by
    rw [show (1832940595295710373/1833500000000000000 : ℝ)+(595485352663/366700000000000 : ℝ)*((7331/50000 : ℝ)+(2199/20000 : ℝ))=(10001115427763153/10000000000000000 : ℝ) by norm_num, show 1+(1416469742062613/4000000000000000000 : ℝ)+(10760233112095753/100000000000000000000 : ℝ)=(50023085988331830539/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1416469742062613/4000000000000000000 : ℝ) ≤ ((1832940595295710373/1833500000000000000 : ℝ)+2*(595485352663/366700000000000 : ℝ)*(7331/50000 : ℝ))^(2119/512 : ℝ) := by
    rw [show (1832940595295710373/1833500000000000000 : ℝ)+2*(595485352663/366700000000000 : ℝ)*(7331/50000 : ℝ)=(1250213864139477/1250000000000000 : ℝ) by norm_num, show 1+2*(1416469742062613/4000000000000000000 : ℝ)=(2001416469742062613/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1832940595295710373/1833500000000000000 : ℝ)*(X 1 0+X 2 0)+(595485352663/366700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (2199/20000 : ℝ)) (hi := (7331/50000 : ℝ)) (c := (1832940595295710373/1833500000000000000 : ℝ)) (alpha := (595485352663/366700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1832940595295710373/1833500000000000000 : ℝ)*(X 0 1+X 2 1)+(595485352663/366700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (2199/20000 : ℝ)) (hi := (7331/50000 : ℝ)) (c := (1832940595295710373/1833500000000000000 : ℝ)) (alpha := (595485352663/366700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1832940595295710373/1833500000000000000 : ℝ)*(X 0 2+X 1 2)+(595485352663/366700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2119/512 : ℝ)) (lo := (2199/20000 : ℝ)) (hi := (7331/50000 : ℝ)) (c := (1832940595295710373/1833500000000000000 : ℝ)) (alpha := (595485352663/366700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-963621547/5000000000 : ℝ)*X 0 0+(5392541029/10000000000 : ℝ)*X 0 1+(1078508311/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642063531/5000000000 : ℝ)*X 1 0+(-41508643/200000000 : ℝ)*X 1 1+(1078508321/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42273019/80000000 : ℝ)*X 2 0+(2696270701/5000000000 : ℝ)*X 2 1+(-518858001/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2246563613/5000000000 : ℝ)*X 0 0+(4272527117/10000000000 : ℝ)*X 0 1+(2136263541/5000000000 : ℝ)*X 0 2+(2246563613/5000000000 : ℝ)*X 1 0+(4272527117/10000000000 : ℝ)*X 1 1+(2136263541/5000000000 : ℝ)*X 1 2+(2246563613/5000000000 : ℝ)*X 2 0+(4272527117/10000000000 : ℝ)*X 2 1+(2136263541/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2274884211/10000000000 : ℝ)*X 0 0+(5263336103/10000000000 : ℝ)*X 0 1+(1052667133/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((537512433/1000000000 : ℝ)*X 1 0+(-2126808483/10000000000 : ℝ)*X 1 1+(5263335939/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5375123871/10000000000 : ℝ)*X 2 0+(2631668129/5000000000 : ℝ)*X 2 1+(-1063404337/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((524097761/1250000000 : ℝ)*X 0 0+(4422643667/10000000000 : ℝ)*X 0 1+(4422643987/10000000000 : ℝ)*X 0 2+(524097761/1250000000 : ℝ)*X 1 0+(4422643667/10000000000 : ℝ)*X 1 1+(4422643987/10000000000 : ℝ)*X 1 2+(524097761/1250000000 : ℝ)*X 2 0+(4422643667/10000000000 : ℝ)*X 2 1+(4422643987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2202061071/10000000000 : ℝ)*X 0 0+(2587348119/5000000000 : ℝ)*X 0 1+(5406582467/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5274232483/10000000000 : ℝ)*X 1 0+(-2069712293/10000000000 : ℝ)*X 1 1+(540658171/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2637116347/5000000000 : ℝ)*X 2 0+(1351645443/2500000000 : ℝ)*X 2 1+(-1034855963/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4525205611/10000000000 : ℝ)*X 0 0+(1064050201/2500000000 : ℝ)*X 0 1+(1064049901/2500000000 : ℝ)*X 0 2+(4525205611/10000000000 : ℝ)*X 1 0+(1064050201/2500000000 : ℝ)*X 1 1+(1064049901/2500000000 : ℝ)*X 1 2+(4525205611/10000000000 : ℝ)*X 2 0+(1064050201/2500000000 : ℝ)*X 2 1+(1064049901/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2000532797/10000000000 : ℝ)*X 0 0+(2739412503/5000000000 : ℝ)*X 0 1+(5252327369/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1345718617/2500000000 : ℝ)*X 1 0+(-26638491/125000000 : ℝ)*X 1 1+(1313081787/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5382874361/10000000000 : ℝ)*X 2 0+(5252327471/10000000000 : ℝ)*X 2 1+(-2131078993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4166745621/10000000000 : ℝ)*X 0 0+(4435424489/10000000000 : ℝ)*X 0 1+(2217711827/5000000000 : ℝ)*X 0 2+(4166745621/10000000000 : ℝ)*X 1 0+(4435424489/10000000000 : ℝ)*X 1 1+(2217711827/5000000000 : ℝ)*X 1 2+(4166745621/10000000000 : ℝ)*X 2 0+(4435424489/10000000000 : ℝ)*X 2 1+(2217711827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1279_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15709/25000 : ℝ) ≤ (-1152055352475547721049432443091/1833500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26980083/100000000000000 : ℝ)*(upper0) + (8265879/12500000000000 : ℝ)*(upper3) + (130284313/100000000000000 : ℝ)*(lower4) + (56986930050411/2000000000000 : ℝ)*(major0) + (56986930050411/2000000000000 : ℝ)*(major1) + (56986930050411/2000000000000 : ℝ)*(major2) + (1813150921/100000000000000 : ℝ)*(sp3) + (192408247727529/5000000000000 : ℝ)*(sp4) + (3848140432354201/100000000000000 : ℝ)*(sp5) + (3848080635356211/100000000000000 : ℝ)*(sp6) + (93573499789009/5000000000000 : ℝ)*(sp7) + (798462887/100000000000000 : ℝ)*(sp8) + (12660329633/50000000000000 : ℝ)*(sp13) + (10639707157/12500000000000 : ℝ)*(sp14) + (1871471808931101/100000000000000 : ℝ)*(f.failure) + (3848165753013467/100000000000000 : ℝ)*(f.sum) + (9387354096387/3667000000000000000000000000 : ℝ)*base65 + (4951241035857303/3667000000000000000000000000000 : ℝ)*base67 + (29595582274958697/3667000000000000000000000000000 : ℝ)*base70 + (7424400437189697/3667000000000000000000000000000 : ℝ)*base72 + (2468471333157/229187500000000000000000000 : ℝ)*base73 + (12748083142684697/3667000000000000000000000000000 : ℝ)*base76 + (2878419708017303/3667000000000000000000000000000 : ℝ)*base77 + (15429831903198697/3667000000000000000000000000000 : ℝ)*base80 + (809945461599/366700000000000000000000000 : ℝ)*base82 + (34675461/10000000000000000000000 : ℝ)*base90 + (34675461/10000000000000000000000 : ℝ)*base92 + (34675461/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58821/100000 : ℝ) ≤ (2696300664434051435399325755283/4583750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33517/125000000000 : ℝ)*(lower3) + (43236439/50000000000000 : ℝ)*(upper4) + (43426161/100000000000000 : ℝ)*(upper5) + (291594729227693/10000000000000 : ℝ)*(major0) + (291594729227693/10000000000000 : ℝ)*(major1) + (291594729227693/10000000000000 : ℝ)*(major2) + (155882661058811/4000000000000 : ℝ)*(sp0) + (3897062544193571/100000000000000 : ℝ)*(sp1) + (194853322298409/5000000000000 : ℝ)*(sp2) + (1915214304965597/100000000000000 : ℝ)*(sp3) + (433219543/5000000000000 : ℝ)*(sp5) + (4762616251/100000000000000 : ℝ)*(sp6) + (6970711/500000000000 : ℝ)*(sp7) + (1170528539/25000000000000 : ℝ)*(sp12) + (1915215699107797/100000000000000 : ℝ)*(f.failure) + (3897071208584431/100000000000000 : ℝ)*(f.sum) + (8175802781069/1833500000000000000000000000 : ℝ)*base65 + (198151713582654489/18335000000000000000000000000000 : ℝ)*base67 + (16276540144650511/18335000000000000000000000000000 : ℝ)*base70 + (130784146141714489/18335000000000000000000000000000 : ℝ)*base71 + (2169098313231/733400000000000000000000000 : ℝ)*base74 + (93344284702339489/18335000000000000000000000000000 : ℝ)*base75 + (98213615271849489/18335000000000000000000000000000 : ℝ)*base77 + (159150982922309489/18335000000000000000000000000000 : ℝ)*base79 + (2684023439451/1833500000000000000000000000 : ℝ)*base82 + (69070717/10000000000000000000000 : ℝ)*base90 + (69070717/10000000000000000000000 : ℝ)*base92 + (69070717/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79577/100000 : ℝ) ≤ (14590971401618118891700262469/18335000000000000000000000000 : ℝ) := by norm_num
    linear_combination (156954647/100000000000000 : ℝ)*(upper1) + (49768157/25000000000000 : ℝ)*(upper4) + (231601/12500000000000 : ℝ)*(lower5) + (1615185486905847/50000000000000 : ℝ)*(major0) + (1615185486905847/50000000000000 : ℝ)*(major1) + (1615185486905847/50000000000000 : ℝ)*(major2) + (2248760231/100000000000000 : ℝ)*(sp1) + (111478351891/100000000000000 : ℝ)*(sp2) + (26601823429/25000000000000 : ℝ)*(sp3) + (3013289987/25000000000000 : ℝ)*(sp4) + (4312471773708289/100000000000000 : ℝ)*(sp8) + (2156240789054003/50000000000000 : ℝ)*(sp9) + (2156186174258173/50000000000000 : ℝ)*(sp10) + (84865003442439/4000000000000 : ℝ)*(sp11) + (2121731493354691/100000000000000 : ℝ)*(f.failure) + (1078120956717059/25000000000000 : ℝ)*(f.sum) + (20008235577783/4583750000000000000000000000 : ℝ)*base65 + (193845417250905931/91675000000000000000000000000000 : ℝ)*base67 + (254641966181569069/91675000000000000000000000000000 : ℝ)*base70 + (262818692870380931/91675000000000000000000000000000 : ℝ)*base71 + (49126836820341/9167500000000000000000000000 : ℝ)*base73 + (240264267170169069/91675000000000000000000000000000 : ℝ)*base76 + (72253684361805931/91675000000000000000000000000000 : ℝ)*base77 + (404830549122994069/91675000000000000000000000000000 : ℝ)*base80 + (3612254096649/9167500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (86911451/10000000000000000000000 : ℝ)*base90 + (86911451/10000000000000000000000 : ℝ)*base92 + (86911451/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-84103/100000 : ℝ) ≤ (-3854946414809674398405385705881/4583750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (142213693/100000000000000 : ℝ)*(lower0) + (2323451/20000000000000 : ℝ)*(lower1) + (18926899/20000000000000 : ℝ)*(lower2) + (163306074124249/5000000000000 : ℝ)*(major0) + (163306074124249/5000000000000 : ℝ)*(major1) + (163306074124249/5000000000000 : ℝ)*(major2) + (14968354553/100000000000000 : ℝ)*(sp0) + (36228742997/12500000000000 : ℝ)*(sp5) + (106762966183/100000000000000 : ℝ)*(sp6) + (25044909801/50000000000000 : ℝ)*(sp7) + (4415048730784369/100000000000000 : ℝ)*(sp12) + (2207386934597473/50000000000000 : ℝ)*(sp13) + (220747846808637/5000000000000 : ℝ)*(sp14) + (214516260144409/10000000000000 : ℝ)*(sp15) + (2145212691263691/100000000000000 : ℝ)*(f.failure) + (2207531849569461/50000000000000 : ℝ)*(f.sum) + (2352464012751/3667000000000000000000000000 : ℝ)*base65 + (5492954147592623/9167500000000000000000000000000 : ℝ)*base68 + (50397476784644877/9167500000000000000000000000000 : ℝ)*base69 + (93551552689174877/9167500000000000000000000000000 : ℝ)*base71 + (15974486727351/916750000000000000000000000 : ℝ)*base74 + (33387158569314877/9167500000000000000000000000000 : ℝ)*base75 + (92180106377737377/9167500000000000000000000000000 : ℝ)*base77 + (390276008356345123/9167500000000000000000000000000 : ℝ)*base80 + (1125889375569/916750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (64060451/10000000000000000000000 : ℝ)*base90 + (64060451/10000000000000000000000 : ℝ)*base92 + (64060451/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1279_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7331/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2199/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15709/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58821/100000 : ℝ) else (79577/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84103/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1279_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1279_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2199/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15709/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58821/100000 : ℝ) else (79577/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84103/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1279_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1279_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2119/512 : ℝ) ≤ p) (hpb : p ≤ (4239/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152251639/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2199/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15709/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58821/100000 : ℝ) else (79577/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84103/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1279_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

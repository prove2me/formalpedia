-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_w1008_box
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T12:57:14.290056+00:00
-- url     : https://prove2.me/submissions/732bd1c0-b6b5-47c6-b1c7-8ce28f729714

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
theorem support_rectangle_w1008_box_0 (p : ℝ) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-16809227/80000000 : ℝ)*x 0 + (1344534001/2500000000 : ℝ)*x 1 + (5378135369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16809227/80000000 : ℝ)^8201 ≤ (12500882913443/100000000000000 : ℝ)^6153 := by
    have hnat : (16809227 : ℕ)^8201*100000000000000^6153 ≤ 12500882913443^6153*80000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16809227 80000000 12500882913443 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344534001/2500000000 : ℝ)^8201 ≤ (43749561977151/100000000000000 : ℝ)^6153 := by
    have hnat : (1344534001 : ℕ)^8201*100000000000000^6153 ≤ 43749561977151^6153*2500000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344534001 2500000000 43749561977151 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5378135369/10000000000 : ℝ)^8201 ≤ (10937388773071/25000000000000 : ℝ)^6153 := by
    have hnat : (5378135369 : ℕ)^8201*25000000000000^6153 ≤ 10937388773071^6153*10000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378135369 10000000000 10937388773071 25000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8201/2048 : ℝ)) 8201 6153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16809227/80000000 : ℝ), (1344534001/2500000000 : ℝ), (5378135369/10000000000 : ℝ)] ![(12500882913443/100000000000000 : ℝ), (43749561977151/100000000000000 : ℝ), (10937388773071/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16809227/80000000 : ℝ)|^8201 ≤ (12500882913443/100000000000000 : ℝ)^6153
        have hw : |(-16809227/80000000 : ℝ)|=(16809227/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344534001/2500000000 : ℝ)|^8201 ≤ (43749561977151/100000000000000 : ℝ)^6153
        have hw : |(1344534001/2500000000 : ℝ)|=(1344534001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5378135369/10000000000 : ℝ)|^8201 ≤ (10937388773071/25000000000000 : ℝ)^6153
        have hw : |(5378135369/10000000000 : ℝ)|=(5378135369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1008_box_1 (p : ℝ) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1058900693/2000000000 : ℝ)*x 0 + (-1107102519/5000000000 : ℝ)*x 1 + (5378135681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058900693/2000000000 : ℝ)^8201 ≤ (42845146899729/100000000000000 : ℝ)^6153 := by
    have hnat : (1058900693 : ℕ)^8201*100000000000000^6153 ≤ 42845146899729^6153*2000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058900693 2000000000 42845146899729 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1107102519/5000000000 : ℝ)^8201 ≤ (13405294610349/100000000000000 : ℝ)^6153 := by
    have hnat : (1107102519 : ℕ)^8201*100000000000000^6153 ≤ 13405294610349^6153*5000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107102519 5000000000 13405294610349 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5378135681/10000000000 : ℝ)^8201 ≤ (8749911695017/20000000000000 : ℝ)^6153 := by
    have hnat : (5378135681 : ℕ)^8201*20000000000000^6153 ≤ 8749911695017^6153*10000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378135681 10000000000 8749911695017 20000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8201/2048 : ℝ)) 8201 6153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058900693/2000000000 : ℝ), (-1107102519/5000000000 : ℝ), (5378135681/10000000000 : ℝ)] ![(42845146899729/100000000000000 : ℝ), (13405294610349/100000000000000 : ℝ), (8749911695017/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058900693/2000000000 : ℝ)|^8201 ≤ (42845146899729/100000000000000 : ℝ)^6153
        have hw : |(1058900693/2000000000 : ℝ)|=(1058900693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1107102519/5000000000 : ℝ)|^8201 ≤ (13405294610349/100000000000000 : ℝ)^6153
        have hw : |(-1107102519/5000000000 : ℝ)|=(1107102519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5378135681/10000000000 : ℝ)|^8201 ≤ (8749911695017/20000000000000 : ℝ)^6153
        have hw : |(5378135681/10000000000 : ℝ)|=(5378135681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1008_box_2 (p : ℝ) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2647251679/5000000000 : ℝ)*x 0 + (5378135717/10000000000 : ℝ)*x 1 + (-2214205133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647251679/5000000000 : ℝ)^8201 ≤ (21422572872819/50000000000000 : ℝ)^6153 := by
    have hnat : (2647251679 : ℕ)^8201*50000000000000^6153 ≤ 21422572872819^6153*5000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647251679 5000000000 21422572872819 50000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5378135717/10000000000 : ℝ)^8201 ≤ (85448357159/195312500000 : ℝ)^6153 := by
    have hnat : (5378135717 : ℕ)^8201*195312500000^6153 ≤ 85448357159^6153*10000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378135717 10000000000 85448357159 195312500000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2214205133/10000000000 : ℝ)^8201 ≤ (13405295376937/100000000000000 : ℝ)^6153 := by
    have hnat : (2214205133 : ℕ)^8201*100000000000000^6153 ≤ 13405295376937^6153*10000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214205133 10000000000 13405295376937 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8201/2048 : ℝ)) 8201 6153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647251679/5000000000 : ℝ), (5378135717/10000000000 : ℝ), (-2214205133/10000000000 : ℝ)] ![(21422572872819/50000000000000 : ℝ), (85448357159/195312500000 : ℝ), (13405295376937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647251679/5000000000 : ℝ)|^8201 ≤ (21422572872819/50000000000000 : ℝ)^6153
        have hw : |(2647251679/5000000000 : ℝ)|=(2647251679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5378135717/10000000000 : ℝ)|^8201 ≤ (85448357159/195312500000 : ℝ)^6153
        have hw : |(5378135717/10000000000 : ℝ)|=(5378135717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2214205133/10000000000 : ℝ)|^8201 ≤ (13405295376937/100000000000000 : ℝ)^6153
        have hw : |(-2214205133/10000000000 : ℝ)|=(2214205133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1008_box_3 (p : ℝ) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4492969373/10000000000 : ℝ)*x 0 + (4331573233/10000000000 : ℝ)*x 1 + (4331574073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4492969373/10000000000 : ℝ)^8201 ≤ (17212767204027/50000000000000 : ℝ)^6153 := by
    have hnat : (4492969373 : ℕ)^8201*50000000000000^6153 ≤ 17212767204027^6153*10000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492969373 10000000000 17212767204027 50000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4331573233/10000000000 : ℝ)^8201 ≤ (4098403568757/12500000000000 : ℝ)^6153 := by
    have hnat : (4331573233 : ℕ)^8201*12500000000000^6153 ≤ 4098403568757^6153*10000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331573233 10000000000 4098403568757 12500000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4331574073/10000000000 : ℝ)^8201 ≤ (32787237024637/100000000000000 : ℝ)^6153 := by
    have hnat : (4331574073 : ℕ)^8201*100000000000000^6153 ≤ 32787237024637^6153*10000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331574073 10000000000 32787237024637 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8201/2048 : ℝ)) 8201 6153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4492969373/10000000000 : ℝ), (4331573233/10000000000 : ℝ), (4331574073/10000000000 : ℝ)] ![(17212767204027/50000000000000 : ℝ), (4098403568757/12500000000000 : ℝ), (32787237024637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4492969373/10000000000 : ℝ)|^8201 ≤ (17212767204027/50000000000000 : ℝ)^6153
        have hw : |(4492969373/10000000000 : ℝ)|=(4492969373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4331573233/10000000000 : ℝ)|^8201 ≤ (4098403568757/12500000000000 : ℝ)^6153
        have hw : |(4331573233/10000000000 : ℝ)|=(4331573233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4331574073/10000000000 : ℝ)|^8201 ≤ (32787237024637/100000000000000 : ℝ)^6153
        have hw : |(4331574073/10000000000 : ℝ)|=(4331574073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1008_box_4 (p : ℝ) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-473108729/2000000000 : ℝ)*x 0 + (1319794043/2500000000 : ℝ)*x 1 + (1055835233/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (473108729/2000000000 : ℝ)^8201 ≤ (3660046022677/25000000000000 : ℝ)^6153 := by
    have hnat : (473108729 : ℕ)^8201*25000000000000^6153 ≤ 3660046022677^6153*2000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473108729 2000000000 3660046022677 25000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1319794043/2500000000 : ℝ)^8201 ≤ (10669976996263/25000000000000 : ℝ)^6153 := by
    have hnat : (1319794043 : ℕ)^8201*25000000000000^6153 ≤ 10669976996263^6153*2500000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319794043 2500000000 10669976996263 25000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055835233/2000000000 : ℝ)^8201 ≤ (42679907909623/100000000000000 : ℝ)^6153 := by
    have hnat : (1055835233 : ℕ)^8201*100000000000000^6153 ≤ 42679907909623^6153*2000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055835233 2000000000 42679907909623 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8201/2048 : ℝ)) 8201 6153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-473108729/2000000000 : ℝ), (1319794043/2500000000 : ℝ), (1055835233/2000000000 : ℝ)] ![(3660046022677/25000000000000 : ℝ), (10669976996263/25000000000000 : ℝ), (42679907909623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-473108729/2000000000 : ℝ)|^8201 ≤ (3660046022677/25000000000000 : ℝ)^6153
        have hw : |(-473108729/2000000000 : ℝ)|=(473108729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1319794043/2500000000 : ℝ)|^8201 ≤ (10669976996263/25000000000000 : ℝ)^6153
        have hw : |(1319794043/2500000000 : ℝ)|=(1319794043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055835233/2000000000 : ℝ)|^8201 ≤ (42679907909623/100000000000000 : ℝ)^6153
        have hw : |(1055835233/2000000000 : ℝ)|=(1055835233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1008_box_5 (p : ℝ) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2682316379/5000000000 : ℝ)*x 0 + (-70397089/312500000 : ℝ)*x 1 + (1055835243/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682316379/5000000000 : ℝ)^8201 ≤ (43603216806267/100000000000000 : ℝ)^6153 := by
    have hnat : (2682316379 : ℕ)^8201*100000000000000^6153 ≤ 43603216806267^6153*5000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682316379 5000000000 43603216806267 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70397089/312500000 : ℝ)^8201 ≤ (6858437361387/50000000000000 : ℝ)^6153 := by
    have hnat : (70397089 : ℕ)^8201*50000000000000^6153 ≤ 6858437361387^6153*312500000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70397089 312500000 6858437361387 50000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055835243/2000000000 : ℝ)^8201 ≤ (21339954224199/50000000000000 : ℝ)^6153 := by
    have hnat : (1055835243 : ℕ)^8201*50000000000000^6153 ≤ 21339954224199^6153*2000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055835243 2000000000 21339954224199 50000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8201/2048 : ℝ)) 8201 6153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682316379/5000000000 : ℝ), (-70397089/312500000 : ℝ), (1055835243/2000000000 : ℝ)] ![(43603216806267/100000000000000 : ℝ), (6858437361387/50000000000000 : ℝ), (21339954224199/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682316379/5000000000 : ℝ)|^8201 ≤ (43603216806267/100000000000000 : ℝ)^6153
        have hw : |(2682316379/5000000000 : ℝ)|=(2682316379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-70397089/312500000 : ℝ)|^8201 ≤ (6858437361387/50000000000000 : ℝ)^6153
        have hw : |(-70397089/312500000 : ℝ)|=(70397089/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055835243/2000000000 : ℝ)|^8201 ≤ (21339954224199/50000000000000 : ℝ)^6153
        have hw : |(1055835243/2000000000 : ℝ)|=(1055835243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1008_box_6 (p : ℝ) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5364632801/10000000000 : ℝ)*x 0 + (1055835239/2000000000 : ℝ)*x 1 + (-1126353409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364632801/10000000000 : ℝ)^8201 ≤ (1362600539753/3125000000000 : ℝ)^6153 := by
    have hnat : (5364632801 : ℕ)^8201*3125000000000^6153 ≤ 1362600539753^6153*10000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364632801 10000000000 1362600539753 3125000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055835239/2000000000 : ℝ)^8201 ≤ (5334988529111/12500000000000 : ℝ)^6153 := by
    have hnat : (1055835239 : ℕ)^8201*12500000000000^6153 ≤ 5334988529111^6153*2000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055835239 2000000000 5334988529111 12500000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126353409/5000000000 : ℝ)^8201 ≤ (137168744793/1000000000000 : ℝ)^6153 := by
    have hnat : (1126353409 : ℕ)^8201*1000000000000^6153 ≤ 137168744793^6153*5000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126353409 5000000000 137168744793 1000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8201/2048 : ℝ)) 8201 6153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364632801/10000000000 : ℝ), (1055835239/2000000000 : ℝ), (-1126353409/5000000000 : ℝ)] ![(1362600539753/3125000000000 : ℝ), (5334988529111/12500000000000 : ℝ), (137168744793/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364632801/10000000000 : ℝ)|^8201 ≤ (1362600539753/3125000000000 : ℝ)^6153
        have hw : |(5364632801/10000000000 : ℝ)|=(5364632801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055835239/2000000000 : ℝ)|^8201 ≤ (5334988529111/12500000000000 : ℝ)^6153
        have hw : |(1055835239/2000000000 : ℝ)|=(1055835239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1126353409/5000000000 : ℝ)|^8201 ≤ (137168744793/1000000000000 : ℝ)^6153
        have hw : |(-1126353409/5000000000 : ℝ)|=(1126353409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1008_box_7 (p : ℝ) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068632631/2500000000 : ℝ)*x 0 + (55509639/125000000 : ℝ)*x 1 + (4440771107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068632631/2500000000 : ℝ)^8201 ≤ (32213001801633/100000000000000 : ℝ)^6153 := by
    have hnat : (1068632631 : ℕ)^8201*100000000000000^6153 ≤ 32213001801633^6153*2500000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068632631 2500000000 32213001801633 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55509639/125000000 : ℝ)^8201 ≤ (33893499156473/100000000000000 : ℝ)^6153 := by
    have hnat : (55509639 : ℕ)^8201*100000000000000^6153 ≤ 33893499156473^6153*125000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55509639 125000000 33893499156473 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4440771107/10000000000 : ℝ)^8201 ≤ (33893499024227/100000000000000 : ℝ)^6153 := by
    have hnat : (4440771107 : ℕ)^8201*100000000000000^6153 ≤ 33893499024227^6153*10000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4440771107 10000000000 33893499024227 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8201/2048 : ℝ)) 8201 6153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068632631/2500000000 : ℝ), (55509639/125000000 : ℝ), (4440771107/10000000000 : ℝ)] ![(32213001801633/100000000000000 : ℝ), (33893499156473/100000000000000 : ℝ), (33893499024227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068632631/2500000000 : ℝ)|^8201 ≤ (32213001801633/100000000000000 : ℝ)^6153
        have hw : |(1068632631/2500000000 : ℝ)|=(1068632631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(55509639/125000000 : ℝ)|^8201 ≤ (33893499156473/100000000000000 : ℝ)^6153
        have hw : |(55509639/125000000 : ℝ)|=(55509639/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4440771107/10000000000 : ℝ)|^8201 ≤ (33893499024227/100000000000000 : ℝ)^6153
        have hw : |(4440771107/10000000000 : ℝ)|=(4440771107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1008_box_8 (p : ℝ) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2310425773/10000000000 : ℝ)*x 0 + (5212143331/10000000000 : ℝ)*x 1 + (1077545341/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2310425773/10000000000 : ℝ)^8201 ≤ (177341189237/1250000000000 : ℝ)^6153 := by
    have hnat : (2310425773 : ℕ)^8201*1250000000000^6153 ≤ 177341189237^6153*10000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2310425773 10000000000 177341189237 1250000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5212143331/10000000000 : ℝ)^8201 ≤ (8391825333211/20000000000000 : ℝ)^6153 := by
    have hnat : (5212143331 : ℕ)^8201*20000000000000^6153 ≤ 8391825333211^6153*10000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212143331 10000000000 8391825333211 20000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077545341/2000000000 : ℝ)^8201 ≤ (21926789090027/50000000000000 : ℝ)^6153 := by
    have hnat : (1077545341 : ℕ)^8201*50000000000000^6153 ≤ 21926789090027^6153*2000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077545341 2000000000 21926789090027 50000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8201/2048 : ℝ)) 8201 6153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2310425773/10000000000 : ℝ), (5212143331/10000000000 : ℝ), (1077545341/2000000000 : ℝ)] ![(177341189237/1250000000000 : ℝ), (8391825333211/20000000000000 : ℝ), (21926789090027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2310425773/10000000000 : ℝ)|^8201 ≤ (177341189237/1250000000000 : ℝ)^6153
        have hw : |(-2310425773/10000000000 : ℝ)|=(2310425773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5212143331/10000000000 : ℝ)|^8201 ≤ (8391825333211/20000000000000 : ℝ)^6153
        have hw : |(5212143331/10000000000 : ℝ)|=(5212143331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077545341/2000000000 : ℝ)|^8201 ≤ (21926789090027/50000000000000 : ℝ)^6153
        have hw : |(1077545341/2000000000 : ℝ)|=(1077545341/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1008_box_9 (p : ℝ) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2643851/5000000 : ℝ)*x 0 + (-1105201059/5000000000 : ℝ)*x 1 + (1077545393/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643851/5000000 : ℝ)^8201 ≤ (2673237667647/6250000000000 : ℝ)^6153 := by
    have hnat : (2643851 : ℕ)^8201*6250000000000^6153 ≤ 2673237667647^6153*5000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643851 5000000 2673237667647 6250000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105201059/5000000000 : ℝ)^8201 ≤ (13374616301609/100000000000000 : ℝ)^6153 := by
    have hnat : (1105201059 : ℕ)^8201*100000000000000^6153 ≤ 13374616301609^6153*5000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105201059 5000000000 13374616301609 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077545393/2000000000 : ℝ)^8201 ≤ (43853581000727/100000000000000 : ℝ)^6153 := by
    have hnat : (1077545393 : ℕ)^8201*100000000000000^6153 ≤ 43853581000727^6153*2000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077545393 2000000000 43853581000727 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8201/2048 : ℝ)) 8201 6153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643851/5000000 : ℝ), (-1105201059/5000000000 : ℝ), (1077545393/2000000000 : ℝ)] ![(2673237667647/6250000000000 : ℝ), (13374616301609/100000000000000 : ℝ), (43853581000727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643851/5000000 : ℝ)|^8201 ≤ (2673237667647/6250000000000 : ℝ)^6153
        have hw : |(2643851/5000000 : ℝ)|=(2643851/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1105201059/5000000000 : ℝ)|^8201 ≤ (13374616301609/100000000000000 : ℝ)^6153
        have hw : |(-1105201059/5000000000 : ℝ)|=(1105201059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077545393/2000000000 : ℝ)|^8201 ≤ (43853581000727/100000000000000 : ℝ)^6153
        have hw : |(1077545393/2000000000 : ℝ)|=(1077545393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1008_box_10 (p : ℝ) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5287702773/10000000000 : ℝ)*x 0 + (1077545349/2000000000 : ℝ)*x 1 + (-110520069/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287702773/10000000000 : ℝ)^8201 ≤ (10692952754071/25000000000000 : ℝ)^6153 := by
    have hnat : (5287702773 : ℕ)^8201*25000000000000^6153 ≤ 10692952754071^6153*10000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287702773 10000000000 10692952754071 25000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077545349/2000000000 : ℝ)^8201 ≤ (10963394653501/25000000000000 : ℝ)^6153 := by
    have hnat : (1077545349 : ℕ)^8201*25000000000000^6153 ≤ 10963394653501^6153*2000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077545349 2000000000 10963394653501 25000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110520069/500000000 : ℝ)^8201 ≤ (13374610349837/100000000000000 : ℝ)^6153 := by
    have hnat : (110520069 : ℕ)^8201*100000000000000^6153 ≤ 13374610349837^6153*500000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110520069 500000000 13374610349837 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8201/2048 : ℝ)) 8201 6153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287702773/10000000000 : ℝ), (1077545349/2000000000 : ℝ), (-110520069/500000000 : ℝ)] ![(10692952754071/25000000000000 : ℝ), (10963394653501/25000000000000 : ℝ), (13374610349837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287702773/10000000000 : ℝ)|^8201 ≤ (10692952754071/25000000000000 : ℝ)^6153
        have hw : |(5287702773/10000000000 : ℝ)|=(5287702773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077545349/2000000000 : ℝ)|^8201 ≤ (10963394653501/25000000000000 : ℝ)^6153
        have hw : |(1077545349/2000000000 : ℝ)|=(1077545349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-110520069/500000000 : ℝ)|^8201 ≤ (13374610349837/100000000000000 : ℝ)^6153
        have hw : |(-110520069/500000000 : ℝ)|=(110520069/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1008_box_11 (p : ℝ) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2256933601/5000000000 : ℝ)*x 0 + (432098451/1000000000 : ℝ)*x 1 + (4320983971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2256933601/5000000000 : ℝ)^8201 ≤ (17319558044081/50000000000000 : ℝ)^6153 := by
    have hnat : (2256933601 : ℕ)^8201*50000000000000^6153 ≤ 17319558044081^6153*5000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256933601 5000000000 17319558044081 50000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (432098451/1000000000 : ℝ)^8201 ≤ (6536088933097/20000000000000 : ℝ)^6153 := by
    have hnat : (432098451 : ℕ)^8201*20000000000000^6153 ≤ 6536088933097^6153*1000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432098451 1000000000 6536088933097 20000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4320983971/10000000000 : ℝ)^8201 ≤ (32680439232057/100000000000000 : ℝ)^6153 := by
    have hnat : (4320983971 : ℕ)^8201*100000000000000^6153 ≤ 32680439232057^6153*10000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320983971 10000000000 32680439232057 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8201/2048 : ℝ)) 8201 6153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2256933601/5000000000 : ℝ), (432098451/1000000000 : ℝ), (4320983971/10000000000 : ℝ)] ![(17319558044081/50000000000000 : ℝ), (6536088933097/20000000000000 : ℝ), (32680439232057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2256933601/5000000000 : ℝ)|^8201 ≤ (17319558044081/50000000000000 : ℝ)^6153
        have hw : |(2256933601/5000000000 : ℝ)|=(2256933601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(432098451/1000000000 : ℝ)|^8201 ≤ (6536088933097/20000000000000 : ℝ)^6153
        have hw : |(432098451/1000000000 : ℝ)|=(432098451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4320983971/10000000000 : ℝ)|^8201 ≤ (32680439232057/100000000000000 : ℝ)^6153
        have hw : |(4320983971/10000000000 : ℝ)|=(4320983971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1008_box_12 (p : ℝ) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-431335833/2000000000 : ℝ)*x 0 + (272189331/500000000 : ℝ)*x 1 + (5271208543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431335833/2000000000 : ℝ)^8201 ≤ (6471558562839/50000000000000 : ℝ)^6153 := by
    have hnat : (431335833 : ℕ)^8201*50000000000000^6153 ≤ 6471558562839^6153*2000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431335833 2000000000 6471558562839 50000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272189331/500000000 : ℝ)^8201 ≤ (4446280845149/10000000000000 : ℝ)^6153 := by
    have hnat : (272189331 : ℕ)^8201*10000000000000^6153 ≤ 4446280845149^6153*500000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272189331 500000000 4446280845149 10000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271208543/10000000000 : ℝ)^8201 ≤ (42594074413177/100000000000000 : ℝ)^6153 := by
    have hnat : (5271208543 : ℕ)^8201*100000000000000^6153 ≤ 42594074413177^6153*10000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271208543 10000000000 42594074413177 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8201/2048 : ℝ)) 8201 6153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431335833/2000000000 : ℝ), (272189331/500000000 : ℝ), (5271208543/10000000000 : ℝ)] ![(6471558562839/50000000000000 : ℝ), (4446280845149/10000000000000 : ℝ), (42594074413177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431335833/2000000000 : ℝ)|^8201 ≤ (6471558562839/50000000000000 : ℝ)^6153
        have hw : |(-431335833/2000000000 : ℝ)|=(431335833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(272189331/500000000 : ℝ)|^8201 ≤ (4446280845149/10000000000000 : ℝ)^6153
        have hw : |(272189331/500000000 : ℝ)|=(272189331/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271208543/10000000000 : ℝ)|^8201 ≤ (42594074413177/100000000000000 : ℝ)^6153
        have hw : |(5271208543/10000000000 : ℝ)|=(5271208543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1008_box_13 (p : ℝ) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2685138301/5000000000 : ℝ)*x 0 + (-1127873761/5000000000 : ℝ)*x 1 + (5271208471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685138301/5000000000 : ℝ)^8201 ≤ (43664368634403/100000000000000 : ℝ)^6153 := by
    have hnat : (2685138301 : ℕ)^8201*100000000000000^6153 ≤ 43664368634403^6153*5000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685138301 5000000000 43664368634403 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127873761/5000000000 : ℝ)^8201 ≤ (6870778856409/50000000000000 : ℝ)^6153 := by
    have hnat : (1127873761 : ℕ)^8201*50000000000000^6153 ≤ 6870778856409^6153*5000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127873761 5000000000 6870778856409 50000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271208471/10000000000 : ℝ)^8201 ≤ (42594073637731/100000000000000 : ℝ)^6153 := by
    have hnat : (5271208471 : ℕ)^8201*100000000000000^6153 ≤ 42594073637731^6153*10000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271208471 10000000000 42594073637731 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8201/2048 : ℝ)) 8201 6153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685138301/5000000000 : ℝ), (-1127873761/5000000000 : ℝ), (5271208471/10000000000 : ℝ)] ![(43664368634403/100000000000000 : ℝ), (6870778856409/50000000000000 : ℝ), (42594073637731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685138301/5000000000 : ℝ)|^8201 ≤ (43664368634403/100000000000000 : ℝ)^6153
        have hw : |(2685138301/5000000000 : ℝ)|=(2685138301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1127873761/5000000000 : ℝ)|^8201 ≤ (6870778856409/50000000000000 : ℝ)^6153
        have hw : |(-1127873761/5000000000 : ℝ)|=(1127873761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271208471/10000000000 : ℝ)|^8201 ≤ (42594073637731/100000000000000 : ℝ)^6153
        have hw : |(5271208471/10000000000 : ℝ)|=(5271208471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1008_box_14 (p : ℝ) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5370276111/10000000000 : ℝ)*x 0 + (1054241897/2000000000 : ℝ)*x 1 + (-140984177/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370276111/10000000000 : ℝ)^8201 ≤ (43664363313419/100000000000000 : ℝ)^6153 := by
    have hnat : (5370276111 : ℕ)^8201*100000000000000^6153 ≤ 43664363313419^6153*10000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370276111 10000000000 43664363313419 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054241897/2000000000 : ℝ)^8201 ≤ (42594084558591/100000000000000 : ℝ)^6153 := by
    have hnat : (1054241897 : ℕ)^8201*100000000000000^6153 ≤ 42594084558591^6153*2000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054241897 2000000000 42594084558591 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140984177/625000000 : ℝ)^8201 ≤ (6870776055207/50000000000000 : ℝ)^6153 := by
    have hnat : (140984177 : ℕ)^8201*50000000000000^6153 ≤ 6870776055207^6153*625000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140984177 625000000 6870776055207 50000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8201/2048 : ℝ)) 8201 6153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370276111/10000000000 : ℝ), (1054241897/2000000000 : ℝ), (-140984177/625000000 : ℝ)] ![(43664363313419/100000000000000 : ℝ), (42594084558591/100000000000000 : ℝ), (6870776055207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370276111/10000000000 : ℝ)|^8201 ≤ (43664363313419/100000000000000 : ℝ)^6153
        have hw : |(5370276111/10000000000 : ℝ)|=(5370276111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054241897/2000000000 : ℝ)|^8201 ≤ (42594084558591/100000000000000 : ℝ)^6153
        have hw : |(1054241897/2000000000 : ℝ)|=(1054241897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-140984177/625000000 : ℝ)|^8201 ≤ (6870776055207/50000000000000 : ℝ)^6153
        have hw : |(-140984177/625000000 : ℝ)|=(140984177/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1008_box_15 (p : ℝ) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2128356593/5000000000 : ℝ)*x 0 + (2224779359/5000000000 : ℝ)*x 1 + (444955801/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128356593/5000000000 : ℝ)^8201 ≤ (32034162140553/100000000000000 : ℝ)^6153 := by
    have hnat : (2128356593 : ℕ)^8201*100000000000000^6153 ≤ 32034162140553^6153*5000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128356593 5000000000 32034162140553 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2224779359/5000000000 : ℝ)^8201 ≤ (33982922526647/100000000000000 : ℝ)^6153 := by
    have hnat : (2224779359 : ℕ)^8201*100000000000000^6153 ≤ 33982922526647^6153*5000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224779359 5000000000 33982922526647 100000000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (444955801/1000000000 : ℝ)^8201 ≤ (4247864414951/12500000000000 : ℝ)^6153 := by
    have hnat : (444955801 : ℕ)^8201*12500000000000^6153 ≤ 4247864414951^6153*1000000000^8201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444955801 1000000000 4247864414951 12500000000000 8201 6153 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8201/2048 : ℝ)) 8201 6153 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2128356593/5000000000 : ℝ), (2224779359/5000000000 : ℝ), (444955801/1000000000 : ℝ)] ![(32034162140553/100000000000000 : ℝ), (33982922526647/100000000000000 : ℝ), (4247864414951/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2128356593/5000000000 : ℝ)|^8201 ≤ (32034162140553/100000000000000 : ℝ)^6153
        have hw : |(2128356593/5000000000 : ℝ)|=(2128356593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2224779359/5000000000 : ℝ)|^8201 ≤ (33982922526647/100000000000000 : ℝ)^6153
        have hw : |(2224779359/5000000000 : ℝ)|=(2224779359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(444955801/1000000000 : ℝ)|^8201 ≤ (4247864414951/12500000000000 : ℝ)^6153
        have hw : |(444955801/1000000000 : ℝ)|=(444955801/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1008_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73433023/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2793/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1117/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29599/50000 : ℝ) ∧ (19847/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82819/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2793/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1117/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2793/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1117/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2793/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1117/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2793/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1117/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2793/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1117/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2793/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1117/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1117/10000 : ℝ) ^ (1025/256 : ℝ) ≤ (15434556332514889/100000000000000000000 : ℝ) := by
    have hpowers : (1117/10000 : ℝ)^1025 ≤ (15434556332514889/100000000000000000000 : ℝ)^256 := by
      have hnat : (1117 : ℕ)^1025*100000000000000000000^256 ≤ 15434556332514889^256*10000^1025 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1117 10000 15434556332514889 100000000000000000000 1025 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1117/10000 : ℝ)) (X := (15434556332514889/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1025 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2793/20000 : ℝ) ^ (1025/256 : ℝ) ≤ (37741927524178639/100000000000000000000 : ℝ) := by
    have hpowers : (2793/20000 : ℝ)^1025 ≤ (37741927524178639/100000000000000000000 : ℝ)^256 := by
      have hnat : (2793 : ℕ)^1025*100000000000000000000^256 ≤ 37741927524178639^256*20000^1025 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2793 20000 37741927524178639 100000000000000000000 1025 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2793/20000 : ℝ)) (X := (37741927524178639/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1025 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015434556332514889/50000000000000000000 : ℝ) ≤ (10000770885651073/10000000000000000 : ℝ) ^ (1025/256 : ℝ) := by
    have hpowers : (50015434556332514889/50000000000000000000 : ℝ)^256 ≤ (10000770885651073/10000000000000000 : ℝ)^1025 := by
      have hnat : (50015434556332514889 : ℕ)^256*10000000000000000^1025 ≤ 10000770885651073^1025*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015434556332514889 50000000000000000000 10000770885651073 10000000000000000 256 1025 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000770885651073/10000000000000000 : ℝ)) (X := (50015434556332514889/50000000000000000000 : ℝ)) (by norm_num) 1025 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506647060482086691/12500000000000000000 : ℝ) ≤ (10001327850263197/10000000000000000 : ℝ) ^ (1025/256 : ℝ) := by
    have hpowers : (12506647060482086691/12500000000000000000 : ℝ)^256 ≤ (10001327850263197/10000000000000000 : ℝ)^1025 := by
      have hnat : (12506647060482086691 : ℕ)^256*10000000000000000^1025 ≤ 10001327850263197^1025*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506647060482086691 12500000000000000000 10001327850263197 10000000000000000 256 1025 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001327850263197/10000000000000000 : ℝ)) (X := (12506647060482086691/12500000000000000000 : ℝ)) (by norm_num) 1025 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037741927524178639/50000000000000000000 : ℝ) ≤ (10001884814875321/10000000000000000 : ℝ) ^ (1025/256 : ℝ) := by
    have hpowers : (50037741927524178639/50000000000000000000 : ℝ)^256 ≤ (10001884814875321/10000000000000000 : ℝ)^1025 := by
      have hnat : (50037741927524178639 : ℕ)^256*10000000000000000^1025 ≤ 10001884814875321^1025*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037741927524178639 50000000000000000000 10001884814875321 10000000000000000 256 1025 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001884814875321/10000000000000000 : ℝ)) (X := (50037741927524178639/50000000000000000000 : ℝ)) (by norm_num) 1025 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15434556332514889/100000000000000000000 : ℝ) ≤ ((223517696287679191/223600000000000000 : ℝ)+2*(139241153031/69875000000000 : ℝ)*(1117/10000 : ℝ))^(1025/256 : ℝ) := by
    rw [show (223517696287679191/223600000000000000 : ℝ)+2*(139241153031/69875000000000 : ℝ)*(1117/10000 : ℝ)=(10000770885651073/10000000000000000 : ℝ) by norm_num, show 1+2*(15434556332514889/100000000000000000000 : ℝ)=(50015434556332514889/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37741927524178639/100000000000000000000 : ℝ)+(15434556332514889/100000000000000000000 : ℝ) ≤ ((223517696287679191/223600000000000000 : ℝ)+(139241153031/69875000000000 : ℝ)*((2793/20000 : ℝ)+(1117/10000 : ℝ)))^(1025/256 : ℝ) := by
    rw [show (223517696287679191/223600000000000000 : ℝ)+(139241153031/69875000000000 : ℝ)*((2793/20000 : ℝ)+(1117/10000 : ℝ))=(10001327850263197/10000000000000000 : ℝ) by norm_num, show 1+(37741927524178639/100000000000000000000 : ℝ)+(15434556332514889/100000000000000000000 : ℝ)=(12506647060482086691/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37741927524178639/100000000000000000000 : ℝ) ≤ ((223517696287679191/223600000000000000 : ℝ)+2*(139241153031/69875000000000 : ℝ)*(2793/20000 : ℝ))^(1025/256 : ℝ) := by
    rw [show (223517696287679191/223600000000000000 : ℝ)+2*(139241153031/69875000000000 : ℝ)*(2793/20000 : ℝ)=(10001884814875321/10000000000000000 : ℝ) by norm_num, show 1+2*(37741927524178639/100000000000000000000 : ℝ)=(50037741927524178639/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (223517696287679191/223600000000000000 : ℝ)*(X 1 0+X 2 0)+(139241153031/69875000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1025/256 : ℝ)) (lo := (1117/10000 : ℝ)) (hi := (2793/20000 : ℝ)) (c := (223517696287679191/223600000000000000 : ℝ)) (alpha := (139241153031/69875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (223517696287679191/223600000000000000 : ℝ)*(X 0 1+X 2 1)+(139241153031/69875000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1025/256 : ℝ)) (lo := (1117/10000 : ℝ)) (hi := (2793/20000 : ℝ)) (c := (223517696287679191/223600000000000000 : ℝ)) (alpha := (139241153031/69875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (223517696287679191/223600000000000000 : ℝ)*(X 0 2+X 1 2)+(139241153031/69875000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1025/256 : ℝ)) (lo := (1117/10000 : ℝ)) (hi := (2793/20000 : ℝ)) (c := (223517696287679191/223600000000000000 : ℝ)) (alpha := (139241153031/69875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-16809227/80000000 : ℝ)*X 0 0+(1344534001/2500000000 : ℝ)*X 0 1+(5378135369/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1008_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1058900693/2000000000 : ℝ)*X 1 0+(-1107102519/5000000000 : ℝ)*X 1 1+(5378135681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1008_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647251679/5000000000 : ℝ)*X 2 0+(5378135717/10000000000 : ℝ)*X 2 1+(-2214205133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1008_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4492969373/10000000000 : ℝ)*X 0 0+(4331573233/10000000000 : ℝ)*X 0 1+(4331574073/10000000000 : ℝ)*X 0 2+(4492969373/10000000000 : ℝ)*X 1 0+(4331573233/10000000000 : ℝ)*X 1 1+(4331574073/10000000000 : ℝ)*X 1 2+(4492969373/10000000000 : ℝ)*X 2 0+(4331573233/10000000000 : ℝ)*X 2 1+(4331574073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1008_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-473108729/2000000000 : ℝ)*X 0 0+(1319794043/2500000000 : ℝ)*X 0 1+(1055835233/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1008_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2682316379/5000000000 : ℝ)*X 1 0+(-70397089/312500000 : ℝ)*X 1 1+(1055835243/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1008_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5364632801/10000000000 : ℝ)*X 2 0+(1055835239/2000000000 : ℝ)*X 2 1+(-1126353409/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1008_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1068632631/2500000000 : ℝ)*X 0 0+(55509639/125000000 : ℝ)*X 0 1+(4440771107/10000000000 : ℝ)*X 0 2+(1068632631/2500000000 : ℝ)*X 1 0+(55509639/125000000 : ℝ)*X 1 1+(4440771107/10000000000 : ℝ)*X 1 2+(1068632631/2500000000 : ℝ)*X 2 0+(55509639/125000000 : ℝ)*X 2 1+(4440771107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1008_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2310425773/10000000000 : ℝ)*X 0 0+(5212143331/10000000000 : ℝ)*X 0 1+(1077545341/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1008_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2643851/5000000 : ℝ)*X 1 0+(-1105201059/5000000000 : ℝ)*X 1 1+(1077545393/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1008_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5287702773/10000000000 : ℝ)*X 2 0+(1077545349/2000000000 : ℝ)*X 2 1+(-110520069/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1008_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2256933601/5000000000 : ℝ)*X 0 0+(432098451/1000000000 : ℝ)*X 0 1+(4320983971/10000000000 : ℝ)*X 0 2+(2256933601/5000000000 : ℝ)*X 1 0+(432098451/1000000000 : ℝ)*X 1 1+(4320983971/10000000000 : ℝ)*X 1 2+(2256933601/5000000000 : ℝ)*X 2 0+(432098451/1000000000 : ℝ)*X 2 1+(4320983971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1008_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-431335833/2000000000 : ℝ)*X 0 0+(272189331/500000000 : ℝ)*X 0 1+(5271208543/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1008_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2685138301/5000000000 : ℝ)*X 1 0+(-1127873761/5000000000 : ℝ)*X 1 1+(5271208471/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1008_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5370276111/10000000000 : ℝ)*X 2 0+(1054241897/2000000000 : ℝ)*X 2 1+(-140984177/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1008_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2128356593/5000000000 : ℝ)*X 0 0+(2224779359/5000000000 : ℝ)*X 0 1+(444955801/1000000000 : ℝ)*X 0 2+(2128356593/5000000000 : ℝ)*X 1 0+(2224779359/5000000000 : ℝ)*X 1 1+(444955801/1000000000 : ℝ)*X 1 2+(2128356593/5000000000 : ℝ)*X 2 0+(2224779359/5000000000 : ℝ)*X 2 1+(444955801/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1008_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-1739056844756225651315589963969/2795000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7272893/100000000000000 : ℝ)*(upper0) + (12153683/50000000000000 : ℝ)*(lower2) + (76857/2500000000000 : ℝ)*(upper5) + (951835062841253/25000000000000 : ℝ)*(major0) + (951835062841253/25000000000000 : ℝ)*(major1) + (951835062841253/25000000000000 : ℝ)*(major2) + (156369027/50000000000000 : ℝ)*(sp3) + (252151507385941/5000000000000 : ℝ)*(sp4) + (50430094275011/1000000000000 : ℝ)*(sp5) + (2521502389335309/50000000000000 : ℝ)*(sp6) + (1296194694333569/50000000000000 : ℝ)*(sp7) + (747163019/100000000000000 : ℝ)*(sp8) + (10733690369/50000000000000 : ℝ)*(sp13) + (1305810561/5000000000000 : ℝ)*(sp14) + (324048712675649/12500000000000 : ℝ)*(f.failure) + (5043030894881839/100000000000000 : ℝ)*(f.sum) + (6497256710837/13975000000000000000000000000 : ℝ)*base66 + (138775368472673923/5590000000000000000000000000000 : ℝ)*base67 + (48910597277206077/5590000000000000000000000000000 : ℝ)*base70 + (24287863842863923/5590000000000000000000000000000 : ℝ)*base71 + (370747203549569/6987500000000000000000000000 : ℝ)*base73 + (27744176329976077/5590000000000000000000000000000 : ℝ)*base76 + (44154833619283923/5590000000000000000000000000000 : ℝ)*base77 + (60133421207883923/5590000000000000000000000000000 : ℝ)*base79 + (5515747778989/1746875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (443073/625000000000000000000 : ℝ)*base90 + (443073/625000000000000000000 : ℝ)*base92 + (443073/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29599/50000 : ℝ) ≤ (3309318648019149803167386437529/5590000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (66011047/100000000000000 : ℝ)*(upper0) + (23666129/20000000000000 : ℝ)*(lower1) + (75053181/100000000000000 : ℝ)*(upper2) + (3869310899406373/100000000000000 : ℝ)*(major0) + (3869310899406373/100000000000000 : ℝ)*(major1) + (1934655449703187/50000000000000 : ℝ)*(major2) + (635537249132971/12500000000000 : ℝ)*(sp0) + (5084299609950293/100000000000000 : ℝ)*(sp1) + (317768909667187/6250000000000 : ℝ)*(sp2) + (1317291424978539/50000000000000 : ℝ)*(sp3) + (3569647043/100000000000000 : ℝ)*(sp5) + (78115293/12500000000000 : ℝ)*(sp6) + (5186533569/100000000000000 : ℝ)*(sp8) + (1102732861/50000000000000 : ℝ)*(sp11) + (2634585055422799/100000000000000 : ℝ)*(f.failure) + (635537897449667/12500000000000 : ℝ)*(f.sum) + (36706281164161/13975000000000000000000000000 : ℝ)*base66 + (260937114012214957/22360000000000000000000000000000 : ℝ)*base68 + (134066487962957483/11180000000000000000000000000000 : ℝ)*base70 + (221721720546134957/22360000000000000000000000000000 : ℝ)*base72 + (43113358675893/6987500000000000000000000000 : ℝ)*base74 + (29866788462662517/11180000000000000000000000000000 : ℝ)*base75 + (273616061120594157/22360000000000000000000000000000 : ℝ)*base78 + (403382301443794157/22360000000000000000000000000000 : ℝ)*base80 + (365824223593/218359375000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (23691377/5000000000000000000000 : ℝ)*base89 + (23691377/5000000000000000000000 : ℝ)*base91 + (26308623/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (19847/25000 : ℝ) ≤ (4437910408022143497210191693493/5590000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21804283/50000000000000 : ℝ)*(upper0) + (149036293/100000000000000 : ℝ)*(lower3) + (140667023/25000000000000 : ℝ)*(upper4) + (4337622848288427/100000000000000 : ℝ)*(major0) + (4337622848288427/100000000000000 : ℝ)*(major1) + (1084405712072107/25000000000000 : ℝ)*(major2) + (356075877601/100000000000000 : ℝ)*(sp1) + (67016857203/12500000000000 : ℝ)*(sp2) + (29442364121/10000000000000 : ℝ)*(sp3) + (2045484461/50000000000000 : ℝ)*(sp4) + (1139064606548483/20000000000000 : ℝ)*(sp8) + (711871380979217/12500000000000 : ℝ)*(sp9) + (5694790988853713/100000000000000 : ℝ)*(sp10) + (46143136871729/1562500000000 : ℝ)*(sp11) + (1476727591715933/50000000000000 : ℝ)*(f.failure) + (5695327123711337/100000000000000 : ℝ)*(f.sum) + (420178003813/2795000000000000000000000000 : ℝ)*base66 + (263709644401159843/22360000000000000000000000000000 : ℝ)*base68 + (30474997168274963/5590000000000000000000000000000 : ℝ)*base70 + (217909742889639843/22360000000000000000000000000000 : ℝ)*base72 + (9879951126589/1397500000000000000000000000 : ℝ)*base74 + (31318169379714963/5590000000000000000000000000000 : ℝ)*base76 + (185179515958699043/22360000000000000000000000000000 : ℝ)*base78 + (182961576130699043/22360000000000000000000000000000 : ℝ)*base80 + (28471345881351/6987500000000000000000000000 : ℝ)*base82 + (42455459/2500000000000000000000 : ℝ)*base89 + (42455459/2500000000000000000000 : ℝ)*base91 + (17455459/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-82819/100000 : ℝ) ≤ (-1157359448324580619898462272077/1397500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (298192353/50000000000000 : ℝ)*(lower0) + (129543547/100000000000000 : ℝ)*(lower1) + (502631457/100000000000000 : ℝ)*(upper5) + (546474267710651/12500000000000 : ℝ)*(major0) + (546474267710651/12500000000000 : ℝ)*(major1) + (546474267710651/12500000000000 : ℝ)*(major2) + (482949831/25000000000000 : ℝ)*(sp0) + (126026054047/25000000000000 : ℝ)*(sp5) + (9605058201/12500000000000 : ℝ)*(sp7) + (562512829/3125000000000 : ℝ)*(sp8) + (5794451660660997/100000000000000 : ℝ)*(sp12) + (5793967488654661/100000000000000 : ℝ)*(sp13) + (5794471592870849/100000000000000 : ℝ)*(sp14) + (2976645322862197/100000000000000 : ℝ)*(sp15) + (744180540831951/25000000000000 : ℝ)*(f.failure) + (5794471592870849/100000000000000 : ℝ)*(f.sum) + (18743969826083/13975000000000000000000000000 : ℝ)*base66 + (138703686907007459/2795000000000000000000000000000 : ℝ)*base68 + (50869804541492459/2795000000000000000000000000000 : ℝ)*base70 + (1486408063242541/2795000000000000000000000000000 : ℝ)*base71 + (196720327543677/3493750000000000000000000000 : ℝ)*base74 + (48263924258772459/2795000000000000000000000000000 : ℝ)*base76 + (9156280614092459/2795000000000000000000000000000 : ℝ)*base78 + (11891772384997541/2795000000000000000000000000000 : ℝ)*base79 + (30895382529379/6987500000000000000000000000 : ℝ)*base82 + (3082127/1250000000000000000000 : ℝ)*base90 + (3082127/1250000000000000000000 : ℝ)*base92 + (3082127/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1008_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73433023/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2793/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1117/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29599/50000 : ℝ) else (19847/25000 : ℝ) ≤ X j i ∧ X j i ≤ (82819/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1008_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1025/256 : ℝ) ≤ p) (hpb : p ≤ (8201/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73433023/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2793/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1117/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29599/50000 : ℝ) else (19847/25000 : ℝ) ≤ X j i ∧ X j i ≤ (82819/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_w1008_box p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

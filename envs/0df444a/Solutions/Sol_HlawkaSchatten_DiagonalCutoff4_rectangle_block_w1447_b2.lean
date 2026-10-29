-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1447_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:58:18.78599+00:00
-- url     : https://prove2.me/submissions/349a5e40-be14-43fb-aa9b-8eeda5689f01

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
theorem support_rectangle_w1447_s6_0 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1956619199/10000000000 : ℝ)*x 0 + (5407293007/10000000000 : ℝ)*x 1 + (16397789/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1956619199/10000000000 : ℝ)^4407 ≤ (11941322083499/100000000000000 : ℝ)^3383 := by
    have hnat : (1956619199 : ℕ)^4407*100000000000000^3383 ≤ 11941322083499^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956619199 10000000000 11941322083499 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407293007/10000000000 : ℝ)^4407 ≤ (2805663802671/6250000000000 : ℝ)^3383 := by
    have hnat : (5407293007 : ℕ)^4407*6250000000000^3383 ≤ 2805663802671^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407293007 10000000000 2805663802671 6250000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16397789/31250000 : ℝ)^4407 ≤ (5396007131621/12500000000000 : ℝ)^3383 := by
    have hnat : (16397789 : ℕ)^4407*12500000000000^3383 ≤ 5396007131621^3383*31250000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16397789 31250000 5396007131621 12500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1956619199/10000000000 : ℝ), (5407293007/10000000000 : ℝ), (16397789/31250000 : ℝ)] ![(11941322083499/100000000000000 : ℝ), (2805663802671/6250000000000 : ℝ), (5396007131621/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1956619199/10000000000 : ℝ)|^4407 ≤ (11941322083499/100000000000000 : ℝ)^3383
        have hw : |(-1956619199/10000000000 : ℝ)|=(1956619199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407293007/10000000000 : ℝ)|^4407 ≤ (2805663802671/6250000000000 : ℝ)^3383
        have hw : |(5407293007/10000000000 : ℝ)|=(5407293007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16397789/31250000 : ℝ)|^4407 ≤ (5396007131621/12500000000000 : ℝ)^3383
        have hw : |(16397789/31250000 : ℝ)|=(16397789/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s6_1 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673471101/5000000000 : ℝ)*x 0 + (-2038066291/10000000000 : ℝ)*x 1 + (5247292391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673471101/5000000000 : ℝ)^4407 ≤ (691235108017/1562500000000 : ℝ)^3383 := by
    have hnat : (2673471101 : ℕ)^4407*1562500000000^3383 ≤ 691235108017^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673471101 5000000000 691235108017 1562500000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2038066291/10000000000 : ℝ)^4407 ≤ (6296448484289/50000000000000 : ℝ)^3383 := by
    have hnat : (2038066291 : ℕ)^4407*50000000000000^3383 ≤ 6296448484289^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038066291 10000000000 6296448484289 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247292391/10000000000 : ℝ)^4407 ≤ (21584028049583/50000000000000 : ℝ)^3383 := by
    have hnat : (5247292391 : ℕ)^4407*50000000000000^3383 ≤ 21584028049583^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247292391 10000000000 21584028049583 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673471101/5000000000 : ℝ), (-2038066291/10000000000 : ℝ), (5247292391/10000000000 : ℝ)] ![(691235108017/1562500000000 : ℝ), (6296448484289/50000000000000 : ℝ), (21584028049583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673471101/5000000000 : ℝ)|^4407 ≤ (691235108017/1562500000000 : ℝ)^3383
        have hw : |(2673471101/5000000000 : ℝ)|=(2673471101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2038066291/10000000000 : ℝ)|^4407 ≤ (6296448484289/50000000000000 : ℝ)^3383
        have hw : |(-2038066291/10000000000 : ℝ)|=(2038066291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247292391/10000000000 : ℝ)|^4407 ≤ (21584028049583/50000000000000 : ℝ)^3383
        have hw : |(5247292391/10000000000 : ℝ)|=(5247292391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s6_2 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213877697/400000000 : ℝ)*x 0 + (2623646061/5000000000 : ℝ)*x 1 + (-2038066351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213877697/400000000 : ℝ)^4407 ≤ (44239049316599/100000000000000 : ℝ)^3383 := by
    have hnat : (213877697 : ℕ)^4407*100000000000000^3383 ≤ 44239049316599^3383*400000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213877697 400000000 44239049316599 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623646061/5000000000 : ℝ)^4407 ≤ (21584026608163/50000000000000 : ℝ)^3383 := by
    have hnat : (2623646061 : ℕ)^4407*50000000000000^3383 ≤ 21584026608163^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623646061 5000000000 21584026608163 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2038066351/10000000000 : ℝ)^4407 ≤ (503715898061/4000000000000 : ℝ)^3383 := by
    have hnat : (2038066351 : ℕ)^4407*4000000000000^3383 ≤ 503715898061^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038066351 10000000000 503715898061 4000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213877697/400000000 : ℝ), (2623646061/5000000000 : ℝ), (-2038066351/10000000000 : ℝ)] ![(44239049316599/100000000000000 : ℝ), (21584026608163/50000000000000 : ℝ), (503715898061/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213877697/400000000 : ℝ)|^4407 ≤ (44239049316599/100000000000000 : ℝ)^3383
        have hw : |(213877697/400000000 : ℝ)|=(213877697/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623646061/5000000000 : ℝ)|^4407 ≤ (21584026608163/50000000000000 : ℝ)^3383
        have hw : |(2623646061/5000000000 : ℝ)|=(2623646061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2038066351/10000000000 : ℝ)|^4407 ≤ (503715898061/4000000000000 : ℝ)^3383
        have hw : |(-2038066351/10000000000 : ℝ)|=(2038066351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s6_3 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4299892551/10000000000 : ℝ)*x 0 + (4128832901/10000000000 : ℝ)*x 1 + (4477251937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299892551/10000000000 : ℝ)^4407 ≤ (33304959847673/100000000000000 : ℝ)^3383 := by
    have hnat : (4299892551 : ℕ)^4407*100000000000000^3383 ≤ 33304959847673^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299892551 10000000000 33304959847673 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4128832901/10000000000 : ℝ)^4407 ≤ (15794726470151/50000000000000 : ℝ)^3383 := by
    have hnat : (4128832901 : ℕ)^4407*50000000000000^3383 ≤ 15794726470151^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128832901 10000000000 15794726470151 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4477251937/10000000000 : ℝ)^4407 ≤ (1755279360259/5000000000000 : ℝ)^3383 := by
    have hnat : (4477251937 : ℕ)^4407*5000000000000^3383 ≤ 1755279360259^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477251937 10000000000 1755279360259 5000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299892551/10000000000 : ℝ), (4128832901/10000000000 : ℝ), (4477251937/10000000000 : ℝ)] ![(33304959847673/100000000000000 : ℝ), (15794726470151/50000000000000 : ℝ), (1755279360259/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299892551/10000000000 : ℝ)|^4407 ≤ (33304959847673/100000000000000 : ℝ)^3383
        have hw : |(4299892551/10000000000 : ℝ)|=(4299892551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4128832901/10000000000 : ℝ)|^4407 ≤ (15794726470151/50000000000000 : ℝ)^3383
        have hw : |(4128832901/10000000000 : ℝ)|=(4128832901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4477251937/10000000000 : ℝ)|^4407 ≤ (1755279360259/5000000000000 : ℝ)^3383
        have hw : |(4477251937/10000000000 : ℝ)|=(4477251937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s6_4 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-9783153/50000000 : ℝ)*x 0 + (209914813/400000000 : ℝ)*x 1 + (5406711993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9783153/50000000 : ℝ)^4407 ≤ (2985353181427/25000000000000 : ℝ)^3383 := by
    have hnat : (9783153 : ℕ)^4407*25000000000000^3383 ≤ 2985353181427^3383*50000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9783153 50000000 2985353181427 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209914813/400000000 : ℝ)^4407 ≤ (10793562462621/25000000000000 : ℝ)^3383 := by
    have hnat : (209914813 : ℕ)^4407*25000000000000^3383 ≤ 10793562462621^3383*400000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209914813 400000000 10793562462621 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406711993/10000000000 : ℝ)^4407 ≤ (11221084354941/25000000000000 : ℝ)^3383 := by
    have hnat : (5406711993 : ℕ)^4407*25000000000000^3383 ≤ 11221084354941^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406711993 10000000000 11221084354941 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9783153/50000000 : ℝ), (209914813/400000000 : ℝ), (5406711993/10000000000 : ℝ)] ![(2985353181427/25000000000000 : ℝ), (10793562462621/25000000000000 : ℝ), (11221084354941/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9783153/50000000 : ℝ)|^4407 ≤ (2985353181427/25000000000000 : ℝ)^3383
        have hw : |(-9783153/50000000 : ℝ)|=(9783153/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209914813/400000000 : ℝ)|^4407 ≤ (10793562462621/25000000000000 : ℝ)^3383
        have hw : |(209914813/400000000 : ℝ)|=(209914813/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406711993/10000000000 : ℝ)|^4407 ≤ (11221084354941/25000000000000 : ℝ)^3383
        have hw : |(5406711993/10000000000 : ℝ)|=(5406711993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s6_5 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132631859/250000000 : ℝ)*x 0 + (-939323243/5000000000 : ℝ)*x 1 + (216268479/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132631859/250000000 : ℝ)^4407 ≤ (43790478292113/100000000000000 : ℝ)^3383 := by
    have hnat : (132631859 : ℕ)^4407*100000000000000^3383 ≤ 43790478292113^3383*250000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132631859 250000000 43790478292113 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (939323243/5000000000 : ℝ)^4407 ≤ (707824029837/6250000000000 : ℝ)^3383 := by
    have hnat : (939323243 : ℕ)^4407*6250000000000^3383 ≤ 707824029837^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939323243 5000000000 707824029837 6250000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216268479/400000000 : ℝ)^4407 ≤ (8976867445021/20000000000000 : ℝ)^3383 := by
    have hnat : (216268479 : ℕ)^4407*20000000000000^3383 ≤ 8976867445021^3383*400000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216268479 400000000 8976867445021 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132631859/250000000 : ℝ), (-939323243/5000000000 : ℝ), (216268479/400000000 : ℝ)] ![(43790478292113/100000000000000 : ℝ), (707824029837/6250000000000 : ℝ), (8976867445021/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132631859/250000000 : ℝ)|^4407 ≤ (43790478292113/100000000000000 : ℝ)^3383
        have hw : |(132631859/250000000 : ℝ)|=(132631859/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-939323243/5000000000 : ℝ)|^4407 ≤ (707824029837/6250000000000 : ℝ)^3383
        have hw : |(-939323243/5000000000 : ℝ)|=(939323243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216268479/400000000 : ℝ)|^4407 ≤ (8976867445021/20000000000000 : ℝ)^3383
        have hw : |(216268479/400000000 : ℝ)|=(216268479/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s6_6 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530527427/1000000000 : ℝ)*x 0 + (168959751/312500000 : ℝ)*x 1 + (-187864653/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530527427/1000000000 : ℝ)^4407 ≤ (2189523866219/5000000000000 : ℝ)^3383 := by
    have hnat : (530527427 : ℕ)^4407*5000000000000^3383 ≤ 2189523866219^3383*1000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530527427 1000000000 2189523866219 5000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168959751/312500000 : ℝ)^4407 ≤ (22442168920763/50000000000000 : ℝ)^3383 := by
    have hnat : (168959751 : ℕ)^4407*50000000000000^3383 ≤ 22442168920763^3383*312500000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168959751 312500000 22442168920763 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187864653/1000000000 : ℝ)^4407 ≤ (11325184822929/100000000000000 : ℝ)^3383 := by
    have hnat : (187864653 : ℕ)^4407*100000000000000^3383 ≤ 11325184822929^3383*1000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187864653 1000000000 11325184822929 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530527427/1000000000 : ℝ), (168959751/312500000 : ℝ), (-187864653/1000000000 : ℝ)] ![(2189523866219/5000000000000 : ℝ), (22442168920763/50000000000000 : ℝ), (11325184822929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530527427/1000000000 : ℝ)|^4407 ≤ (2189523866219/5000000000000 : ℝ)^3383
        have hw : |(530527427/1000000000 : ℝ)|=(530527427/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168959751/312500000 : ℝ)|^4407 ≤ (22442168920763/50000000000000 : ℝ)^3383
        have hw : |(168959751/312500000 : ℝ)|=(168959751/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-187864653/1000000000 : ℝ)|^4407 ≤ (11325184822929/100000000000000 : ℝ)^3383
        have hw : |(-187864653/1000000000 : ℝ)|=(187864653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s6_7 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4299916931/10000000000 : ℝ)*x 0 + (69937393/156250000 : ℝ)*x 1 + (4130098139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299916931/10000000000 : ℝ)^4407 ≤ (33305205842763/100000000000000 : ℝ)^3383 := by
    have hnat : (4299916931 : ℕ)^4407*100000000000000^3383 ≤ 33305205842763^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299916931 10000000000 33305205842763 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69937393/156250000 : ℝ)^4407 ≤ (8773182557249/25000000000000 : ℝ)^3383 := by
    have hnat : (69937393 : ℕ)^4407*25000000000000^3383 ≤ 8773182557249^3383*156250000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69937393 156250000 8773182557249 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4130098139/10000000000 : ℝ)^4407 ≤ (31602063902321/100000000000000 : ℝ)^3383 := by
    have hnat : (4130098139 : ℕ)^4407*100000000000000^3383 ≤ 31602063902321^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130098139 10000000000 31602063902321 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299916931/10000000000 : ℝ), (69937393/156250000 : ℝ), (4130098139/10000000000 : ℝ)] ![(33305205842763/100000000000000 : ℝ), (8773182557249/25000000000000 : ℝ), (31602063902321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299916931/10000000000 : ℝ)|^4407 ≤ (33305205842763/100000000000000 : ℝ)^3383
        have hw : |(4299916931/10000000000 : ℝ)|=(4299916931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(69937393/156250000 : ℝ)|^4407 ≤ (8773182557249/25000000000000 : ℝ)^3383
        have hw : |(69937393/156250000 : ℝ)|=(69937393/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4130098139/10000000000 : ℝ)|^4407 ≤ (31602063902321/100000000000000 : ℝ)^3383
        have hw : |(4130098139/10000000000 : ℝ)|=(4130098139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1447_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (711/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7383/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11373/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11373/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11373/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11373/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11373/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11373/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11373/100000 : ℝ) ^ (2203/512 : ℝ) ≤ (8663254575889871/100000000000000000000 : ℝ) := by
    have hpowers : (11373/100000 : ℝ)^2203 ≤ (8663254575889871/100000000000000000000 : ℝ)^512 := by
      have hnat : (11373 : ℕ)^2203*100000000000000000000^512 ≤ 8663254575889871^512*100000^2203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11373 100000 8663254575889871 100000000000000000000 2203 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11373/100000 : ℝ)) (X := (8663254575889871/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14769/100000 : ℝ) ^ (2203/512 : ℝ) ≤ (26664803248627393/100000000000000000000 : ℝ) := by
    have hpowers : (14769/100000 : ℝ)^2203 ≤ (26664803248627393/100000000000000000000 : ℝ)^512 := by
      have hnat : (14769 : ℕ)^2203*100000000000000000000^512 ≤ 26664803248627393^512*100000^2203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14769 100000 26664803248627393 100000000000000000000 2203 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14769/100000 : ℝ)) (X := (26664803248627393/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008663254575889871/50000000000000000000 : ℝ) ≤ (500020132961481/500000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (50008663254575889871/50000000000000000000 : ℝ)^512 ≤ (500020132961481/500000000000000 : ℝ)^2203 := by
      have hnat : (50008663254575889871 : ℕ)^512*500000000000000^2203 ≤ 500020132961481^2203*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008663254575889871 50000000000000000000 500020132961481 500000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500020132961481/500000000000000 : ℝ)) (X := (50008663254575889871/50000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252208003614032329/6250000000000000000 : ℝ) ≤ (5000410474662253/5000000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (6252208003614032329/6250000000000000000 : ℝ)^512 ≤ (5000410474662253/5000000000000000 : ℝ)^2203 := by
      have hnat : (6252208003614032329 : ℕ)^512*5000000000000000^2203 ≤ 5000410474662253^2203*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252208003614032329 6250000000000000000 5000410474662253 5000000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000410474662253/5000000000000000 : ℝ)) (X := (6252208003614032329/6250000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026664803248627393/50000000000000000000 : ℝ) ≤ (19533670389491/19531250000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (50026664803248627393/50000000000000000000 : ℝ)^512 ≤ (19533670389491/19531250000000 : ℝ)^2203 := by
      have hnat : (50026664803248627393 : ℕ)^512*19531250000000^2203 ≤ 19533670389491^2203*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026664803248627393 50000000000000000000 19533670389491 19531250000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (19533670389491/19531250000000 : ℝ)) (X := (50026664803248627393/50000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8663254575889871/100000000000000000000 : ℝ) ≤ ((2829321083687126047/2830000000000000000 : ℝ)+2*(209145047443/169800000000000 : ℝ)*(11373/100000 : ℝ))^(2203/512 : ℝ) := by
    rw [show (2829321083687126047/2830000000000000000 : ℝ)+2*(209145047443/169800000000000 : ℝ)*(11373/100000 : ℝ)=(500020132961481/500000000000000 : ℝ) by norm_num, show 1+2*(8663254575889871/100000000000000000000 : ℝ)=(50008663254575889871/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26664803248627393/100000000000000000000 : ℝ)+(8663254575889871/100000000000000000000 : ℝ) ≤ ((2829321083687126047/2830000000000000000 : ℝ)+(209145047443/169800000000000 : ℝ)*((14769/100000 : ℝ)+(11373/100000 : ℝ)))^(2203/512 : ℝ) := by
    rw [show (2829321083687126047/2830000000000000000 : ℝ)+(209145047443/169800000000000 : ℝ)*((14769/100000 : ℝ)+(11373/100000 : ℝ))=(5000410474662253/5000000000000000 : ℝ) by norm_num, show 1+(26664803248627393/100000000000000000000 : ℝ)+(8663254575889871/100000000000000000000 : ℝ)=(6252208003614032329/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26664803248627393/100000000000000000000 : ℝ) ≤ ((2829321083687126047/2830000000000000000 : ℝ)+2*(209145047443/169800000000000 : ℝ)*(14769/100000 : ℝ))^(2203/512 : ℝ) := by
    rw [show (2829321083687126047/2830000000000000000 : ℝ)+2*(209145047443/169800000000000 : ℝ)*(14769/100000 : ℝ)=(19533670389491/19531250000000 : ℝ) by norm_num, show 1+2*(26664803248627393/100000000000000000000 : ℝ)=(50026664803248627393/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2829321083687126047/2830000000000000000 : ℝ)*(X 1 0+X 2 0)+(209145047443/169800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (2829321083687126047/2830000000000000000 : ℝ)) (alpha := (209145047443/169800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2829321083687126047/2830000000000000000 : ℝ)*(X 0 1+X 2 1)+(209145047443/169800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (2829321083687126047/2830000000000000000 : ℝ)) (alpha := (209145047443/169800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2829321083687126047/2830000000000000000 : ℝ)*(X 0 2+X 1 2)+(209145047443/169800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (14769/100000 : ℝ)) (c := (2829321083687126047/2830000000000000000 : ℝ)) (alpha := (209145047443/169800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1956619199/10000000000 : ℝ)*X 0 0+(5407293007/10000000000 : ℝ)*X 0 1+(16397789/31250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673471101/5000000000 : ℝ)*X 1 0+(-2038066291/10000000000 : ℝ)*X 1 1+(5247292391/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213877697/400000000 : ℝ)*X 2 0+(2623646061/5000000000 : ℝ)*X 2 1+(-2038066351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4299892551/10000000000 : ℝ)*X 0 0+(4128832901/10000000000 : ℝ)*X 0 1+(4477251937/10000000000 : ℝ)*X 0 2+(4299892551/10000000000 : ℝ)*X 1 0+(4128832901/10000000000 : ℝ)*X 1 1+(4477251937/10000000000 : ℝ)*X 1 2+(4299892551/10000000000 : ℝ)*X 2 0+(4128832901/10000000000 : ℝ)*X 2 1+(4477251937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-9783153/50000000 : ℝ)*X 0 0+(209914813/400000000 : ℝ)*X 0 1+(5406711993/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132631859/250000000 : ℝ)*X 1 0+(-939323243/5000000000 : ℝ)*X 1 1+(216268479/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530527427/1000000000 : ℝ)*X 2 0+(168959751/312500000 : ℝ)*X 2 1+(-187864653/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4299916931/10000000000 : ℝ)*X 0 0+(69937393/156250000 : ℝ)*X 0 1+(4130098139/10000000000 : ℝ)*X 0 2+(4299916931/10000000000 : ℝ)*X 1 0+(69937393/156250000 : ℝ)*X 1 1+(4130098139/10000000000 : ℝ)*X 1 2+(4299916931/10000000000 : ℝ)*X 2 0+(69937393/156250000 : ℝ)*X 2 1+(4130098139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (795774603198755727492500893/70750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (356423003/25000000000000 : ℝ)*(base19) + (1386795579/100000000000000 : ℝ)*(base23) + (194063931/100000000000000 : ℝ)*(lower2) + (250874811/100000000000000 : ℝ)*(upper3) + (169453/500000000000 : ℝ)*(lower4) + (912016352761023/20000000000000 : ℝ)*(major0) + (912016352761023/20000000000000 : ℝ)*(major1) + (1140020440951279/25000000000000 : ℝ)*(major2) + (6250006539495809/100000000000000 : ℝ)*(sp0) + (3125014195679491/50000000000000 : ℝ)*(sp1) + (3125014215127707/50000000000000 : ℝ)*(sp2) + (2870117284590113/100000000000000 : ℝ)*(sp3) + (4655511037/20000000000000 : ℝ)*(sp4) + (16051045863/100000000000000 : ℝ)*(sp7) + (358766666954497/12500000000000 : ℝ)*(f.failure) + (3125014908525497/50000000000000 : ℝ)*(f.sum) + (40006676001167/16980000000000000000000000000 : ℝ)*base66 + (1433045539941721757/169800000000000000000000000000000 : ℝ)*base68 + (824074196419448387/70750000000000000000000000000000 : ℝ)*base70 + (1071843974991121757/169800000000000000000000000000000 : ℝ)*base72 + (19995456574873/16980000000000000000000000000 : ℝ)*base73 + (709604653962198387/70750000000000000000000000000000 : ℝ)*base76 + (568246376322783919/56600000000000000000000000000000 : ℝ)*base78 + (427844010557383919/56600000000000000000000000000000 : ℝ)*base80 + (1981362076521/566000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3758209/250000000000000000000 : ℝ)*base89 + (3758209/250000000000000000000 : ℝ)*base91 + (1258209/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (111481886686421187177441059/17687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1070500957/100000000000000 : ℝ)*(base19) + (542595411/50000000000000 : ℝ)*(base23) + (7599093/2000000000000 : ℝ)*(lower1) + (88352133/100000000000000 : ℝ)*(upper3) + (67608923/100000000000000 : ℝ)*(lower4) + (16052251/12500000000000 : ℝ)*(upper5) + (1148323850113699/25000000000000 : ℝ)*(major0) + (1148323850113699/25000000000000 : ℝ)*(major1) + (1148323850113699/25000000000000 : ℝ)*(major2) + (189329707/25000000000000 : ℝ)*(sp1) + (39347202888051/625000000000 : ℝ)*(sp4) + (50364405074147/800000000000 : ℝ)*(sp5) + (3147775688448669/50000000000000 : ℝ)*(sp6) + (1445519064363001/50000000000000 : ℝ)*(sp7) + (1445519064363001/50000000000000 : ℝ)*(f.failure) + (39347202888051/625000000000 : ℝ)*(f.sum) + (3526389437719/1061250000000000000000000000 : ℝ)*base66 + (2951215457896441/212250000000000000000000000000000 : ℝ)*base68 + (279432916219396441/212250000000000000000000000000000 : ℝ)*base70 + (135649347520603559/212250000000000000000000000000000 : ℝ)*base71 + (2277469700207/530625000000000000000000000 : ℝ)*base74 + (217121727108646441/212250000000000000000000000000000 : ℝ)*base76 + (7438778578396441/212250000000000000000000000000000 : ℝ)*base78 + (384050084153896441/212250000000000000000000000000000 : ℝ)*base80 + (380985190937/530625000000000000000000000 : ℝ)*base82 + (2987097/1000000000000000000000 : ℝ)*base89 + (2987097/1000000000000000000000 : ℝ)*base91 + (2987097/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1447_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (711/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1447_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1447_s7_0 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-978311733/5000000000 : ℝ)*x 0 + (540727151/1000000000 : ℝ)*x 1 + (163978469/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (978311733/5000000000 : ℝ)^4407 ≤ (2985339001931/25000000000000 : ℝ)^3383 := by
    have hnat : (978311733 : ℕ)^4407*25000000000000^3383 ≤ 2985339001931^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978311733 5000000000 2985339001931 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540727151/1000000000 : ℝ)^4407 ≤ (44890388358047/100000000000000 : ℝ)^3383 := by
    have hnat : (540727151 : ℕ)^4407*100000000000000^3383 ≤ 44890388358047^3383*1000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540727151 1000000000 44890388358047 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163978469/312500000 : ℝ)^4407 ≤ (10792063903847/25000000000000 : ℝ)^3383 := by
    have hnat : (163978469 : ℕ)^4407*25000000000000^3383 ≤ 10792063903847^3383*312500000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163978469 312500000 10792063903847 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-978311733/5000000000 : ℝ), (540727151/1000000000 : ℝ), (163978469/312500000 : ℝ)] ![(2985339001931/25000000000000 : ℝ), (44890388358047/100000000000000 : ℝ), (10792063903847/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-978311733/5000000000 : ℝ)|^4407 ≤ (2985339001931/25000000000000 : ℝ)^3383
        have hw : |(-978311733/5000000000 : ℝ)|=(978311733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540727151/1000000000 : ℝ)|^4407 ≤ (44890388358047/100000000000000 : ℝ)^3383
        have hw : |(540727151/1000000000 : ℝ)|=(540727151/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163978469/312500000 : ℝ)|^4407 ≤ (10792063903847/25000000000000 : ℝ)^3383
        have hw : |(163978469/312500000 : ℝ)|=(163978469/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s7_1 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346938609/10000000000 : ℝ)*x 0 + (-254756061/1250000000 : ℝ)*x 1 + (81989209/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346938609/10000000000 : ℝ)^4407 ≤ (44239008187457/100000000000000 : ℝ)^3383 := by
    have hnat : (5346938609 : ℕ)^4407*100000000000000^3383 ≤ 44239008187457^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346938609 10000000000 44239008187457 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (254756061/1250000000 : ℝ)^4407 ≤ (6296376835143/50000000000000 : ℝ)^3383 := by
    have hnat : (254756061 : ℕ)^4407*50000000000000^3383 ≤ 6296376835143^3383*1250000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254756061 1250000000 6296376835143 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81989209/156250000 : ℝ)^4407 ≤ (21584119062713/50000000000000 : ℝ)^3383 := by
    have hnat : (81989209 : ℕ)^4407*50000000000000^3383 ≤ 21584119062713^3383*156250000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81989209 156250000 21584119062713 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346938609/10000000000 : ℝ), (-254756061/1250000000 : ℝ), (81989209/156250000 : ℝ)] ![(44239008187457/100000000000000 : ℝ), (6296376835143/50000000000000 : ℝ), (21584119062713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346938609/10000000000 : ℝ)|^4407 ≤ (44239008187457/100000000000000 : ℝ)^3383
        have hw : |(5346938609/10000000000 : ℝ)|=(5346938609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-254756061/1250000000 : ℝ)|^4407 ≤ (6296376835143/50000000000000 : ℝ)^3383
        have hw : |(-254756061/1250000000 : ℝ)|=(254756061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81989209/156250000 : ℝ)|^4407 ≤ (21584119062713/50000000000000 : ℝ)^3383
        have hw : |(81989209/156250000 : ℝ)|=(81989209/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s7_2 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336734199/2500000000 : ℝ)*x 0 + (655914071/1250000000 : ℝ)*x 1 + (-407609333/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336734199/2500000000 : ℝ)^4407 ≤ (44238988646807/100000000000000 : ℝ)^3383 := by
    have hnat : (1336734199 : ℕ)^4407*100000000000000^3383 ≤ 44238988646807^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336734199 2500000000 44238988646807 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655914071/1250000000 : ℝ)^4407 ≤ (5396034041717/12500000000000 : ℝ)^3383 := by
    have hnat : (655914071 : ℕ)^4407*12500000000000^3383 ≤ 5396034041717^3383*1250000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655914071 1250000000 5396034041717 12500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407609333/2000000000 : ℝ)^4407 ≤ (12592738996781/100000000000000 : ℝ)^3383 := by
    have hnat : (407609333 : ℕ)^4407*100000000000000^3383 ≤ 12592738996781^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407609333 2000000000 12592738996781 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336734199/2500000000 : ℝ), (655914071/1250000000 : ℝ), (-407609333/2000000000 : ℝ)] ![(44238988646807/100000000000000 : ℝ), (5396034041717/12500000000000 : ℝ), (12592738996781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336734199/2500000000 : ℝ)|^4407 ≤ (44238988646807/100000000000000 : ℝ)^3383
        have hw : |(1336734199/2500000000 : ℝ)|=(1336734199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655914071/1250000000 : ℝ)|^4407 ≤ (5396034041717/12500000000000 : ℝ)^3383
        have hw : |(655914071/1250000000 : ℝ)|=(655914071/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-407609333/2000000000 : ℝ)|^4407 ≤ (12592738996781/100000000000000 : ℝ)^3383
        have hw : |(-407609333/2000000000 : ℝ)|=(407609333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s7_3 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1074973141/2500000000 : ℝ)*x 0 + (4128879077/10000000000 : ℝ)*x 1 + (2238603433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074973141/2500000000 : ℝ)^4407 ≤ (8326239994711/25000000000000 : ℝ)^3383 := by
    have hnat : (1074973141 : ℕ)^4407*25000000000000^3383 ≤ 8326239994711^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074973141 2500000000 8326239994711 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4128879077/10000000000 : ℝ)^4407 ≤ (31589913168151/100000000000000 : ℝ)^3383 := by
    have hnat : (4128879077 : ℕ)^4407*100000000000000^3383 ≤ 31589913168151^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128879077 10000000000 31589913168151 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2238603433/5000000000 : ℝ)^4407 ≤ (7021025368037/20000000000000 : ℝ)^3383 := by
    have hnat : (2238603433 : ℕ)^4407*20000000000000^3383 ≤ 7021025368037^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238603433 5000000000 7021025368037 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074973141/2500000000 : ℝ), (4128879077/10000000000 : ℝ), (2238603433/5000000000 : ℝ)] ![(8326239994711/25000000000000 : ℝ), (31589913168151/100000000000000 : ℝ), (7021025368037/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074973141/2500000000 : ℝ)|^4407 ≤ (8326239994711/25000000000000 : ℝ)^3383
        have hw : |(1074973141/2500000000 : ℝ)|=(1074973141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4128879077/10000000000 : ℝ)|^4407 ≤ (31589913168151/100000000000000 : ℝ)^3383
        have hw : |(4128879077/10000000000 : ℝ)|=(4128879077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2238603433/5000000000 : ℝ)|^4407 ≤ (7021025368037/20000000000000 : ℝ)^3383
        have hw : |(2238603433/5000000000 : ℝ)|=(2238603433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s7_4 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-978316501/5000000000 : ℝ)*x 0 + (5247889337/10000000000 : ℝ)*x 1 + (1081338277/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (978316501/5000000000 : ℝ)^4407 ≤ (5970715911263/50000000000000 : ℝ)^3383 := by
    have hnat : (978316501 : ℕ)^4407*50000000000000^3383 ≤ 5970715911263^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978316501 5000000000 5970715911263 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247889337/10000000000 : ℝ)^4407 ≤ (4317445360667/10000000000000 : ℝ)^3383 := by
    have hnat : (5247889337 : ℕ)^4407*10000000000000^3383 ≤ 4317445360667^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247889337 10000000000 4317445360667 10000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081338277/2000000000 : ℝ)^4407 ≤ (5610514319579/12500000000000 : ℝ)^3383 := by
    have hnat : (1081338277 : ℕ)^4407*12500000000000^3383 ≤ 5610514319579^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081338277 2000000000 5610514319579 12500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-978316501/5000000000 : ℝ), (5247889337/10000000000 : ℝ), (1081338277/2000000000 : ℝ)] ![(5970715911263/50000000000000 : ℝ), (4317445360667/10000000000000 : ℝ), (5610514319579/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-978316501/5000000000 : ℝ)|^4407 ≤ (5970715911263/50000000000000 : ℝ)^3383
        have hw : |(-978316501/5000000000 : ℝ)|=(978316501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247889337/10000000000 : ℝ)|^4407 ≤ (4317445360667/10000000000000 : ℝ)^3383
        have hw : |(5247889337/10000000000 : ℝ)|=(5247889337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081338277/2000000000 : ℝ)|^4407 ≤ (5610514319579/12500000000000 : ℝ)^3383
        have hw : |(1081338277/2000000000 : ℝ)|=(1081338277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s7_5 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305279851/10000000000 : ℝ)*x 0 + (-234833407/1250000000 : ℝ)*x 1 + (5406691433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305279851/10000000000 : ℝ)^4407 ≤ (5473817166821/12500000000000 : ℝ)^3383 := by
    have hnat : (5305279851 : ℕ)^4407*12500000000000^3383 ≤ 5473817166821^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305279851 10000000000 5473817166821 12500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (234833407/1250000000 : ℝ)^4407 ≤ (11325347586607/100000000000000 : ℝ)^3383 := by
    have hnat : (234833407 : ℕ)^4407*100000000000000^3383 ≤ 11325347586607^3383*1250000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234833407 1250000000 11325347586607 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406691433/10000000000 : ℝ)^4407 ≤ (22442057537861/50000000000000 : ℝ)^3383 := by
    have hnat : (5406691433 : ℕ)^4407*50000000000000^3383 ≤ 22442057537861^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406691433 10000000000 22442057537861 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305279851/10000000000 : ℝ), (-234833407/1250000000 : ℝ), (5406691433/10000000000 : ℝ)] ![(5473817166821/12500000000000 : ℝ), (11325347586607/100000000000000 : ℝ), (22442057537861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305279851/10000000000 : ℝ)|^4407 ≤ (5473817166821/12500000000000 : ℝ)^3383
        have hw : |(5305279851/10000000000 : ℝ)|=(5305279851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-234833407/1250000000 : ℝ)|^4407 ≤ (11325347586607/100000000000000 : ℝ)^3383
        have hw : |(-234833407/1250000000 : ℝ)|=(234833407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406691433/10000000000 : ℝ)|^4407 ≤ (22442057537861/50000000000000 : ℝ)^3383
        have hw : |(5406691433/10000000000 : ℝ)|=(5406691433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_s7_6 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-6420611/2500000000 : ℝ)*x 0 + (2935932249/5000000000 : ℝ)*x 1 + (1174371781/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6420611/2500000000 : ℝ)^4407 ≤ (10556000253/25000000000000 : ℝ)^3383 := by
    have hnat : (6420611 : ℕ)^4407*25000000000000^3383 ≤ 10556000253^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6420611 2500000000 10556000253 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2935932249/5000000000 : ℝ)^4407 ≤ (9995783800451/20000000000000 : ℝ)^3383 := by
    have hnat : (2935932249 : ℕ)^4407*20000000000000^3383 ≤ 9995783800451^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2935932249 5000000000 9995783800451 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1174371781/2000000000 : ℝ)^4407 ≤ (4997885698727/10000000000000 : ℝ)^3383 := by
    have hnat : (1174371781 : ℕ)^4407*10000000000000^3383 ≤ 4997885698727^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174371781 2000000000 4997885698727 10000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6420611/2500000000 : ℝ), (2935932249/5000000000 : ℝ), (1174371781/2000000000 : ℝ)] ![(10556000253/25000000000000 : ℝ), (9995783800451/20000000000000 : ℝ), (4997885698727/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6420611/2500000000 : ℝ)|^4407 ≤ (10556000253/25000000000000 : ℝ)^3383
        have hw : |(-6420611/2500000000 : ℝ)|=(6420611/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2935932249/5000000000 : ℝ)|^4407 ≤ (9995783800451/20000000000000 : ℝ)^3383
        have hw : |(2935932249/5000000000 : ℝ)|=(2935932249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1174371781/2000000000 : ℝ)|^4407 ≤ (4997885698727/10000000000000 : ℝ)^3383
        have hw : |(1174371781/2000000000 : ℝ)|=(1174371781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1447_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (711/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11377/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7383/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (711/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (711/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (711/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (711/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (711/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (711/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (711/6250 : ℝ) ^ (2203/512 : ℝ) ≤ (8673091538146061/100000000000000000000 : ℝ) := by
    have hpowers : (711/6250 : ℝ)^2203 ≤ (8673091538146061/100000000000000000000 : ℝ)^512 := by
      have hnat : (711 : ℕ)^2203*100000000000000000000^512 ≤ 8673091538146061^512*6250^2203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        711 6250 8673091538146061 100000000000000000000 2203 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (711/6250 : ℝ)) (X := (8673091538146061/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7383/50000 : ℝ) ^ (2203/512 : ℝ) ≤ (26641505851496393/100000000000000000000 : ℝ) := by
    have hpowers : (7383/50000 : ℝ)^2203 ≤ (26641505851496393/100000000000000000000 : ℝ)^512 := by
      have hnat : (7383 : ℕ)^2203*100000000000000000000^512 ≤ 26641505851496393^512*50000^2203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7383 50000 26641505851496393 100000000000000000000 2203 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7383/50000 : ℝ)) (X := (26641505851496393/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008673091538146061/50000000000000000000 : ℝ) ≤ (200008062328223/200000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (50008673091538146061/50000000000000000000 : ℝ)^512 ≤ (200008062328223/200000000000000 : ℝ)^2203 := by
      have hnat : (50008673091538146061 : ℕ)^512*200000000000000^2203 ≤ 200008062328223^2203*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008673091538146061 50000000000000000000 200008062328223 200000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200008062328223/200000000000000 : ℝ)) (X := (50008673091538146061/50000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017657298694821227/50000000000000000000 : ℝ) ≤ (10000820636574859/10000000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (50017657298694821227/50000000000000000000 : ℝ)^512 ≤ (10000820636574859/10000000000000000 : ℝ)^2203 := by
      have hnat : (50017657298694821227 : ℕ)^512*10000000000000000^2203 ≤ 10000820636574859^2203*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017657298694821227 50000000000000000000 10000820636574859 10000000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000820636574859/10000000000000000 : ℝ)) (X := (50017657298694821227/50000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026641505851496393/50000000000000000000 : ℝ) ≤ (1250154769592321/1250000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (50026641505851496393/50000000000000000000 : ℝ)^512 ≤ (1250154769592321/1250000000000000 : ℝ)^2203 := by
      have hnat : (50026641505851496393 : ℕ)^512*1250000000000000^2203 ≤ 1250154769592321^2203*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026641505851496393 50000000000000000000 1250154769592321 1250000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250154769592321/1250000000000000 : ℝ)) (X := (50026641505851496393/50000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8673091538146061/100000000000000000000 : ℝ) ≤ ((2824322262155757611/2825000000000000000 : ℝ)+2*(139173387903/113000000000000 : ℝ)*(711/6250 : ℝ))^(2203/512 : ℝ) := by
    rw [show (2824322262155757611/2825000000000000000 : ℝ)+2*(139173387903/113000000000000 : ℝ)*(711/6250 : ℝ)=(200008062328223/200000000000000 : ℝ) by norm_num, show 1+2*(8673091538146061/100000000000000000000 : ℝ)=(50008673091538146061/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26641505851496393/100000000000000000000 : ℝ)+(8673091538146061/100000000000000000000 : ℝ) ≤ ((2824322262155757611/2825000000000000000 : ℝ)+(139173387903/113000000000000 : ℝ)*((7383/50000 : ℝ)+(711/6250 : ℝ)))^(2203/512 : ℝ) := by
    rw [show (2824322262155757611/2825000000000000000 : ℝ)+(139173387903/113000000000000 : ℝ)*((7383/50000 : ℝ)+(711/6250 : ℝ))=(10000820636574859/10000000000000000 : ℝ) by norm_num, show 1+(26641505851496393/100000000000000000000 : ℝ)+(8673091538146061/100000000000000000000 : ℝ)=(50017657298694821227/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26641505851496393/100000000000000000000 : ℝ) ≤ ((2824322262155757611/2825000000000000000 : ℝ)+2*(139173387903/113000000000000 : ℝ)*(7383/50000 : ℝ))^(2203/512 : ℝ) := by
    rw [show (2824322262155757611/2825000000000000000 : ℝ)+2*(139173387903/113000000000000 : ℝ)*(7383/50000 : ℝ)=(1250154769592321/1250000000000000 : ℝ) by norm_num, show 1+2*(26641505851496393/100000000000000000000 : ℝ)=(50026641505851496393/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2824322262155757611/2825000000000000000 : ℝ)*(X 1 0+X 2 0)+(139173387903/113000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (711/6250 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (2824322262155757611/2825000000000000000 : ℝ)) (alpha := (139173387903/113000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2824322262155757611/2825000000000000000 : ℝ)*(X 0 1+X 2 1)+(139173387903/113000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (711/6250 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (2824322262155757611/2825000000000000000 : ℝ)) (alpha := (139173387903/113000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2824322262155757611/2825000000000000000 : ℝ)*(X 0 2+X 1 2)+(139173387903/113000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (711/6250 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (2824322262155757611/2825000000000000000 : ℝ)) (alpha := (139173387903/113000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-978311733/5000000000 : ℝ)*X 0 0+(540727151/1000000000 : ℝ)*X 0 1+(163978469/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346938609/10000000000 : ℝ)*X 1 0+(-254756061/1250000000 : ℝ)*X 1 1+(81989209/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336734199/2500000000 : ℝ)*X 2 0+(655914071/1250000000 : ℝ)*X 2 1+(-407609333/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1074973141/2500000000 : ℝ)*X 0 0+(4128879077/10000000000 : ℝ)*X 0 1+(2238603433/5000000000 : ℝ)*X 0 2+(1074973141/2500000000 : ℝ)*X 1 0+(4128879077/10000000000 : ℝ)*X 1 1+(2238603433/5000000000 : ℝ)*X 1 2+(1074973141/2500000000 : ℝ)*X 2 0+(4128879077/10000000000 : ℝ)*X 2 1+(2238603433/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-978316501/5000000000 : ℝ)*X 0 0+(5247889337/10000000000 : ℝ)*X 0 1+(1081338277/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305279851/10000000000 : ℝ)*X 1 0+(-234833407/1250000000 : ℝ)*X 1 1+(5406691433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((-6420611/2500000000 : ℝ)*X 0 0+(2935932249/5000000000 : ℝ)*X 0 1+(1174371781/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_s7_6 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4440859808997332807277/1412500000000000000000000000 : ℝ) := by norm_num
    linear_combination (22981311/25000000000000 : ℝ)*(upper2) + (167901309/100000000000000 : ℝ)*(lower3) + (7405327/1250000000000 : ℝ)*(lower4) + (299434431/50000000000000 : ℝ)*(lower5) + (570155196725087/12500000000000 : ℝ)*(major0) + (570155196725087/12500000000000 : ℝ)*(major1) + (570155196725087/12500000000000 : ℝ)*(major2) + (3125799006284269/50000000000000 : ℝ)*(sp0) + (6251511921608713/100000000000000 : ℝ)*(sp1) + (6251619718209199/100000000000000 : ℝ)*(sp2) + (1435431662296567/50000000000000 : ℝ)*(sp3) + (10531686717/100000000000000 : ℝ)*(sp4) + (53898300243/50000000000000 : ℝ)*(sp5) + (1396744243/12500000000000 : ℝ)*(sp6) + (1435431662296567/50000000000000 : ℝ)*(f.failure) + (6251619718209199/100000000000000 : ℝ)*(f.sum) + (19953173961697/1412500000000000000000000000 : ℝ)*base65 + (45847024261724657/35312500000000000000000000000000 : ℝ)*base67 + (196809962288900343/35312500000000000000000000000000 : ℝ)*base70 + (109500032317974657/35312500000000000000000000000000 : ℝ)*base71 + (5692650716947/1412500000000000000000000000 : ℝ)*base73 + (78409228176712843/35312500000000000000000000000000 : ℝ)*base76 + (683127631720162157/35312500000000000000000000000000 : ℝ)*base77 + (27837588845462843/35312500000000000000000000000000 : ℝ)*base80 + (8233472237319/2825000000000000000000000000 : ℝ)*base81 + (4241001/1000000000000000000000 : ℝ)*base90 + (4241001/1000000000000000000000 : ℝ)*base92 + (4241001/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1447_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (711/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1447_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1447_box_0 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1797245509/10000000000 : ℝ)*x 0 + (2692742553/5000000000 : ℝ)*x 1 + (2692742327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1797245509/10000000000 : ℝ)^4407 ≤ (5345084642817/50000000000000 : ℝ)^3383 := by
    have hnat : (1797245509 : ℕ)^4407*50000000000000^3383 ≤ 5345084642817^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797245509 10000000000 5345084642817 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692742553/5000000000 : ℝ)^4407 ≤ (697733090427/1562500000000 : ℝ)^3383 := by
    have hnat : (2692742553 : ℕ)^4407*1562500000000^3383 ≤ 697733090427^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692742553 5000000000 697733090427 1562500000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692742327/5000000000 : ℝ)^4407 ≤ (44654912905033/100000000000000 : ℝ)^3383 := by
    have hnat : (2692742327 : ℕ)^4407*100000000000000^3383 ≤ 44654912905033^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692742327 5000000000 44654912905033 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1797245509/10000000000 : ℝ), (2692742553/5000000000 : ℝ), (2692742327/5000000000 : ℝ)] ![(5345084642817/50000000000000 : ℝ), (697733090427/1562500000000 : ℝ), (44654912905033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1797245509/10000000000 : ℝ)|^4407 ≤ (5345084642817/50000000000000 : ℝ)^3383
        have hw : |(-1797245509/10000000000 : ℝ)|=(1797245509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692742553/5000000000 : ℝ)|^4407 ≤ (697733090427/1562500000000 : ℝ)^3383
        have hw : |(2692742553/5000000000 : ℝ)|=(2692742553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692742327/5000000000 : ℝ)|^4407 ≤ (44654912905033/100000000000000 : ℝ)^3383
        have hw : |(2692742327/5000000000 : ℝ)|=(2692742327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_box_1 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057236377/2000000000 : ℝ)*x 0 + (-1933745731/10000000000 : ℝ)*x 1 + (2692742239/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057236377/2000000000 : ℝ)^4407 ≤ (2179264836781/5000000000000 : ℝ)^3383 := by
    have hnat : (1057236377 : ℕ)^4407*5000000000000^3383 ≤ 2179264836781^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057236377 2000000000 2179264836781 5000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1933745731/10000000000 : ℝ)^4407 ≤ (470391690083/4000000000000 : ℝ)^3383 := by
    have hnat : (1933745731 : ℕ)^4407*4000000000000^3383 ≤ 470391690083^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933745731 10000000000 470391690083 4000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692742239/5000000000 : ℝ)^4407 ≤ (44654911003963/100000000000000 : ℝ)^3383 := by
    have hnat : (2692742239 : ℕ)^4407*100000000000000^3383 ≤ 44654911003963^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692742239 5000000000 44654911003963 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057236377/2000000000 : ℝ), (-1933745731/10000000000 : ℝ), (2692742239/5000000000 : ℝ)] ![(2179264836781/5000000000000 : ℝ), (470391690083/4000000000000 : ℝ), (44654911003963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057236377/2000000000 : ℝ)|^4407 ≤ (2179264836781/5000000000000 : ℝ)^3383
        have hw : |(1057236377/2000000000 : ℝ)|=(1057236377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1933745731/10000000000 : ℝ)|^4407 ≤ (470391690083/4000000000000 : ℝ)^3383
        have hw : |(-1933745731/10000000000 : ℝ)|=(1933745731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692742239/5000000000 : ℝ)|^4407 ≤ (44654911003963/100000000000000 : ℝ)^3383
        have hw : |(2692742239/5000000000 : ℝ)|=(2692742239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_box_2 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286181471/10000000000 : ℝ)*x 0 + (5385484997/10000000000 : ℝ)*x 1 + (-1933745583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286181471/10000000000 : ℝ)^4407 ≤ (8717058457781/20000000000000 : ℝ)^3383 := by
    have hnat : (5286181471 : ℕ)^4407*20000000000000^3383 ≤ 8717058457781^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286181471 10000000000 8717058457781 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385484997/10000000000 : ℝ)^4407 ≤ (1116372915249/2500000000000 : ℝ)^3383 := by
    have hnat : (5385484997 : ℕ)^4407*2500000000000^3383 ≤ 1116372915249^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385484997 10000000000 1116372915249 2500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1933745583/10000000000 : ℝ)^4407 ≤ (5879895539801/50000000000000 : ℝ)^3383 := by
    have hnat : (1933745583 : ℕ)^4407*50000000000000^3383 ≤ 5879895539801^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933745583 10000000000 5879895539801 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286181471/10000000000 : ℝ), (5385484997/10000000000 : ℝ), (-1933745583/10000000000 : ℝ)] ![(8717058457781/20000000000000 : ℝ), (1116372915249/2500000000000 : ℝ), (5879895539801/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286181471/10000000000 : ℝ)|^4407 ≤ (8717058457781/20000000000000 : ℝ)^3383
        have hw : |(5286181471/10000000000 : ℝ)|=(5286181471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385484997/10000000000 : ℝ)|^4407 ≤ (1116372915249/2500000000000 : ℝ)^3383
        have hw : |(5385484997/10000000000 : ℝ)|=(5385484997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1933745583/10000000000 : ℝ)|^4407 ≤ (5879895539801/50000000000000 : ℝ)^3383
        have hw : |(-1933745583/10000000000 : ℝ)|=(1933745583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_box_3 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4445838879/10000000000 : ℝ)*x 0 + (2115298017/5000000000 : ℝ)*x 1 + (2115297819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4445838879/10000000000 : ℝ)^4407 ≤ (2174066761017/6250000000000 : ℝ)^3383 := by
    have hnat : (4445838879 : ℕ)^4407*6250000000000^3383 ≤ 2174066761017^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4445838879 10000000000 2174066761017 6250000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115298017/5000000000 : ℝ)^4407 ≤ (4075933486557/12500000000000 : ℝ)^3383 := by
    have hnat : (2115298017 : ℕ)^4407*12500000000000^3383 ≤ 4075933486557^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115298017 5000000000 4075933486557 12500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115297819/5000000000 : ℝ)^4407 ≤ (32607463916407/100000000000000 : ℝ)^3383 := by
    have hnat : (2115297819 : ℕ)^4407*100000000000000^3383 ≤ 32607463916407^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115297819 5000000000 32607463916407 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4445838879/10000000000 : ℝ), (2115298017/5000000000 : ℝ), (2115297819/5000000000 : ℝ)] ![(2174066761017/6250000000000 : ℝ), (4075933486557/12500000000000 : ℝ), (32607463916407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4445838879/10000000000 : ℝ)|^4407 ≤ (2174066761017/6250000000000 : ℝ)^3383
        have hw : |(4445838879/10000000000 : ℝ)|=(4445838879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2115298017/5000000000 : ℝ)|^4407 ≤ (4075933486557/12500000000000 : ℝ)^3383
        have hw : |(2115298017/5000000000 : ℝ)|=(2115298017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115297819/5000000000 : ℝ)|^4407 ≤ (32607463916407/100000000000000 : ℝ)^3383
        have hw : |(2115297819/5000000000 : ℝ)|=(2115297819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_box_4 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2118724587/10000000000 : ℝ)*x 0 + (5266779063/10000000000 : ℝ)*x 1 + (2633389623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118724587/10000000000 : ℝ)^4407 ≤ (13245978707097/100000000000000 : ℝ)^3383 := by
    have hnat : (2118724587 : ℕ)^4407*100000000000000^3383 ≤ 13245978707097^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118724587 10000000000 13245978707097 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266779063/10000000000 : ℝ)^4407 ≤ (43377009656571/100000000000000 : ℝ)^3383 := by
    have hnat : (5266779063 : ℕ)^4407*100000000000000^3383 ≤ 43377009656571^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266779063 10000000000 43377009656571 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633389623/5000000000 : ℝ)^4407 ≤ (43377011619961/100000000000000 : ℝ)^3383 := by
    have hnat : (2633389623 : ℕ)^4407*100000000000000^3383 ≤ 43377011619961^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633389623 5000000000 43377011619961 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2118724587/10000000000 : ℝ), (5266779063/10000000000 : ℝ), (2633389623/5000000000 : ℝ)] ![(13245978707097/100000000000000 : ℝ), (43377009656571/100000000000000 : ℝ), (43377011619961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2118724587/10000000000 : ℝ)|^4407 ≤ (13245978707097/100000000000000 : ℝ)^3383
        have hw : |(-2118724587/10000000000 : ℝ)|=(2118724587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266779063/10000000000 : ℝ)|^4407 ≤ (43377009656571/100000000000000 : ℝ)^3383
        have hw : |(5266779063/10000000000 : ℝ)|=(5266779063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633389623/5000000000 : ℝ)|^4407 ≤ (43377011619961/100000000000000 : ℝ)^3383
        have hw : |(2633389623/5000000000 : ℝ)|=(2633389623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_box_5 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073839463/2000000000 : ℝ)*x 0 + (-123878311/625000000 : ℝ)*x 1 + (5266778929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073839463/2000000000 : ℝ)^4407 ≤ (44479065212181/100000000000000 : ℝ)^3383 := by
    have hnat : (1073839463 : ℕ)^4407*100000000000000^3383 ≤ 44479065212181^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073839463 2000000000 44479065212181 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123878311/625000000 : ℝ)^4407 ≤ (12143926544369/100000000000000 : ℝ)^3383 := by
    have hnat : (123878311 : ℕ)^4407*100000000000000^3383 ≤ 12143926544369^3383*625000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123878311 625000000 12143926544369 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266778929/10000000000 : ℝ)^4407 ≤ (43377008218897/100000000000000 : ℝ)^3383 := by
    have hnat : (5266778929 : ℕ)^4407*100000000000000^3383 ≤ 43377008218897^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266778929 10000000000 43377008218897 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073839463/2000000000 : ℝ), (-123878311/625000000 : ℝ), (5266778929/10000000000 : ℝ)] ![(44479065212181/100000000000000 : ℝ), (12143926544369/100000000000000 : ℝ), (43377008218897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073839463/2000000000 : ℝ)|^4407 ≤ (44479065212181/100000000000000 : ℝ)^3383
        have hw : |(1073839463/2000000000 : ℝ)|=(1073839463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-123878311/625000000 : ℝ)|^4407 ≤ (12143926544369/100000000000000 : ℝ)^3383
        have hw : |(-123878311/625000000 : ℝ)|=(123878311/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266778929/10000000000 : ℝ)|^4407 ≤ (43377008218897/100000000000000 : ℝ)^3383
        have hw : |(5266778929/10000000000 : ℝ)|=(5266778929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_box_6 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073839397/2000000000 : ℝ)*x 0 + (210671173/400000000 : ℝ)*x 1 + (-495513223/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073839397/2000000000 : ℝ)^4407 ≤ (44479061650941/100000000000000 : ℝ)^3383 := by
    have hnat : (1073839397 : ℕ)^4407*100000000000000^3383 ≤ 44479061650941^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073839397 2000000000 44479061650941 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210671173/400000000 : ℝ)^4407 ≤ (8675402493509/20000000000000 : ℝ)^3383 := by
    have hnat : (210671173 : ℕ)^4407*20000000000000^3383 ≤ 8675402493509^3383*400000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210671173 400000000 8675402493509 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (495513223/2500000000 : ℝ)^4407 ≤ (12143925873923/100000000000000 : ℝ)^3383 := by
    have hnat : (495513223 : ℕ)^4407*100000000000000^3383 ≤ 12143925873923^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495513223 2500000000 12143925873923 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073839397/2000000000 : ℝ), (210671173/400000000 : ℝ), (-495513223/2500000000 : ℝ)] ![(44479061650941/100000000000000 : ℝ), (8675402493509/20000000000000 : ℝ), (12143925873923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073839397/2000000000 : ℝ)|^4407 ≤ (44479061650941/100000000000000 : ℝ)^3383
        have hw : |(1073839397/2000000000 : ℝ)|=(1073839397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210671173/400000000 : ℝ)|^4407 ≤ (8675402493509/20000000000000 : ℝ)^3383
        have hw : |(210671173/400000000 : ℝ)|=(210671173/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-495513223/2500000000 : ℝ)|^4407 ≤ (12143925873923/100000000000000 : ℝ)^3383
        have hw : |(-495513223/2500000000 : ℝ)|=(495513223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_box_7 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4152876877/10000000000 : ℝ)*x 0 + (4377025967/10000000000 : ℝ)*x 1 + (4377026937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4152876877/10000000000 : ℝ)^4407 ≤ (31829305421727/100000000000000 : ℝ)^3383 := by
    have hnat : (4152876877 : ℕ)^4407*100000000000000^3383 ≤ 31829305421727^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152876877 10000000000 31829305421727 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4377025967/10000000000 : ℝ)^4407 ≤ (8521335590281/25000000000000 : ℝ)^3383 := by
    have hnat : (4377025967 : ℕ)^4407*25000000000000^3383 ≤ 8521335590281^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377025967 10000000000 8521335590281 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4377026937/10000000000 : ℝ)^4407 ≤ (6817070440253/20000000000000 : ℝ)^3383 := by
    have hnat : (4377026937 : ℕ)^4407*20000000000000^3383 ≤ 6817070440253^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377026937 10000000000 6817070440253 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4152876877/10000000000 : ℝ), (4377025967/10000000000 : ℝ), (4377026937/10000000000 : ℝ)] ![(31829305421727/100000000000000 : ℝ), (8521335590281/25000000000000 : ℝ), (6817070440253/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4152876877/10000000000 : ℝ)|^4407 ≤ (31829305421727/100000000000000 : ℝ)^3383
        have hw : |(4152876877/10000000000 : ℝ)|=(4152876877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4377025967/10000000000 : ℝ)|^4407 ≤ (8521335590281/25000000000000 : ℝ)^3383
        have hw : |(4377025967/10000000000 : ℝ)|=(4377025967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4377026937/10000000000 : ℝ)|^4407 ≤ (6817070440253/20000000000000 : ℝ)^3383
        have hw : |(4377026937/10000000000 : ℝ)|=(4377026937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_box_8 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2050973229/10000000000 : ℝ)*x 0 + (5184591357/10000000000 : ℝ)*x 1 + (53994481/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2050973229/10000000000 : ℝ)^4407 ≤ (1269688588761/10000000000000 : ℝ)^3383 := by
    have hnat : (2050973229 : ℕ)^4407*10000000000000^3383 ≤ 1269688588761^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050973229 10000000000 1269688588761 10000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184591357/10000000000 : ℝ)^4407 ≤ (132804110553/312500000000 : ℝ)^3383 := by
    have hnat : (5184591357 : ℕ)^4407*312500000000^3383 ≤ 132804110553^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184591357 10000000000 132804110553 312500000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53994481/100000000 : ℝ)^4407 ≤ (44805798715631/100000000000000 : ℝ)^3383 := by
    have hnat : (53994481 : ℕ)^4407*100000000000000^3383 ≤ 44805798715631^3383*100000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53994481 100000000 44805798715631 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2050973229/10000000000 : ℝ), (5184591357/10000000000 : ℝ), (53994481/100000000 : ℝ)] ![(1269688588761/10000000000000 : ℝ), (132804110553/312500000000 : ℝ), (44805798715631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2050973229/10000000000 : ℝ)|^4407 ≤ (1269688588761/10000000000000 : ℝ)^3383
        have hw : |(-2050973229/10000000000 : ℝ)|=(2050973229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184591357/10000000000 : ℝ)|^4407 ≤ (132804110553/312500000000 : ℝ)^3383
        have hw : |(5184591357/10000000000 : ℝ)|=(5184591357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53994481/100000000 : ℝ)|^4407 ≤ (44805798715631/100000000000000 : ℝ)^3383
        have hw : |(53994481/100000000 : ℝ)|=(53994481/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_box_9 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638206689/5000000000 : ℝ)*x 0 + (-481984523/2500000000 : ℝ)*x 1 + (674930931/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638206689/5000000000 : ℝ)^4407 ≤ (1358762623437/3125000000000 : ℝ)^3383 := by
    have hnat : (2638206689 : ℕ)^4407*3125000000000^3383 ≤ 1358762623437^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638206689 5000000000 1358762623437 3125000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (481984523/2500000000 : ℝ)^4407 ≤ (5856902187491/50000000000000 : ℝ)^3383 := by
    have hnat : (481984523 : ℕ)^4407*50000000000000^3383 ≤ 5856902187491^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      481984523 2500000000 5856902187491 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674930931/1250000000 : ℝ)^4407 ≤ (11201447916877/25000000000000 : ℝ)^3383 := by
    have hnat : (674930931 : ℕ)^4407*25000000000000^3383 ≤ 11201447916877^3383*1250000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674930931 1250000000 11201447916877 25000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638206689/5000000000 : ℝ), (-481984523/2500000000 : ℝ), (674930931/1250000000 : ℝ)] ![(1358762623437/3125000000000 : ℝ), (5856902187491/50000000000000 : ℝ), (11201447916877/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638206689/5000000000 : ℝ)|^4407 ≤ (1358762623437/3125000000000 : ℝ)^3383
        have hw : |(2638206689/5000000000 : ℝ)|=(2638206689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-481984523/2500000000 : ℝ)|^4407 ≤ (5856902187491/50000000000000 : ℝ)^3383
        have hw : |(-481984523/2500000000 : ℝ)|=(481984523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674930931/1250000000 : ℝ)|^4407 ≤ (11201447916877/25000000000000 : ℝ)^3383
        have hw : |(674930931/1250000000 : ℝ)|=(674930931/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_box_10 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638206489/5000000000 : ℝ)*x 0 + (5399447479/10000000000 : ℝ)*x 1 + (-192793859/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638206489/5000000000 : ℝ)^4407 ≤ (21740199828023/50000000000000 : ℝ)^3383 := by
    have hnat : (2638206489 : ℕ)^4407*50000000000000^3383 ≤ 21740199828023^3383*5000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638206489 5000000000 21740199828023 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399447479/10000000000 : ℝ)^4407 ≤ (22402896001309/50000000000000 : ℝ)^3383 := by
    have hnat : (5399447479 : ℕ)^4407*50000000000000^3383 ≤ 22402896001309^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399447479 10000000000 22402896001309 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (192793859/1000000000 : ℝ)^4407 ≤ (11713808316607/100000000000000 : ℝ)^3383 := by
    have hnat : (192793859 : ℕ)^4407*100000000000000^3383 ≤ 11713808316607^3383*1000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192793859 1000000000 11713808316607 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638206489/5000000000 : ℝ), (5399447479/10000000000 : ℝ), (-192793859/1000000000 : ℝ)] ![(21740199828023/50000000000000 : ℝ), (22402896001309/50000000000000 : ℝ), (11713808316607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638206489/5000000000 : ℝ)|^4407 ≤ (21740199828023/50000000000000 : ℝ)^3383
        have hw : |(2638206489/5000000000 : ℝ)|=(2638206489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399447479/10000000000 : ℝ)|^4407 ≤ (22402896001309/50000000000000 : ℝ)^3383
        have hw : |(5399447479/10000000000 : ℝ)|=(5399447479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-192793859/1000000000 : ℝ)|^4407 ≤ (11713808316607/100000000000000 : ℝ)^3383
        have hw : |(-192793859/1000000000 : ℝ)|=(192793859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_box_11 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (279983889/625000000 : ℝ)*x 0 + (4213357181/10000000000 : ℝ)*x 1 + (4213357099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (279983889/625000000 : ℝ)^4407 ≤ (17565512858919/50000000000000 : ℝ)^3383 := by
    have hnat : (279983889 : ℕ)^4407*50000000000000^3383 ≤ 17565512858919^3383*625000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279983889 625000000 17565512858919 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4213357181/10000000000 : ℝ)^4407 ≤ (16217243771597/50000000000000 : ℝ)^3383 := by
    have hnat : (4213357181 : ℕ)^4407*50000000000000^3383 ≤ 16217243771597^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213357181 10000000000 16217243771597 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4213357099/10000000000 : ℝ)^4407 ≤ (4054310840111/12500000000000 : ℝ)^3383 := by
    have hnat : (4213357099 : ℕ)^4407*12500000000000^3383 ≤ 4054310840111^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213357099 10000000000 4054310840111 12500000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(279983889/625000000 : ℝ), (4213357181/10000000000 : ℝ), (4213357099/10000000000 : ℝ)] ![(17565512858919/50000000000000 : ℝ), (16217243771597/50000000000000 : ℝ), (4054310840111/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(279983889/625000000 : ℝ)|^4407 ≤ (17565512858919/50000000000000 : ℝ)^3383
        have hw : |(279983889/625000000 : ℝ)|=(279983889/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4213357181/10000000000 : ℝ)|^4407 ≤ (16217243771597/50000000000000 : ℝ)^3383
        have hw : |(4213357181/10000000000 : ℝ)|=(4213357181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4213357099/10000000000 : ℝ)|^4407 ≤ (4054310840111/12500000000000 : ℝ)^3383
        have hw : |(4213357099/10000000000 : ℝ)|=(4213357099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_box_12 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-466286841/2500000000 : ℝ)*x 0 + (5465682899/10000000000 : ℝ)*x 1 + (5255644601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (466286841/2500000000 : ℝ)^4407 ≤ (11219289965669/100000000000000 : ℝ)^3383 := by
    have hnat : (466286841 : ℕ)^4407*100000000000000^3383 ≤ 11219289965669^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466286841 2500000000 11219289965669 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465682899/10000000000 : ℝ)^4407 ≤ (45523122751979/100000000000000 : ℝ)^3383 := by
    have hnat : (5465682899 : ℕ)^4407*100000000000000^3383 ≤ 45523122751979^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465682899 10000000000 45523122751979 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255644601/10000000000 : ℝ)^4407 ≤ (8651517453641/20000000000000 : ℝ)^3383 := by
    have hnat : (5255644601 : ℕ)^4407*20000000000000^3383 ≤ 8651517453641^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255644601 10000000000 8651517453641 20000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-466286841/2500000000 : ℝ), (5465682899/10000000000 : ℝ), (5255644601/10000000000 : ℝ)] ![(11219289965669/100000000000000 : ℝ), (45523122751979/100000000000000 : ℝ), (8651517453641/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-466286841/2500000000 : ℝ)|^4407 ≤ (11219289965669/100000000000000 : ℝ)^3383
        have hw : |(-466286841/2500000000 : ℝ)|=(466286841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465682899/10000000000 : ℝ)|^4407 ≤ (45523122751979/100000000000000 : ℝ)^3383
        have hw : |(5465682899/10000000000 : ℝ)|=(5465682899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255644601/10000000000 : ℝ)|^4407 ≤ (8651517453641/20000000000000 : ℝ)^3383
        have hw : |(5255644601/10000000000 : ℝ)|=(5255644601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_box_13 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376982483/10000000000 : ℝ)*x 0 + (-1986485189/10000000000 : ℝ)*x 1 + (5255644611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376982483/10000000000 : ℝ)^4407 ≤ (22281549175921/50000000000000 : ℝ)^3383 := by
    have hnat : (5376982483 : ℕ)^4407*50000000000000^3383 ≤ 22281549175921^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376982483 10000000000 22281549175921 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1986485189/10000000000 : ℝ)^4407 ≤ (6089657125903/50000000000000 : ℝ)^3383 := by
    have hnat : (1986485189 : ℕ)^4407*50000000000000^3383 ≤ 6089657125903^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986485189 10000000000 6089657125903 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255644611/10000000000 : ℝ)^4407 ≤ (21628793687713/50000000000000 : ℝ)^3383 := by
    have hnat : (5255644611 : ℕ)^4407*50000000000000^3383 ≤ 21628793687713^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255644611 10000000000 21628793687713 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376982483/10000000000 : ℝ), (-1986485189/10000000000 : ℝ), (5255644611/10000000000 : ℝ)] ![(22281549175921/50000000000000 : ℝ), (6089657125903/50000000000000 : ℝ), (21628793687713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376982483/10000000000 : ℝ)|^4407 ≤ (22281549175921/50000000000000 : ℝ)^3383
        have hw : |(5376982483/10000000000 : ℝ)|=(5376982483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1986485189/10000000000 : ℝ)|^4407 ≤ (6089657125903/50000000000000 : ℝ)^3383
        have hw : |(-1986485189/10000000000 : ℝ)|=(1986485189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255644611/10000000000 : ℝ)|^4407 ≤ (21628793687713/50000000000000 : ℝ)^3383
        have hw : |(5255644611/10000000000 : ℝ)|=(5255644611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_box_14 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344245613/2500000000 : ℝ)*x 0 + (5255644629/10000000000 : ℝ)*x 1 + (-248310651/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344245613/2500000000 : ℝ)^4407 ≤ (22281549008577/50000000000000 : ℝ)^3383 := by
    have hnat : (1344245613 : ℕ)^4407*50000000000000^3383 ≤ 22281549008577^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344245613 2500000000 22281549008577 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255644629/10000000000 : ℝ)^4407 ≤ (21628793784211/50000000000000 : ℝ)^3383 := by
    have hnat : (5255644629 : ℕ)^4407*50000000000000^3383 ≤ 21628793784211^3383*10000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255644629 10000000000 21628793784211 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (248310651/1250000000 : ℝ)^4407 ≤ (12179314403557/100000000000000 : ℝ)^3383 := by
    have hnat : (248310651 : ℕ)^4407*100000000000000^3383 ≤ 12179314403557^3383*1250000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248310651 1250000000 12179314403557 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344245613/2500000000 : ℝ), (5255644629/10000000000 : ℝ), (-248310651/1250000000 : ℝ)] ![(22281549008577/50000000000000 : ℝ), (21628793784211/50000000000000 : ℝ), (12179314403557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344245613/2500000000 : ℝ)|^4407 ≤ (22281549008577/50000000000000 : ℝ)^3383
        have hw : |(1344245613/2500000000 : ℝ)|=(1344245613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255644629/10000000000 : ℝ)|^4407 ≤ (21628793784211/50000000000000 : ℝ)^3383
        have hw : |(5255644629/10000000000 : ℝ)|=(5255644629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-248310651/1250000000 : ℝ)|^4407 ≤ (12179314403557/100000000000000 : ℝ)^3383
        have hw : |(-248310651/1250000000 : ℝ)|=(248310651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1447_box_15 (p : ℝ) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (824989369/2000000000 : ℝ)*x 0 + (1097687631/2500000000 : ℝ)*x 1 + (439075047/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (824989369/2000000000 : ℝ)^4407 ≤ (15775363453071/50000000000000 : ℝ)^3383 := by
    have hnat : (824989369 : ℕ)^4407*50000000000000^3383 ≤ 15775363453071^3383*2000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824989369 2000000000 15775363453071 50000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097687631/2500000000 : ℝ)^4407 ≤ (34224636814511/100000000000000 : ℝ)^3383 := by
    have hnat : (1097687631 : ℕ)^4407*100000000000000^3383 ≤ 34224636814511^3383*2500000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097687631 2500000000 34224636814511 100000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (439075047/1000000000 : ℝ)^4407 ≤ (3422463626619/10000000000000 : ℝ)^3383 := by
    have hnat : (439075047 : ℕ)^4407*10000000000000^3383 ≤ 3422463626619^3383*1000000000^4407 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439075047 1000000000 3422463626619 10000000000000 4407 3383 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4407/1024 : ℝ)) 4407 3383 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(824989369/2000000000 : ℝ), (1097687631/2500000000 : ℝ), (439075047/1000000000 : ℝ)] ![(15775363453071/50000000000000 : ℝ), (34224636814511/100000000000000 : ℝ), (3422463626619/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(824989369/2000000000 : ℝ)|^4407 ≤ (15775363453071/50000000000000 : ℝ)^3383
        have hw : |(824989369/2000000000 : ℝ)|=(824989369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097687631/2500000000 : ℝ)|^4407 ≤ (34224636814511/100000000000000 : ℝ)^3383
        have hw : |(1097687631/2500000000 : ℝ)|=(1097687631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(439075047/1000000000 : ℝ)|^4407 ≤ (3422463626619/10000000000000 : ℝ)^3383
        have hw : |(439075047/1000000000 : ℝ)|=(439075047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1447_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62911/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59149/100000 : ℝ) ∧ (80547/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (5297/6250 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11377/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11377/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11377/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11377/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11377/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11377/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11377/100000 : ℝ) ^ (2203/512 : ℝ) ≤ (347054897203181/4000000000000000000 : ℝ) := by
    have hpowers : (11377/100000 : ℝ)^2203 ≤ (347054897203181/4000000000000000000 : ℝ)^512 := by
      have hnat : (11377 : ℕ)^2203*4000000000000000000^512 ≤ 347054897203181^512*100000^2203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11377 100000 347054897203181 4000000000000000000 2203 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11377/100000 : ℝ)) (X := (347054897203181/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7383/50000 : ℝ) ^ (2203/512 : ℝ) ≤ (26641505851496393/100000000000000000000 : ℝ) := by
    have hpowers : (7383/50000 : ℝ)^2203 ≤ (26641505851496393/100000000000000000000 : ℝ)^512 := by
      have hnat : (7383 : ℕ)^2203*100000000000000000000^512 ≤ 26641505851496393^512*50000^2203 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7383 50000 26641505851496393 100000000000000000000 2203 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7383/50000 : ℝ)) (X := (26641505851496393/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000347054897203181/2000000000000000000 : ℝ) ≤ (2500100817223373/2500000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (2000347054897203181/2000000000000000000 : ℝ)^512 ≤ (2500100817223373/2500000000000000 : ℝ)^2203 := by
      have hnat : (2000347054897203181 : ℕ)^512*2500000000000000^2203 ≤ 2500100817223373^2203*2000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000347054897203181 2000000000000000000 2500100817223373 2500000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500100817223373/2500000000000000 : ℝ)) (X := (2000347054897203181/2000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017658939140787959/50000000000000000000 : ℝ) ≤ (10000820712805519/10000000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (50017658939140787959/50000000000000000000 : ℝ)^512 ≤ (10000820712805519/10000000000000000 : ℝ)^2203 := by
      have hnat : (50017658939140787959 : ℕ)^512*10000000000000000^2203 ≤ 10000820712805519^2203*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017658939140787959 50000000000000000000 10000820712805519 10000000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000820712805519/10000000000000000 : ℝ)) (X := (50017658939140787959/50000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026641505851496393/50000000000000000000 : ℝ) ≤ (5000619078358773/5000000000000000 : ℝ) ^ (2203/512 : ℝ) := by
    have hpowers : (50026641505851496393/50000000000000000000 : ℝ)^512 ≤ (5000619078358773/5000000000000000 : ℝ)^2203 := by
      have hnat : (50026641505851496393 : ℕ)^512*5000000000000000^2203 ≤ 5000619078358773^2203*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026641505851496393 50000000000000000000 5000619078358773 5000000000000000 512 2203 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000619078358773/5000000000000000 : ℝ)) (X := (50026641505851496393/50000000000000000000 : ℝ)) (by norm_num) 2203 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(347054897203181/4000000000000000000 : ℝ) ≤ ((3388186815950578203/3389000000000000000 : ℝ)+2*(417443912027/338900000000000 : ℝ)*(11377/100000 : ℝ))^(2203/512 : ℝ) := by
    rw [show (3388186815950578203/3389000000000000000 : ℝ)+2*(417443912027/338900000000000 : ℝ)*(11377/100000 : ℝ)=(2500100817223373/2500000000000000 : ℝ) by norm_num, show 1+2*(347054897203181/4000000000000000000 : ℝ)=(2000347054897203181/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26641505851496393/100000000000000000000 : ℝ)+(347054897203181/4000000000000000000 : ℝ) ≤ ((3388186815950578203/3389000000000000000 : ℝ)+(417443912027/338900000000000 : ℝ)*((7383/50000 : ℝ)+(11377/100000 : ℝ)))^(2203/512 : ℝ) := by
    rw [show (3388186815950578203/3389000000000000000 : ℝ)+(417443912027/338900000000000 : ℝ)*((7383/50000 : ℝ)+(11377/100000 : ℝ))=(10000820712805519/10000000000000000 : ℝ) by norm_num, show 1+(26641505851496393/100000000000000000000 : ℝ)+(347054897203181/4000000000000000000 : ℝ)=(50017658939140787959/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26641505851496393/100000000000000000000 : ℝ) ≤ ((3388186815950578203/3389000000000000000 : ℝ)+2*(417443912027/338900000000000 : ℝ)*(7383/50000 : ℝ))^(2203/512 : ℝ) := by
    rw [show (3388186815950578203/3389000000000000000 : ℝ)+2*(417443912027/338900000000000 : ℝ)*(7383/50000 : ℝ)=(5000619078358773/5000000000000000 : ℝ) by norm_num, show 1+2*(26641505851496393/100000000000000000000 : ℝ)=(50026641505851496393/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3388186815950578203/3389000000000000000 : ℝ)*(X 1 0+X 2 0)+(417443912027/338900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (11377/100000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (3388186815950578203/3389000000000000000 : ℝ)) (alpha := (417443912027/338900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3388186815950578203/3389000000000000000 : ℝ)*(X 0 1+X 2 1)+(417443912027/338900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (11377/100000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (3388186815950578203/3389000000000000000 : ℝ)) (alpha := (417443912027/338900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3388186815950578203/3389000000000000000 : ℝ)*(X 0 2+X 1 2)+(417443912027/338900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2203/512 : ℝ)) (lo := (11377/100000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (3388186815950578203/3389000000000000000 : ℝ)) (alpha := (417443912027/338900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1797245509/10000000000 : ℝ)*X 0 0+(2692742553/5000000000 : ℝ)*X 0 1+(2692742327/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1057236377/2000000000 : ℝ)*X 1 0+(-1933745731/10000000000 : ℝ)*X 1 1+(2692742239/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5286181471/10000000000 : ℝ)*X 2 0+(5385484997/10000000000 : ℝ)*X 2 1+(-1933745583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4445838879/10000000000 : ℝ)*X 0 0+(2115298017/5000000000 : ℝ)*X 0 1+(2115297819/5000000000 : ℝ)*X 0 2+(4445838879/10000000000 : ℝ)*X 1 0+(2115298017/5000000000 : ℝ)*X 1 1+(2115297819/5000000000 : ℝ)*X 1 2+(4445838879/10000000000 : ℝ)*X 2 0+(2115298017/5000000000 : ℝ)*X 2 1+(2115297819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2118724587/10000000000 : ℝ)*X 0 0+(5266779063/10000000000 : ℝ)*X 0 1+(2633389623/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1073839463/2000000000 : ℝ)*X 1 0+(-123878311/625000000 : ℝ)*X 1 1+(5266778929/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1073839397/2000000000 : ℝ)*X 2 0+(210671173/400000000 : ℝ)*X 2 1+(-495513223/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4152876877/10000000000 : ℝ)*X 0 0+(4377025967/10000000000 : ℝ)*X 0 1+(4377026937/10000000000 : ℝ)*X 0 2+(4152876877/10000000000 : ℝ)*X 1 0+(4377025967/10000000000 : ℝ)*X 1 1+(4377026937/10000000000 : ℝ)*X 1 2+(4152876877/10000000000 : ℝ)*X 2 0+(4377025967/10000000000 : ℝ)*X 2 1+(4377026937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2050973229/10000000000 : ℝ)*X 0 0+(5184591357/10000000000 : ℝ)*X 0 1+(53994481/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2638206689/5000000000 : ℝ)*X 1 0+(-481984523/2500000000 : ℝ)*X 1 1+(674930931/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2638206489/5000000000 : ℝ)*X 2 0+(5399447479/10000000000 : ℝ)*X 2 1+(-192793859/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((279983889/625000000 : ℝ)*X 0 0+(4213357181/10000000000 : ℝ)*X 0 1+(4213357099/10000000000 : ℝ)*X 0 2+(279983889/625000000 : ℝ)*X 1 0+(4213357181/10000000000 : ℝ)*X 1 1+(4213357099/10000000000 : ℝ)*X 1 2+(279983889/625000000 : ℝ)*X 2 0+(4213357181/10000000000 : ℝ)*X 2 1+(4213357099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-466286841/2500000000 : ℝ)*X 0 0+(5465682899/10000000000 : ℝ)*X 0 1+(5255644601/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5376982483/10000000000 : ℝ)*X 1 0+(-1986485189/10000000000 : ℝ)*X 1 1+(5255644611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1344245613/2500000000 : ℝ)*X 2 0+(5255644629/10000000000 : ℝ)*X 2 1+(-248310651/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((824989369/2000000000 : ℝ)*X 0 0+(1097687631/2500000000 : ℝ)*X 0 1+(439075047/1000000000 : ℝ)*X 0 2+(824989369/2000000000 : ℝ)*X 1 0+(1097687631/2500000000 : ℝ)*X 1 1+(439075047/1000000000 : ℝ)*X 1 2+(824989369/2000000000 : ℝ)*X 2 0+(1097687631/2500000000 : ℝ)*X 2 1+(439075047/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1447_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62911/100000 : ℝ) ≤ (-5329916315558463104449469943219/8472500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22953677/25000000000000 : ℝ)*(lower3) + (35575701/25000000000000 : ℝ)*(lower4) + (26236463/20000000000000 : ℝ)*(upper5) + (151815753294209/5000000000000 : ℝ)*(major0) + (151815753294209/5000000000000 : ℝ)*(major1) + (151815753294209/5000000000000 : ℝ)*(major2) + (1660866407/50000000000000 : ℝ)*(sp1) + (959302281/25000000000000 : ℝ)*(sp2) + (292820091/100000000000000 : ℝ)*(sp3) + (167301191969227/4000000000000 : ℝ)*(sp4) + (4182527681589553/100000000000000 : ℝ)*(sp5) + (2091263583056621/50000000000000 : ℝ)*(sp6) + (238883538831893/12500000000000 : ℝ)*(sp7) + (1204091691/100000000000000 : ℝ)*(sp12) + (382213720695047/20000000000000 : ℝ)*(f.failure) + (2091265501661183/50000000000000 : ℝ)*(f.sum) + (296853238941/169450000000000000000000000 : ℝ)*base66 + (68517122865136427/16945000000000000000000000000000 : ℝ)*base67 + (73353814686941427/16945000000000000000000000000000 : ℝ)*base69 + (143116688483633573/16945000000000000000000000000000 : ℝ)*base72 + (1743612808369/423625000000000000000000000 : ℝ)*base73 + (63180666642218573/16945000000000000000000000000000 : ℝ)*base76 + (36013989126238573/16945000000000000000000000000000 : ℝ)*base78 + (4410506232943573/16945000000000000000000000000000 : ℝ)*base80 + (5937834057649/1694500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (891559/400000000000000000000 : ℝ)*base89 + (891559/400000000000000000000 : ℝ)*base91 + (891559/400000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59149/100000 : ℝ) ≤ (50116451069608329459595985562801/84725000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (89156429/100000000000000 : ℝ)*(upper3) + (4464083/20000000000000 : ℝ)*(upper4) + (168913/400000000000 : ℝ)*(lower5) + (1554267913876489/50000000000000 : ℝ)*(major0) + (1554267913876489/50000000000000 : ℝ)*(major1) + (1554267913876489/50000000000000 : ℝ)*(major2) + (848164798058437/20000000000000 : ℝ)*(sp0) + (424070668336863/10000000000000 : ℝ)*(sp1) + (424082035995891/10000000000000 : ℝ)*(sp2) + (61141351861169/3125000000000 : ℝ)*(sp3) + (2339996333/25000000000000 : ℝ)*(sp6) + (343627847/25000000000000 : ℝ)*(sp7) + (5729652057/100000000000000 : ℝ)*(sp8) + (123036575613/100000000000000 : ℝ)*(sp9) + (489131158517199/25000000000000 : ℝ)*(f.failure) + (2120414859972121/50000000000000 : ℝ)*(f.sum) + (26047544205161/4236250000000000000000000000 : ℝ)*base66 + (955692196565550733/169450000000000000000000000000000 : ℝ)*base68 + (1303598968062099267/169450000000000000000000000000000 : ℝ)*base69 + (3050968413685800733/169450000000000000000000000000000 : ℝ)*base72 + (66286666357/33095703125000000000000000 : ℝ)*base74 + (690088742477200733/169450000000000000000000000000000 : ℝ)*base76 + (366365686604500733/169450000000000000000000000000000 : ℝ)*base78 + (64876988980499267/169450000000000000000000000000000 : ℝ)*base79 + (15442040491159/4236250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1592303/500000000000000000000 : ℝ)*base89 + (1592303/500000000000000000000 : ℝ)*base91 + (1592303/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80547/100000 : ℝ) ≤ (2729825703185680007946402833667/3389000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22094299/50000000000000 : ℝ)*(upper1) + (11641861/5000000000000 : ℝ)*(upper2) + (173321/97656250000 : ℝ)*(lower5) + (68308064353921/2000000000000 : ℝ)*(major0) + (68308064353921/2000000000000 : ℝ)*(major1) + (68308064353921/2000000000000 : ℝ)*(major2) + (23885781357/50000000000000 : ℝ)*(sp1) + (78305285261/100000000000000 : ℝ)*(sp3) + (12650544157/100000000000000 : ℝ)*(sp4) + (58178309393103/1250000000000 : ℝ)*(sp8) + (930848125489667/20000000000000 : ℝ)*(sp9) + (4654288399011049/100000000000000 : ℝ)*(sp10) + (429917973359541/20000000000000 : ℝ)*(sp11) + (2749254663/25000000000000 : ℝ)*(sp12) + (1074834086041483/50000000000000 : ℝ)*(f.failure) + (4654288399011049/100000000000000 : ℝ)*(f.sum) + (6105757257341/1694500000000000000000000000 : ℝ)*base65 + (12872396617190037/6778000000000000000000000000000 : ℝ)*base68 + (51582595643432037/6778000000000000000000000000000 : ℝ)*base70 + (38373378945448037/6778000000000000000000000000000 : ℝ)*base72 + (3809287344929/677800000000000000000000000 : ℝ)*base73 + (74136694962076037/6778000000000000000000000000000 : ℝ)*base76 + (8705614766204037/6778000000000000000000000000000 : ℝ)*base78 + (69904635562246037/6778000000000000000000000000000 : ℝ)*base80 + (14948265339097/3389000000000000000000000000 : ℝ)*base82 + (9831851/1000000000000000000000 : ℝ)*base89 + (9831851/1000000000000000000000 : ℝ)*base91 + (9831851/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-5297/6250 : ℝ) ≤ (-4487753000866685502893148516897/5295312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2416819/25000000000000 : ℝ)*(lower0) + (44029/312500000000 : ℝ)*(upper3) + (1906789/20000000000000 : ℝ)*(lower4) + (1726543468459273/50000000000000 : ℝ)*(major0) + (1726543468459273/50000000000000 : ℝ)*(major1) + (863271734229637/25000000000000 : ℝ)*(major2) + (520312141/100000000000000 : ℝ)*(sp0) + (14445410461/100000000000000 : ℝ)*(sp5) + (7733286719/100000000000000 : ℝ)*(sp6) + (2827220847/50000000000000 : ℝ)*(sp7) + (4761036747624453/100000000000000 : ℝ)*(sp12) + (1190255705631533/25000000000000 : ℝ)*(sp13) + (38088236277199/800000000000 : ℝ)*(sp14) + (2173380798223369/100000000000000 : ℝ)*(sp15) + (2173386452665063/100000000000000 : ℝ)*(f.failure) + (2380518633968297/50000000000000 : ℝ)*(f.sum) + (25657541871221/16945000000000000000000000000 : ℝ)*base66 + (3877631873643143581/169450000000000000000000000000000 : ℝ)*base68 + (520248672158782311/84725000000000000000000000000000 : ℝ)*base69 + (4864868545961293581/169450000000000000000000000000000 : ℝ)*base72 + (173829016216119/16945000000000000000000000000 : ℝ)*base73 + (81962989143632311/84725000000000000000000000000000 : ℝ)*base75 + (4663411638802363581/169450000000000000000000000000000 : ℝ)*base78 + (2763903123282063581/169450000000000000000000000000000 : ℝ)*base80 + (35457906061271/8472500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (30399111/2000000000000000000000 : ℝ)*base89 + (30399111/2000000000000000000000 : ℝ)*base91 + (9600889/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1447_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62911/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59149/100000 : ℝ) else (80547/100000 : ℝ) ≤ X j i ∧ X j i ≤ (5297/6250 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1447_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1447_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62911/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59149/100000 : ℝ) else (80547/100000 : ℝ) ≤ X j i ∧ X j i ≤ (5297/6250 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1447_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1447_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1447_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2203/512 : ℝ) ≤ p) (hpb : p ≤ (4407/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31776097/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62911/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59149/100000 : ℝ) else (80547/100000 : ℝ) ≤ X j i ∧ X j i ≤ (5297/6250 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1447_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

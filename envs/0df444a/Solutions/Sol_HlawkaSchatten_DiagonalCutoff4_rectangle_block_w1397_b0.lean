-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1397_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:44:37.072983+00:00
-- url     : https://prove2.me/submissions/b97ed472-59dc-4909-895d-12f4358c5570

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
theorem support_rectangle_w1397_s0_0 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2776679/15625000 : ℝ)*x 0 + (5973498693/10000000000 : ℝ)*x 1 + (192954431/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2776679/15625000 : ℝ)^4357 ≤ (2090365213881/20000000000000 : ℝ)^3333 := by
    have hnat : (2776679 : ℕ)^4357*20000000000000^3333 ≤ 2090365213881^3333*15625000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2776679 15625000 2090365213881 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5973498693/10000000000 : ℝ)^4357 ≤ (50989338425077/100000000000000 : ℝ)^3333 := by
    have hnat : (5973498693 : ℕ)^4357*100000000000000^3333 ≤ 50989338425077^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5973498693 10000000000 50989338425077 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (192954431/400000000 : ℝ)^4357 ≤ (7711767100223/20000000000000 : ℝ)^3333 := by
    have hnat : (192954431 : ℕ)^4357*20000000000000^3333 ≤ 7711767100223^3333*400000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192954431 400000000 7711767100223 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2776679/15625000 : ℝ), (5973498693/10000000000 : ℝ), (192954431/400000000 : ℝ)] ![(2090365213881/20000000000000 : ℝ), (50989338425077/100000000000000 : ℝ), (7711767100223/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2776679/15625000 : ℝ)|^4357 ≤ (2090365213881/20000000000000 : ℝ)^3333
        have hw : |(-2776679/15625000 : ℝ)|=(2776679/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5973498693/10000000000 : ℝ)|^4357 ≤ (50989338425077/100000000000000 : ℝ)^3333
        have hw : |(5973498693/10000000000 : ℝ)|=(5973498693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(192954431/400000000 : ℝ)|^4357 ≤ (7711767100223/20000000000000 : ℝ)^3333
        have hw : |(192954431/400000000 : ℝ)|=(192954431/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s0_1 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5495664037/10000000000 : ℝ)*x 0 + (-485591141/2000000000 : ℝ)*x 1 + (1205965239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5495664037/10000000000 : ℝ)^4357 ≤ (4572422844843/10000000000000 : ℝ)^3333 := by
    have hnat : (5495664037 : ℕ)^4357*10000000000000^3333 ≤ 4572422844843^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495664037 10000000000 4572422844843 10000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (485591141/2000000000 : ℝ)^4357 ≤ (15716934139209/100000000000000 : ℝ)^3333 := by
    have hnat : (485591141 : ℕ)^4357*100000000000000^3333 ≤ 15716934139209^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485591141 2000000000 15716934139209 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1205965239/2500000000 : ℝ)^4357 ≤ (38558837392413/100000000000000 : ℝ)^3333 := by
    have hnat : (1205965239 : ℕ)^4357*100000000000000^3333 ≤ 38558837392413^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205965239 2500000000 38558837392413 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5495664037/10000000000 : ℝ), (-485591141/2000000000 : ℝ), (1205965239/2500000000 : ℝ)] ![(4572422844843/10000000000000 : ℝ), (15716934139209/100000000000000 : ℝ), (38558837392413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5495664037/10000000000 : ℝ)|^4357 ≤ (4572422844843/10000000000000 : ℝ)^3333
        have hw : |(5495664037/10000000000 : ℝ)|=(5495664037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-485591141/2000000000 : ℝ)|^4357 ≤ (15716934139209/100000000000000 : ℝ)^3333
        have hw : |(-485591141/2000000000 : ℝ)|=(485591141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1205965239/2500000000 : ℝ)|^4357 ≤ (38558837392413/100000000000000 : ℝ)^3333
        have hw : |(1205965239/2500000000 : ℝ)|=(1205965239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s0_2 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (343479003/625000000 : ℝ)*x 0 + (482386093/1000000000 : ℝ)*x 1 + (-606988931/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343479003/625000000 : ℝ)^4357 ≤ (11431057142017/25000000000000 : ℝ)^3333 := by
    have hnat : (343479003 : ℕ)^4357*25000000000000^3333 ≤ 11431057142017^3333*625000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343479003 625000000 11431057142017 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482386093/1000000000 : ℝ)^4357 ≤ (7711767424147/20000000000000 : ℝ)^3333 := by
    have hnat : (482386093 : ℕ)^4357*20000000000000^3333 ≤ 7711767424147^3333*1000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482386093 1000000000 7711767424147 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (606988931/2500000000 : ℝ)^4357 ≤ (1571693429999/10000000000000 : ℝ)^3333 := by
    have hnat : (606988931 : ℕ)^4357*10000000000000^3333 ≤ 1571693429999^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606988931 2500000000 1571693429999 10000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(343479003/625000000 : ℝ), (482386093/1000000000 : ℝ), (-606988931/2500000000 : ℝ)] ![(11431057142017/25000000000000 : ℝ), (7711767424147/20000000000000 : ℝ), (1571693429999/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(343479003/625000000 : ℝ)|^4357 ≤ (11431057142017/25000000000000 : ℝ)^3333
        have hw : |(343479003/625000000 : ℝ)|=(343479003/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(482386093/1000000000 : ℝ)|^4357 ≤ (7711767424147/20000000000000 : ℝ)^3333
        have hw : |(482386093/1000000000 : ℝ)|=(482386093/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-606988931/2500000000 : ℝ)|^4357 ≤ (1571693429999/10000000000000 : ℝ)^3333
        have hw : |(-606988931/2500000000 : ℝ)|=(606988931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s0_3 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (834125209/2000000000 : ℝ)*x 0 + (3104286227/10000000000 : ℝ)*x 1 + (1112441639/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (834125209/2000000000 : ℝ)^4357 ≤ (996243333837/3125000000000 : ℝ)^3333 := by
    have hnat : (834125209 : ℕ)^4357*3125000000000^3333 ≤ 996243333837^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834125209 2000000000 996243333837 3125000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3104286227/10000000000 : ℝ)^4357 ≤ (10835446345237/50000000000000 : ℝ)^3333 := by
    have hnat : (3104286227 : ℕ)^4357*50000000000000^3333 ≤ 10835446345237^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104286227 10000000000 10835446345237 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1112441639/2000000000 : ℝ)^4357 ≤ (11612330150951/25000000000000 : ℝ)^3333 := by
    have hnat : (1112441639 : ℕ)^4357*25000000000000^3333 ≤ 11612330150951^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112441639 2000000000 11612330150951 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(834125209/2000000000 : ℝ), (3104286227/10000000000 : ℝ), (1112441639/2000000000 : ℝ)] ![(996243333837/3125000000000 : ℝ), (10835446345237/50000000000000 : ℝ), (11612330150951/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(834125209/2000000000 : ℝ)|^4357 ≤ (996243333837/3125000000000 : ℝ)^3333
        have hw : |(834125209/2000000000 : ℝ)|=(834125209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3104286227/10000000000 : ℝ)|^4357 ≤ (10835446345237/50000000000000 : ℝ)^3333
        have hw : |(3104286227/10000000000 : ℝ)|=(3104286227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1112441639/2000000000 : ℝ)|^4357 ≤ (11612330150951/25000000000000 : ℝ)^3333
        have hw : |(1112441639/2000000000 : ℝ)|=(1112441639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s0_4 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-222656237/1250000000 : ℝ)*x 0 + (4853344289/10000000000 : ℝ)*x 1 + (594296139/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (222656237/1250000000 : ℝ)^4357 ≤ (5241969754943/50000000000000 : ℝ)^3333 := by
    have hnat : (222656237 : ℕ)^4357*50000000000000^3333 ≤ 5241969754943^3333*1250000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222656237 1250000000 5241969754943 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4853344289/10000000000 : ℝ)^4357 ≤ (7773440462323/20000000000000 : ℝ)^3333 := by
    have hnat : (4853344289 : ℕ)^4357*20000000000000^3333 ≤ 7773440462323^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4853344289 10000000000 7773440462323 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (594296139/1000000000 : ℝ)^4357 ≤ (25324429082229/50000000000000 : ℝ)^3333 := by
    have hnat : (594296139 : ℕ)^4357*50000000000000^3333 ≤ 25324429082229^3333*1000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594296139 1000000000 25324429082229 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-222656237/1250000000 : ℝ), (4853344289/10000000000 : ℝ), (594296139/1000000000 : ℝ)] ![(5241969754943/50000000000000 : ℝ), (7773440462323/20000000000000 : ℝ), (25324429082229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-222656237/1250000000 : ℝ)|^4357 ≤ (5241969754943/50000000000000 : ℝ)^3333
        have hw : |(-222656237/1250000000 : ℝ)|=(222656237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4853344289/10000000000 : ℝ)|^4357 ≤ (7773440462323/20000000000000 : ℝ)^3333
        have hw : |(4853344289/10000000000 : ℝ)|=(4853344289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(594296139/1000000000 : ℝ)|^4357 ≤ (25324429082229/50000000000000 : ℝ)^3333
        have hw : |(594296139/1000000000 : ℝ)|=(594296139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s0_5 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5182041039/10000000000 : ℝ)*x 0 + (-261770857/2000000000 : ℝ)*x 1 + (237718387/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5182041039/10000000000 : ℝ)^4357 ≤ (21171749238009/50000000000000 : ℝ)^3333 := by
    have hnat : (5182041039 : ℕ)^4357*50000000000000^3333 ≤ 21171749238009^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182041039 10000000000 21171749238009 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261770857/2000000000 : ℝ)^4357 ≤ (7007662452879/100000000000000 : ℝ)^3333 := by
    have hnat : (261770857 : ℕ)^4357*100000000000000^3333 ≤ 7007662452879^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261770857 2000000000 7007662452879 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237718387/400000000 : ℝ)^4357 ≤ (3165552441117/6250000000000 : ℝ)^3333 := by
    have hnat : (237718387 : ℕ)^4357*6250000000000^3333 ≤ 3165552441117^3333*400000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237718387 400000000 3165552441117 6250000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5182041039/10000000000 : ℝ), (-261770857/2000000000 : ℝ), (237718387/400000000 : ℝ)] ![(21171749238009/50000000000000 : ℝ), (7007662452879/100000000000000 : ℝ), (3165552441117/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5182041039/10000000000 : ℝ)|^4357 ≤ (21171749238009/50000000000000 : ℝ)^3333
        have hw : |(5182041039/10000000000 : ℝ)|=(5182041039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-261770857/2000000000 : ℝ)|^4357 ≤ (7007662452879/100000000000000 : ℝ)^3333
        have hw : |(-261770857/2000000000 : ℝ)|=(261770857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(237718387/400000000 : ℝ)|^4357 ≤ (3165552441117/6250000000000 : ℝ)^3333
        have hw : |(237718387/400000000 : ℝ)|=(237718387/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s0_6 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5182036579/10000000000 : ℝ)*x 0 + (5942964251/10000000000 : ℝ)*x 1 + (-1308853809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5182036579/10000000000 : ℝ)^4357 ≤ (2646465677243/6250000000000 : ℝ)^3333 := by
    have hnat : (5182036579 : ℕ)^4357*6250000000000^3333 ≤ 2646465677243^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182036579 10000000000 2646465677243 6250000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5942964251/10000000000 : ℝ)^4357 ≤ (25324445019241/50000000000000 : ℝ)^3333 := by
    have hnat : (5942964251 : ℕ)^4357*50000000000000^3333 ≤ 25324445019241^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5942964251 10000000000 25324445019241 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1308853809/10000000000 : ℝ)^4357 ≤ (700765912137/10000000000000 : ℝ)^3333 := by
    have hnat : (1308853809 : ℕ)^4357*10000000000000^3333 ≤ 700765912137^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308853809 10000000000 700765912137 10000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5182036579/10000000000 : ℝ), (5942964251/10000000000 : ℝ), (-1308853809/10000000000 : ℝ)] ![(2646465677243/6250000000000 : ℝ), (25324445019241/50000000000000 : ℝ), (700765912137/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5182036579/10000000000 : ℝ)|^4357 ≤ (2646465677243/6250000000000 : ℝ)^3333
        have hw : |(5182036579/10000000000 : ℝ)|=(5182036579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5942964251/10000000000 : ℝ)|^4357 ≤ (25324445019241/50000000000000 : ℝ)^3333
        have hw : |(5942964251/10000000000 : ℝ)|=(5942964251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1308853809/10000000000 : ℝ)|^4357 ≤ (700765912137/10000000000000 : ℝ)^3333
        have hw : |(-1308853809/10000000000 : ℝ)|=(1308853809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s0_7 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (835909429/2000000000 : ℝ)*x 0 + (109983467/200000000 : ℝ)*x 1 + (3169577787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835909429/2000000000 : ℝ)^4357 ≤ (3996119807433/12500000000000 : ℝ)^3333 := by
    have hnat : (835909429 : ℕ)^4357*12500000000000^3333 ≤ 3996119807433^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835909429 2000000000 3996119807433 12500000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109983467/200000000 : ℝ)^4357 ≤ (45762400293699/100000000000000 : ℝ)^3333 := by
    have hnat : (109983467 : ℕ)^4357*100000000000000^3333 ≤ 45762400293699^3333*200000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109983467 200000000 45762400293699 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3169577787/10000000000 : ℝ)^4357 ≤ (11134320614157/50000000000000 : ℝ)^3333 := by
    have hnat : (3169577787 : ℕ)^4357*50000000000000^3333 ≤ 11134320614157^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3169577787 10000000000 11134320614157 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(835909429/2000000000 : ℝ), (109983467/200000000 : ℝ), (3169577787/10000000000 : ℝ)] ![(3996119807433/12500000000000 : ℝ), (45762400293699/100000000000000 : ℝ), (11134320614157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(835909429/2000000000 : ℝ)|^4357 ≤ (3996119807433/12500000000000 : ℝ)^3333
        have hw : |(835909429/2000000000 : ℝ)|=(835909429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(109983467/200000000 : ℝ)|^4357 ≤ (45762400293699/100000000000000 : ℝ)^3333
        have hw : |(109983467/200000000 : ℝ)|=(109983467/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3169577787/10000000000 : ℝ)|^4357 ≤ (11134320614157/50000000000000 : ℝ)^3333
        have hw : |(3169577787/10000000000 : ℝ)|=(3169577787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1397_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1819/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26481/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (1089/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1089 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1089*1^256 ≤ 0^256*1^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1089 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1089/256 : ℝ) ≤ (2028619099139394569/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1089 ≤ (2028619099139394569/100000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1089*100000000000000000000^256 ≤ 2028619099139394569^256*5^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2028619099139394569 100000000000000000000 1089 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2028619099139394569/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1089 := by
      have hnat : (1 : ℕ)^256*1^1089 ≤ 1^1089*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (102028619099139394569/100000000000000000000 : ℝ) ≤ (10047322738901163/10000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (102028619099139394569/100000000000000000000 : ℝ)^256 ≤ (10047322738901163/10000000000000000 : ℝ)^1089 := by
      have hnat : (102028619099139394569 : ℕ)^256*10000000000000000^1089 ≤ 10047322738901163^1089*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102028619099139394569 100000000000000000000 10047322738901163 10000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10047322738901163/10000000000000000 : ℝ)) (X := (102028619099139394569/100000000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (52028619099139394569/50000000000000000000 : ℝ) ≤ (5047322738901163/5000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (52028619099139394569/50000000000000000000 : ℝ)^256 ≤ (5047322738901163/5000000000000000 : ℝ)^1089 := by
      have hnat : (52028619099139394569 : ℕ)^256*5000000000000000^1089 ≤ 5047322738901163^1089*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52028619099139394569 50000000000000000000 5047322738901163 5000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5047322738901163/5000000000000000 : ℝ)) (X := (52028619099139394569/50000000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(47322738901163/4000000000000000 : ℝ)*(0 : ℝ))^(1089/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(47322738901163/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2028619099139394569/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(47322738901163/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1089/256 : ℝ) := by
    rw [show (1 : ℝ)+(47322738901163/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10047322738901163/10000000000000000 : ℝ) by norm_num, show 1+(2028619099139394569/100000000000000000000 : ℝ)+(0 : ℝ)=(102028619099139394569/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2028619099139394569/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(47322738901163/4000000000000000 : ℝ)*(2/5 : ℝ))^(1089/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(47322738901163/4000000000000000 : ℝ)*(2/5 : ℝ)=(5047322738901163/5000000000000000 : ℝ) by norm_num, show 1+2*(2028619099139394569/100000000000000000000 : ℝ)=(52028619099139394569/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(47322738901163/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47322738901163/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(47322738901163/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47322738901163/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(47322738901163/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47322738901163/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2776679/15625000 : ℝ)*X 0 0+(5973498693/10000000000 : ℝ)*X 0 1+(192954431/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5495664037/10000000000 : ℝ)*X 1 0+(-485591141/2000000000 : ℝ)*X 1 1+(1205965239/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((343479003/625000000 : ℝ)*X 2 0+(482386093/1000000000 : ℝ)*X 2 1+(-606988931/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((834125209/2000000000 : ℝ)*X 0 0+(3104286227/10000000000 : ℝ)*X 0 1+(1112441639/2000000000 : ℝ)*X 0 2+(834125209/2000000000 : ℝ)*X 1 0+(3104286227/10000000000 : ℝ)*X 1 1+(1112441639/2000000000 : ℝ)*X 1 2+(834125209/2000000000 : ℝ)*X 2 0+(3104286227/10000000000 : ℝ)*X 2 1+(1112441639/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-222656237/1250000000 : ℝ)*X 0 0+(4853344289/10000000000 : ℝ)*X 0 1+(594296139/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5182041039/10000000000 : ℝ)*X 1 0+(-261770857/2000000000 : ℝ)*X 1 1+(237718387/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5182036579/10000000000 : ℝ)*X 2 0+(5942964251/10000000000 : ℝ)*X 2 1+(-1308853809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((835909429/2000000000 : ℝ)*X 0 0+(109983467/200000000 : ℝ)*X 0 1+(3169577787/10000000000 : ℝ)*X 0 2+(835909429/2000000000 : ℝ)*X 1 0+(109983467/200000000 : ℝ)*X 1 1+(3169577787/10000000000 : ℝ)*X 1 2+(835909429/2000000000 : ℝ)*X 2 0+(109983467/200000000 : ℝ)*X 2 1+(3169577787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (298632704387135261682903/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41600043/100000000000000 : ℝ)*(base1) + (694136067/50000000000000 : ℝ)*(base19) + (1390013201/100000000000000 : ℝ)*(base23) + (44051939/25000000000000 : ℝ)*(upper3) + (85945221/50000000000000 : ℝ)*(upper5) + (159587600026109/25000000000000 : ℝ)*(major0) + (159587600026109/25000000000000 : ℝ)*(major1) + (159587600026109/25000000000000 : ℝ)*(major2) + (34793746891553/4000000000000 : ℝ)*(sp0) + (86984705036843/10000000000000 : ℝ)*(sp1) + (217461762156841/25000000000000 : ℝ)*(sp2) + (101712466435531/25000000000000 : ℝ)*(sp3) + (2403975891/50000000000000 : ℝ)*(sp4) + (2255137663/100000000000000 : ℝ)*(sp7) + (406852162479829/100000000000000 : ℝ)*(f.failure) + (217462109660141/25000000000000 : ℝ)*(f.sum) + (62297981685233/50000000000000000000000000000 : ℝ)*base66 + (86680178364767/100000000000000000000000000000 : ℝ)*base67 + (203974661135233/100000000000000000000000000000 : ℝ)*base70 + (296489407964767/100000000000000000000000000000 : ℝ)*base71 + (192601931935233/50000000000000000000000000000 : ℝ)*base74 + (586427066364767/100000000000000000000000000000 : ℝ)*base75 + (76776348235233/100000000000000000000000000000 : ℝ)*base78 + (104860801335233/100000000000000000000000000000 : ℝ)*base80 + (228959550785233/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (50856491/5000000000000000000000 : ℝ)*base90 + (50856491/5000000000000000000000 : ℝ)*base92 + (50856491/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1850181879553096665020523/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (194584801/10000000000000 : ℝ)*(base19) + (366476903/20000000000000 : ℝ)*(base23) + (549909441/100000000000000 : ℝ)*(base39) + (98886853/100000000000000 : ℝ)*(upper2) + (13182181/3125000000000 : ℝ)*(upper5) + (673504255228587/100000000000000 : ℝ)*(major0) + (673504255228587/100000000000000 : ℝ)*(major1) + (336751852659573/50000000000000 : ℝ)*(major2) + (1411949217/25000000000000 : ℝ)*(sp1) + (95846383/2000000000000 : ℝ)*(sp2) + (458875102874913/50000000000000 : ℝ)*(sp4) + (229435653026237/25000000000000 : ℝ)*(sp5) + (458872065477801/50000000000000 : ℝ)*(sp6) + (429257446434259/100000000000000 : ℝ)*(sp7) + (429257446434259/100000000000000 : ℝ)*(f.failure) + (917750755659267/100000000000000 : ℝ)*(f.sum) + (147644952886521/400000000000000000000000000000 : ℝ)*base66 + (233859140016601/200000000000000000000000000000 : ℝ)*base68 + (771903424053319/400000000000000000000000000000 : ℝ)*base70 + (532618395816601/200000000000000000000000000000 : ℝ)*base72 + (752578618713479/400000000000000000000000000000 : ℝ)*base73 + (723519251253319/400000000000000000000000000000 : ℝ)*base76 + (379944360053319/400000000000000000000000000000 : ℝ)*base78 + (1152050735653319/400000000000000000000000000000 : ℝ)*base80 + (75594677853319/200000000000000000000000000000 : ℝ)*base82 + (243539/5000000000000000000000 : ℝ)*base89 + (243539/5000000000000000000000 : ℝ)*base91 + (243539/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1397_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1819/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26481/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1397_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1397_s1_0 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-97699181/500000000 : ℝ)*x 0 + (5618327449/10000000000 : ℝ)*x 1 + (2532835301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (97699181/500000000 : ℝ)^4357 ≤ (5916161818089/50000000000000 : ℝ)^3333 := by
    have hnat : (97699181 : ℕ)^4357*50000000000000^3333 ≤ 5916161818089^3333*500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97699181 500000000 5916161818089 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5618327449/10000000000 : ℝ)^4357 ≤ (47062895082449/100000000000000 : ℝ)^3333 := by
    have hnat : (5618327449 : ℕ)^4357*100000000000000^3333 ≤ 47062895082449^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5618327449 10000000000 47062895082449 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2532835301/5000000000 : ℝ)^4357 ≤ (20552390634241/50000000000000 : ℝ)^3333 := by
    have hnat : (2532835301 : ℕ)^4357*50000000000000^3333 ≤ 20552390634241^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2532835301 5000000000 20552390634241 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-97699181/500000000 : ℝ), (5618327449/10000000000 : ℝ), (2532835301/5000000000 : ℝ)] ![(5916161818089/50000000000000 : ℝ), (47062895082449/100000000000000 : ℝ), (20552390634241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-97699181/500000000 : ℝ)|^4357 ≤ (5916161818089/50000000000000 : ℝ)^3333
        have hw : |(-97699181/500000000 : ℝ)|=(97699181/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5618327449/10000000000 : ℝ)|^4357 ≤ (47062895082449/100000000000000 : ℝ)^3333
        have hw : |(5618327449/10000000000 : ℝ)|=(5618327449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2532835301/5000000000 : ℝ)|^4357 ≤ (20552390634241/50000000000000 : ℝ)^3333
        have hw : |(2532835301/5000000000 : ℝ)|=(2532835301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s1_1 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400047729/10000000000 : ℝ)*x 0 + (-2247559379/10000000000 : ℝ)*x 1 + (2532835983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400047729/10000000000 : ℝ)^4357 ≤ (11171768500383/25000000000000 : ℝ)^3333 := by
    have hnat : (5400047729 : ℕ)^4357*25000000000000^3333 ≤ 11171768500383^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400047729 10000000000 11171768500383 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247559379/10000000000 : ℝ)^4357 ≤ (7104065123309/50000000000000 : ℝ)^3333 := by
    have hnat : (2247559379 : ℕ)^4357*50000000000000^3333 ≤ 7104065123309^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247559379 10000000000 7104065123309 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2532835983/5000000000 : ℝ)^4357 ≤ (10276198934233/25000000000000 : ℝ)^3333 := by
    have hnat : (2532835983 : ℕ)^4357*25000000000000^3333 ≤ 10276198934233^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2532835983 5000000000 10276198934233 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400047729/10000000000 : ℝ), (-2247559379/10000000000 : ℝ), (2532835983/5000000000 : ℝ)] ![(11171768500383/25000000000000 : ℝ), (7104065123309/50000000000000 : ℝ), (10276198934233/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400047729/10000000000 : ℝ)|^4357 ≤ (11171768500383/25000000000000 : ℝ)^3333
        have hw : |(5400047729/10000000000 : ℝ)|=(5400047729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2247559379/10000000000 : ℝ)|^4357 ≤ (7104065123309/50000000000000 : ℝ)^3333
        have hw : |(-2247559379/10000000000 : ℝ)|=(2247559379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2532835983/5000000000 : ℝ)|^4357 ≤ (10276198934233/25000000000000 : ℝ)^3333
        have hw : |(2532835983/5000000000 : ℝ)|=(2532835983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s1_2 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350012161/2500000000 : ℝ)*x 0 + (2532835393/5000000000 : ℝ)*x 1 + (-2247559697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350012161/2500000000 : ℝ)^4357 ≤ (8937416779953/20000000000000 : ℝ)^3333 := by
    have hnat : (1350012161 : ℕ)^4357*20000000000000^3333 ≤ 8937416779953^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350012161 2500000000 8937416779953 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2532835393/5000000000 : ℝ)^4357 ≤ (41104783220237/100000000000000 : ℝ)^3333 := by
    have hnat : (2532835393 : ℕ)^4357*100000000000000^3333 ≤ 41104783220237^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2532835393 5000000000 41104783220237 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247559697/10000000000 : ℝ)^4357 ≤ (55500519041/390625000000 : ℝ)^3333 := by
    have hnat : (2247559697 : ℕ)^4357*390625000000^3333 ≤ 55500519041^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247559697 10000000000 55500519041 390625000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350012161/2500000000 : ℝ), (2532835393/5000000000 : ℝ), (-2247559697/10000000000 : ℝ)] ![(8937416779953/20000000000000 : ℝ), (41104783220237/100000000000000 : ℝ), (55500519041/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350012161/2500000000 : ℝ)|^4357 ≤ (8937416779953/20000000000000 : ℝ)^3333
        have hw : |(1350012161/2500000000 : ℝ)|=(1350012161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2532835393/5000000000 : ℝ)|^4357 ≤ (41104783220237/100000000000000 : ℝ)^3333
        have hw : |(2532835393/5000000000 : ℝ)|=(2532835393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2247559697/10000000000 : ℝ)|^4357 ≤ (55500519041/390625000000 : ℝ)^3333
        have hw : |(-2247559697/10000000000 : ℝ)|=(2247559697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s1_3 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4282435619/10000000000 : ℝ)*x 0 + (372852619/1000000000 : ℝ)*x 1 + (4910101247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4282435619/10000000000 : ℝ)^4357 ≤ (3300159679423/10000000000000 : ℝ)^3333 := by
    have hnat : (4282435619 : ℕ)^4357*10000000000000^3333 ≤ 3300159679423^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4282435619 10000000000 3300159679423 10000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (372852619/1000000000 : ℝ)^4357 ≤ (6883990625299/25000000000000 : ℝ)^3333 := by
    have hnat : (372852619 : ℕ)^4357*25000000000000^3333 ≤ 6883990625299^3333*1000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372852619 1000000000 6883990625299 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4910101247/10000000000 : ℝ)^4357 ≤ (39462440694721/100000000000000 : ℝ)^3333 := by
    have hnat : (4910101247 : ℕ)^4357*100000000000000^3333 ≤ 39462440694721^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4910101247 10000000000 39462440694721 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4282435619/10000000000 : ℝ), (372852619/1000000000 : ℝ), (4910101247/10000000000 : ℝ)] ![(3300159679423/10000000000000 : ℝ), (6883990625299/25000000000000 : ℝ), (39462440694721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4282435619/10000000000 : ℝ)|^4357 ≤ (3300159679423/10000000000000 : ℝ)^3333
        have hw : |(4282435619/10000000000 : ℝ)|=(4282435619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(372852619/1000000000 : ℝ)|^4357 ≤ (6883990625299/25000000000000 : ℝ)^3333
        have hw : |(372852619/1000000000 : ℝ)|=(372852619/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4910101247/10000000000 : ℝ)|^4357 ≤ (39462440694721/100000000000000 : ℝ)^3333
        have hw : |(4910101247/10000000000 : ℝ)|=(4910101247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s1_4 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-977214003/5000000000 : ℝ)*x 0 + (1014463227/2000000000 : ℝ)*x 1 + (2805783099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977214003/5000000000 : ℝ)^4357 ≤ (11835841482857/100000000000000 : ℝ)^3333 := by
    have hnat : (977214003 : ℕ)^4357*100000000000000^3333 ≤ 11835841482857^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977214003 5000000000 11835841482857 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1014463227/2000000000 : ℝ)^4357 ≤ (41175287084959/100000000000000 : ℝ)^3333 := by
    have hnat : (1014463227 : ℕ)^4357*100000000000000^3333 ≤ 41175287084959^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014463227 2000000000 41175287084959 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2805783099/5000000000 : ℝ)^4357 ≤ (46988871417837/100000000000000 : ℝ)^3333 := by
    have hnat : (2805783099 : ℕ)^4357*100000000000000^3333 ≤ 46988871417837^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2805783099 5000000000 46988871417837 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-977214003/5000000000 : ℝ), (1014463227/2000000000 : ℝ), (2805783099/5000000000 : ℝ)] ![(11835841482857/100000000000000 : ℝ), (41175287084959/100000000000000 : ℝ), (46988871417837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-977214003/5000000000 : ℝ)|^4357 ≤ (11835841482857/100000000000000 : ℝ)^3333
        have hw : |(-977214003/5000000000 : ℝ)|=(977214003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1014463227/2000000000 : ℝ)|^4357 ≤ (41175287084959/100000000000000 : ℝ)^3333
        have hw : |(1014463227/2000000000 : ℝ)|=(1014463227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2805783099/5000000000 : ℝ)|^4357 ≤ (46988871417837/100000000000000 : ℝ)^3333
        have hw : |(2805783099/5000000000 : ℝ)|=(2805783099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s1_5 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628001847/5000000000 : ℝ)*x 0 + (-1701665067/10000000000 : ℝ)*x 1 + (561156617/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628001847/5000000000 : ℝ)^4357 ≤ (673988559557/1562500000000 : ℝ)^3333 := by
    have hnat : (2628001847 : ℕ)^4357*1562500000000^3333 ≤ 673988559557^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628001847 5000000000 673988559557 1562500000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1701665067/10000000000 : ℝ)^4357 ≤ (9875861073539/100000000000000 : ℝ)^3333 := by
    have hnat : (1701665067 : ℕ)^4357*100000000000000^3333 ≤ 9875861073539^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1701665067 10000000000 9875861073539 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561156617/1000000000 : ℝ)^4357 ≤ (2936804444459/6250000000000 : ℝ)^3333 := by
    have hnat : (561156617 : ℕ)^4357*6250000000000^3333 ≤ 2936804444459^3333*1000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561156617 1000000000 2936804444459 6250000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628001847/5000000000 : ℝ), (-1701665067/10000000000 : ℝ), (561156617/1000000000 : ℝ)] ![(673988559557/1562500000000 : ℝ), (9875861073539/100000000000000 : ℝ), (2936804444459/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628001847/5000000000 : ℝ)|^4357 ≤ (673988559557/1562500000000 : ℝ)^3333
        have hw : |(2628001847/5000000000 : ℝ)|=(2628001847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1701665067/10000000000 : ℝ)|^4357 ≤ (9875861073539/100000000000000 : ℝ)^3333
        have hw : |(-1701665067/10000000000 : ℝ)|=(1701665067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561156617/1000000000 : ℝ)|^4357 ≤ (2936804444459/6250000000000 : ℝ)^3333
        have hw : |(561156617/1000000000 : ℝ)|=(561156617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s1_6 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628002093/5000000000 : ℝ)*x 0 + (2805783291/5000000000 : ℝ)*x 1 + (-53176993/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628002093/5000000000 : ℝ)^4357 ≤ (862705461799/2000000000000 : ℝ)^3333 := by
    have hnat : (2628002093 : ℕ)^4357*2000000000000^3333 ≤ 862705461799^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628002093 5000000000 862705461799 2000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2805783291/5000000000 : ℝ)^4357 ≤ (5873609452647/12500000000000 : ℝ)^3333 := by
    have hnat : (2805783291 : ℕ)^4357*12500000000000^3333 ≤ 5873609452647^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2805783291 5000000000 5873609452647 12500000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53176993/312500000 : ℝ)^4357 ≤ (1975170255821/20000000000000 : ℝ)^3333 := by
    have hnat : (53176993 : ℕ)^4357*20000000000000^3333 ≤ 1975170255821^3333*312500000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53176993 312500000 1975170255821 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628002093/5000000000 : ℝ), (2805783291/5000000000 : ℝ), (-53176993/312500000 : ℝ)] ![(862705461799/2000000000000 : ℝ), (5873609452647/12500000000000 : ℝ), (1975170255821/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628002093/5000000000 : ℝ)|^4357 ≤ (862705461799/2000000000000 : ℝ)^3333
        have hw : |(2628002093/5000000000 : ℝ)|=(2628002093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2805783291/5000000000 : ℝ)|^4357 ≤ (5873609452647/12500000000000 : ℝ)^3333
        have hw : |(2805783291/5000000000 : ℝ)|=(2805783291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-53176993/312500000 : ℝ)|^4357 ≤ (1975170255821/20000000000000 : ℝ)^3333
        have hw : |(-53176993/312500000 : ℝ)|=(53176993/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s1_7 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53542341/125000000 : ℝ)*x 0 + (4895893237/10000000000 : ℝ)*x 1 + (467872447/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53542341/125000000 : ℝ)^4357 ≤ (33011184031021/100000000000000 : ℝ)^3333 := by
    have hnat : (53542341 : ℕ)^4357*100000000000000^3333 ≤ 33011184031021^3333*125000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53542341 125000000 33011184031021 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4895893237/10000000000 : ℝ)^4357 ≤ (3931323487031/10000000000000 : ℝ)^3333 := by
    have hnat : (4895893237 : ℕ)^4357*10000000000000^3333 ≤ 3931323487031^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4895893237 10000000000 3931323487031 10000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467872447/1250000000 : ℝ)^4357 ≤ (27675581081237/100000000000000 : ℝ)^3333 := by
    have hnat : (467872447 : ℕ)^4357*100000000000000^3333 ≤ 27675581081237^3333*1250000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467872447 1250000000 27675581081237 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53542341/125000000 : ℝ), (4895893237/10000000000 : ℝ), (467872447/1250000000 : ℝ)] ![(33011184031021/100000000000000 : ℝ), (3931323487031/10000000000000 : ℝ), (27675581081237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53542341/125000000 : ℝ)|^4357 ≤ (33011184031021/100000000000000 : ℝ)^3333
        have hw : |(53542341/125000000 : ℝ)|=(53542341/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4895893237/10000000000 : ℝ)|^4357 ≤ (3931323487031/10000000000000 : ℝ)^3333
        have hw : |(4895893237/10000000000 : ℝ)|=(4895893237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(467872447/1250000000 : ℝ)|^4357 ≤ (27675581081237/100000000000000 : ℝ)^3333
        have hw : |(467872447/1250000000 : ℝ)|=(467872447/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1397_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1819/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3691/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2383/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1819/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1819/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1819/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1819/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1819/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1819/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1819/100000 : ℝ) ^ (1089/256 : ℝ) ≤ (3958142654879/100000000000000000000 : ℝ) := by
    have hpowers : (1819/100000 : ℝ)^1089 ≤ (3958142654879/100000000000000000000 : ℝ)^256 := by
      have hnat : (1819 : ℕ)^1089*100000000000000000000^256 ≤ 3958142654879^256*100000^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1819 100000 3958142654879 100000000000000000000 1089 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1819/100000 : ℝ)) (X := (3958142654879/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hpowhi : (26481/100000 : ℝ) ^ (1089/256 : ℝ) ≤ (350927140811860553/100000000000000000000 : ℝ) := by
    have hpowers : (26481/100000 : ℝ)^1089 ≤ (350927140811860553/100000000000000000000 : ℝ)^256 := by
      have hnat : (26481 : ℕ)^1089*100000000000000000000^256 ≤ 350927140811860553^256*100000^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26481 100000 350927140811860553 100000000000000000000 1089 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26481/100000 : ℝ)) (X := (350927140811860553/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000003958142654879/50000000000000000000 : ℝ) ≤ (10000000186094489/10000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (50000003958142654879/50000000000000000000 : ℝ)^256 ≤ (10000000186094489/10000000000000000 : ℝ)^1089 := by
      have hnat : (50000003958142654879 : ℕ)^256*10000000000000000^1089 ≤ 10000000186094489^1089*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000003958142654879 50000000000000000000 10000000186094489 10000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000186094489/10000000000000000 : ℝ)) (X := (50000003958142654879/50000000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12543866387369314429/12500000000000000000 : ℝ) ≤ (5004119285165929/5000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (12543866387369314429/12500000000000000000 : ℝ)^256 ≤ (5004119285165929/5000000000000000 : ℝ)^1089 := by
      have hnat : (12543866387369314429 : ℕ)^256*5000000000000000^1089 ≤ 5004119285165929^1089*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12543866387369314429 12500000000000000000 5004119285165929 5000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004119285165929/5000000000000000 : ℝ)) (X := (12543866387369314429/12500000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50350927140811860553/50000000000000000000 : ℝ) ≤ (10016476954569227/10000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (50350927140811860553/50000000000000000000 : ℝ)^256 ≤ (10016476954569227/10000000000000000 : ℝ)^1089 := by
      have hnat : (50350927140811860553 : ℕ)^256*10000000000000000^1089 ≤ 10016476954569227^1089*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50350927140811860553 50000000000000000000 10016476954569227 10000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10016476954569227/10000000000000000 : ℝ)) (X := (50350927140811860553/50000000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3958142654879/100000000000000000000 : ℝ) ≤ ((700539867464791873/700625000000000000 : ℝ)+2*(748944021579/224200000000000 : ℝ)*(1819/100000 : ℝ))^(1089/256 : ℝ) := by
    rw [show (700539867464791873/700625000000000000 : ℝ)+2*(748944021579/224200000000000 : ℝ)*(1819/100000 : ℝ)=(10000000186094489/10000000000000000 : ℝ) by norm_num, show 1+2*(3958142654879/100000000000000000000 : ℝ)=(50000003958142654879/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(350927140811860553/100000000000000000000 : ℝ)+(3958142654879/100000000000000000000 : ℝ) ≤ ((700539867464791873/700625000000000000 : ℝ)+(748944021579/224200000000000 : ℝ)*((26481/100000 : ℝ)+(1819/100000 : ℝ)))^(1089/256 : ℝ) := by
    rw [show (700539867464791873/700625000000000000 : ℝ)+(748944021579/224200000000000 : ℝ)*((26481/100000 : ℝ)+(1819/100000 : ℝ))=(5004119285165929/5000000000000000 : ℝ) by norm_num, show 1+(350927140811860553/100000000000000000000 : ℝ)+(3958142654879/100000000000000000000 : ℝ)=(12543866387369314429/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(350927140811860553/100000000000000000000 : ℝ) ≤ ((700539867464791873/700625000000000000 : ℝ)+2*(748944021579/224200000000000 : ℝ)*(26481/100000 : ℝ))^(1089/256 : ℝ) := by
    rw [show (700539867464791873/700625000000000000 : ℝ)+2*(748944021579/224200000000000 : ℝ)*(26481/100000 : ℝ)=(10016476954569227/10000000000000000 : ℝ) by norm_num, show 1+2*(350927140811860553/100000000000000000000 : ℝ)=(50350927140811860553/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (700539867464791873/700625000000000000 : ℝ)*(X 1 0+X 2 0)+(748944021579/224200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (1819/100000 : ℝ)) (hi := (26481/100000 : ℝ)) (c := (700539867464791873/700625000000000000 : ℝ)) (alpha := (748944021579/224200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (700539867464791873/700625000000000000 : ℝ)*(X 0 1+X 2 1)+(748944021579/224200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (1819/100000 : ℝ)) (hi := (26481/100000 : ℝ)) (c := (700539867464791873/700625000000000000 : ℝ)) (alpha := (748944021579/224200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (700539867464791873/700625000000000000 : ℝ)*(X 0 2+X 1 2)+(748944021579/224200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (1819/100000 : ℝ)) (hi := (26481/100000 : ℝ)) (c := (700539867464791873/700625000000000000 : ℝ)) (alpha := (748944021579/224200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-97699181/500000000 : ℝ)*X 0 0+(5618327449/10000000000 : ℝ)*X 0 1+(2532835301/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5400047729/10000000000 : ℝ)*X 1 0+(-2247559379/10000000000 : ℝ)*X 1 1+(2532835983/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1350012161/2500000000 : ℝ)*X 2 0+(2532835393/5000000000 : ℝ)*X 2 1+(-2247559697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4282435619/10000000000 : ℝ)*X 0 0+(372852619/1000000000 : ℝ)*X 0 1+(4910101247/10000000000 : ℝ)*X 0 2+(4282435619/10000000000 : ℝ)*X 1 0+(372852619/1000000000 : ℝ)*X 1 1+(4910101247/10000000000 : ℝ)*X 1 2+(4282435619/10000000000 : ℝ)*X 2 0+(372852619/1000000000 : ℝ)*X 2 1+(4910101247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-977214003/5000000000 : ℝ)*X 0 0+(1014463227/2000000000 : ℝ)*X 0 1+(2805783099/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628001847/5000000000 : ℝ)*X 1 0+(-1701665067/10000000000 : ℝ)*X 1 1+(561156617/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2628002093/5000000000 : ℝ)*X 2 0+(2805783291/5000000000 : ℝ)*X 2 1+(-53176993/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((53542341/125000000 : ℝ)*X 0 0+(4895893237/10000000000 : ℝ)*X 0 1+(467872447/1250000000 : ℝ)*X 0 2+(53542341/125000000 : ℝ)*X 1 0+(4895893237/10000000000 : ℝ)*X 1 1+(467872447/1250000000 : ℝ)*X 1 2+(53542341/125000000 : ℝ)*X 2 0+(4895893237/10000000000 : ℝ)*X 2 1+(467872447/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62038034813128266054699/11210000000000000000000000000 : ℝ) := by norm_num
    linear_combination (945773711/100000000000000 : ℝ)*(base19) + (1237596001/100000000000000 : ℝ)*(base23) + (66722381/50000000000000 : ℝ)*(upper3) + (3990127/50000000000000 : ℝ)*(upper4) + (52703011/100000000000000 : ℝ)*(upper5) + (1327898939259583/100000000000000 : ℝ)*(major0) + (1327898939259583/100000000000000 : ℝ)*(major1) + (1327898939259583/100000000000000 : ℝ)*(major2) + (1809451646954649/100000000000000 : ℝ)*(sp0) + (452365331671609/25000000000000 : ℝ)*(sp1) + (1809461034864147/100000000000000 : ℝ)*(sp2) + (846331261404143/100000000000000 : ℝ)*(sp3) + (10625505499/100000000000000 : ℝ)*(sp4) + (520022821/12500000000000 : ℝ)*(sp7) + (846335421586711/100000000000000 : ℝ)*(f.failure) + (452365568115037/25000000000000 : ℝ)*(f.sum) + (25446263990127/11210000000000000000000000000 : ℝ)*base65 + (59900491270795677/8757812500000000000000000000000 : ℝ)*base68 + (10222609633419479/17515625000000000000000000000000 : ℝ)*base70 + (113067082540768021/17515625000000000000000000000000 : ℝ)*base71 + (47169474474263/11210000000000000000000000000 : ℝ)*base74 + (105387492260393021/17515625000000000000000000000000 : ℝ)*base75 + (200719433485856979/17515625000000000000000000000000 : ℝ)*base78 + (26863833480016823/8757812500000000000000000000000 : ℝ)*base79 + (55733847265257/11210000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (22599831/5000000000000000000000 : ℝ)*base89 + (22599831/5000000000000000000000 : ℝ)*base91 + (22599831/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2311745463487887340147539/593750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (186087743/100000000000000 : ℝ)*(base1) + (1127967311/100000000000000 : ℝ)*(base19) + (701636487/50000000000000 : ℝ)*(base23) + (91403991/100000000000000 : ℝ)*(upper3) + (49459167/25000000000000 : ℝ)*(upper5) + (1360898436811321/100000000000000 : ℝ)*(major0) + (1360898436811321/100000000000000 : ℝ)*(major1) + (1360898436811321/100000000000000 : ℝ)*(major2) + (2692648381/50000000000000 : ℝ)*(sp1) + (4548418773/50000000000000 : ℝ)*(sp2) + (370885860523281/20000000000000 : ℝ)*(sp4) + (1854422603264589/100000000000000 : ℝ)*(sp5) + (1854418616418141/100000000000000 : ℝ)*(sp6) + (86736744122403/10000000000000 : ℝ)*(sp7) + (867367627311773/100000000000000 : ℝ)*(f.failure) + (927214558264331/50000000000000 : ℝ)*(f.sum) + (3972362832159/11210000000000000000000000000 : ℝ)*base65 + (63185378818297777/17515625000000000000000000000000 : ℝ)*base67 + (8138033154242413/4378906250000000000000000000000 : ℝ)*base69 + (32504343718844201/8757812500000000000000000000000 : ℝ)*base71 + (11116026368569/11210000000000000000000000000 : ℝ)*base73 + (8445103899945087/4378906250000000000000000000000 : ℝ)*base76 + (6139034454870981/2189453125000000000000000000000 : ℝ)*base78 + (123224801059906701/8757812500000000000000000000000 : ℝ)*base79 + (3409987040439/11210000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (15780067/5000000000000000000000 : ℝ)*base90 + (15780067/5000000000000000000000 : ℝ)*base92 + (15780067/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1397_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1819/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3691/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2383/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1397_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1397_s2_0 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1989574789/10000000000 : ℝ)*x 0 + (1366403191/2500000000 : ℝ)*x 1 + (207820659/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989574789/10000000000 : ℝ)^4357 ≤ (1211484548801/10000000000000 : ℝ)^3333 := by
    have hnat : (1989574789 : ℕ)^4357*10000000000000^3333 ≤ 1211484548801^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989574789 10000000000 1211484548801 10000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366403191/2500000000 : ℝ)^4357 ≤ (45397658731733/100000000000000 : ℝ)^3333 := by
    have hnat : (1366403191 : ℕ)^4357*100000000000000^3333 ≤ 45397658731733^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366403191 2500000000 45397658731733 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207820659/400000000 : ℝ)^4357 ≤ (1062187394053/2500000000000 : ℝ)^3333 := by
    have hnat : (207820659 : ℕ)^4357*2500000000000^3333 ≤ 1062187394053^3333*400000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207820659 400000000 1062187394053 2500000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1989574789/10000000000 : ℝ), (1366403191/2500000000 : ℝ), (207820659/400000000 : ℝ)] ![(1211484548801/10000000000000 : ℝ), (45397658731733/100000000000000 : ℝ), (1062187394053/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1989574789/10000000000 : ℝ)|^4357 ≤ (1211484548801/10000000000000 : ℝ)^3333
        have hw : |(-1989574789/10000000000 : ℝ)|=(1989574789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366403191/2500000000 : ℝ)|^4357 ≤ (45397658731733/100000000000000 : ℝ)^3333
        have hw : |(1366403191/2500000000 : ℝ)|=(1366403191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207820659/400000000 : ℝ)|^4357 ≤ (1062187394053/2500000000000 : ℝ)^3333
        have hw : |(207820659/400000000 : ℝ)|=(207820659/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s2_1 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362208141/10000000000 : ℝ)*x 0 + (-1064371211/5000000000 : ℝ)*x 1 + (103910329/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362208141/10000000000 : ℝ)^4357 ≤ (44278176487991/100000000000000 : ℝ)^3333 := by
    have hnat : (5362208141 : ℕ)^4357*100000000000000^3333 ≤ 44278176487991^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362208141 10000000000 44278176487991 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1064371211/5000000000 : ℝ)^4357 ≤ (13234327991857/100000000000000 : ℝ)^3333 := by
    have hnat : (1064371211 : ℕ)^4357*100000000000000^3333 ≤ 13234327991857^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064371211 5000000000 13234327991857 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103910329/200000000 : ℝ)^4357 ≤ (21243747747433/50000000000000 : ℝ)^3333 := by
    have hnat : (103910329 : ℕ)^4357*50000000000000^3333 ≤ 21243747747433^3333*200000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103910329 200000000 21243747747433 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362208141/10000000000 : ℝ), (-1064371211/5000000000 : ℝ), (103910329/200000000 : ℝ)] ![(44278176487991/100000000000000 : ℝ), (13234327991857/100000000000000 : ℝ), (21243747747433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362208141/10000000000 : ℝ)|^4357 ≤ (44278176487991/100000000000000 : ℝ)^3333
        have hw : |(5362208141/10000000000 : ℝ)|=(5362208141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1064371211/5000000000 : ℝ)|^4357 ≤ (13234327991857/100000000000000 : ℝ)^3333
        have hw : |(-1064371211/5000000000 : ℝ)|=(1064371211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103910329/200000000 : ℝ)|^4357 ≤ (21243747747433/50000000000000 : ℝ)^3333
        have hw : |(103910329/200000000 : ℝ)|=(103910329/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s2_2 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362207963/10000000000 : ℝ)*x 0 + (103910333/200000000 : ℝ)*x 1 + (-2128742397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362207963/10000000000 : ℝ)^4357 ≤ (44278174566589/100000000000000 : ℝ)^3333 := by
    have hnat : (5362207963 : ℕ)^4357*100000000000000^3333 ≤ 44278174566589^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362207963 10000000000 44278174566589 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103910333/200000000 : ℝ)^4357 ≤ (424874976329/1000000000000 : ℝ)^3333 := by
    have hnat : (103910333 : ℕ)^4357*1000000000000^3333 ≤ 424874976329^3333*200000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103910333 200000000 424874976329 1000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2128742397/10000000000 : ℝ)^4357 ≤ (13234327788681/100000000000000 : ℝ)^3333 := by
    have hnat : (2128742397 : ℕ)^4357*100000000000000^3333 ≤ 13234327788681^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128742397 10000000000 13234327788681 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362207963/10000000000 : ℝ), (103910333/200000000 : ℝ), (-2128742397/10000000000 : ℝ)] ![(44278174566589/100000000000000 : ℝ), (424874976329/1000000000000 : ℝ), (13234327788681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362207963/10000000000 : ℝ)|^4357 ≤ (44278174566589/100000000000000 : ℝ)^3333
        have hw : |(5362207963/10000000000 : ℝ)|=(5362207963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103910333/200000000 : ℝ)|^4357 ≤ (424874976329/1000000000000 : ℝ)^3333
        have hw : |(103910333/200000000 : ℝ)|=(103910333/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2128742397/10000000000 : ℝ)|^4357 ≤ (13234327788681/100000000000000 : ℝ)^3333
        have hw : |(-2128742397/10000000000 : ℝ)|=(2128742397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s2_3 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076869051/2500000000 : ℝ)*x 0 + (1006887641/2500000000 : ℝ)*x 1 + (4605015811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076869051/2500000000 : ℝ)^4357 ≤ (33254078679929/100000000000000 : ℝ)^3333 := by
    have hnat : (1076869051 : ℕ)^4357*100000000000000^3333 ≤ 33254078679929^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076869051 2500000000 33254078679929 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006887641/2500000000 : ℝ)^4357 ≤ (380721563937/1250000000000 : ℝ)^3333 := by
    have hnat : (1006887641 : ℕ)^4357*1250000000000^3333 ≤ 380721563937^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006887641 2500000000 380721563937 1250000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4605015811/10000000000 : ℝ)^4357 ≤ (1814409809547/5000000000000 : ℝ)^3333 := by
    have hnat : (4605015811 : ℕ)^4357*5000000000000^3333 ≤ 1814409809547^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4605015811 10000000000 1814409809547 5000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076869051/2500000000 : ℝ), (1006887641/2500000000 : ℝ), (4605015811/10000000000 : ℝ)] ![(33254078679929/100000000000000 : ℝ), (380721563937/1250000000000 : ℝ), (1814409809547/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076869051/2500000000 : ℝ)|^4357 ≤ (33254078679929/100000000000000 : ℝ)^3333
        have hw : |(1076869051/2500000000 : ℝ)|=(1076869051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1006887641/2500000000 : ℝ)|^4357 ≤ (380721563937/1250000000000 : ℝ)^3333
        have hw : |(1006887641/2500000000 : ℝ)|=(1006887641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4605015811/10000000000 : ℝ)|^4357 ≤ (1814409809547/5000000000000 : ℝ)^3333
        have hw : |(4605015811/10000000000 : ℝ)|=(4605015811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s2_4 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1989626427/10000000000 : ℝ)*x 0 + (1039422661/2000000000 : ℝ)*x 1 + (2732001301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1989626427/10000000000 : ℝ)^4357 ≤ (1211525652509/10000000000000 : ℝ)^3333 := by
    have hnat : (1989626427 : ℕ)^4357*10000000000000^3333 ≤ 1211525652509^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989626427 10000000000 1211525652509 10000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039422661/2000000000 : ℝ)^4357 ≤ (42504566953849/100000000000000 : ℝ)^3333 := by
    have hnat : (1039422661 : ℕ)^4357*100000000000000^3333 ≤ 42504566953849^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039422661 2000000000 42504566953849 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2732001301/5000000000 : ℝ)^4357 ≤ (9076035300903/20000000000000 : ℝ)^3333 := by
    have hnat : (2732001301 : ℕ)^4357*20000000000000^3333 ≤ 9076035300903^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732001301 5000000000 9076035300903 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1989626427/10000000000 : ℝ), (1039422661/2000000000 : ℝ), (2732001301/5000000000 : ℝ)] ![(1211525652509/10000000000000 : ℝ), (42504566953849/100000000000000 : ℝ), (9076035300903/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1989626427/10000000000 : ℝ)|^4357 ≤ (1211525652509/10000000000000 : ℝ)^3333
        have hw : |(-1989626427/10000000000 : ℝ)|=(1989626427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1039422661/2000000000 : ℝ)|^4357 ≤ (42504566953849/100000000000000 : ℝ)^3333
        have hw : |(1039422661/2000000000 : ℝ)|=(1039422661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2732001301/5000000000 : ℝ)|^4357 ≤ (9076035300903/20000000000000 : ℝ)^3333
        have hw : |(2732001301/5000000000 : ℝ)|=(2732001301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s2_5 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646095653/5000000000 : ℝ)*x 0 + (-372051377/2000000000 : ℝ)*x 1 + (2732001149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646095653/5000000000 : ℝ)^4357 ≤ (43523907694591/100000000000000 : ℝ)^3333 := by
    have hnat : (2646095653 : ℕ)^4357*100000000000000^3333 ≤ 43523907694591^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646095653 5000000000 43523907694591 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (372051377/2000000000 : ℝ)^4357 ≤ (11095919078789/100000000000000 : ℝ)^3333 := by
    have hnat : (372051377 : ℕ)^4357*100000000000000^3333 ≤ 11095919078789^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372051377 2000000000 11095919078789 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2732001149/5000000000 : ℝ)^4357 ≤ (9076034640801/20000000000000 : ℝ)^3333 := by
    have hnat : (2732001149 : ℕ)^4357*20000000000000^3333 ≤ 9076034640801^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732001149 5000000000 9076034640801 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646095653/5000000000 : ℝ), (-372051377/2000000000 : ℝ), (2732001149/5000000000 : ℝ)] ![(43523907694591/100000000000000 : ℝ), (11095919078789/100000000000000 : ℝ), (9076034640801/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646095653/5000000000 : ℝ)|^4357 ≤ (43523907694591/100000000000000 : ℝ)^3333
        have hw : |(2646095653/5000000000 : ℝ)|=(2646095653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-372051377/2000000000 : ℝ)|^4357 ≤ (11095919078789/100000000000000 : ℝ)^3333
        have hw : |(-372051377/2000000000 : ℝ)|=(372051377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2732001149/5000000000 : ℝ)|^4357 ≤ (9076034640801/20000000000000 : ℝ)^3333
        have hw : |(2732001149/5000000000 : ℝ)|=(2732001149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s2_6 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5292192723/10000000000 : ℝ)*x 0 + (341500143/625000000 : ℝ)*x 1 + (-930127473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292192723/10000000000 : ℝ)^4357 ≤ (43523922928609/100000000000000 : ℝ)^3333 := by
    have hnat : (5292192723 : ℕ)^4357*100000000000000^3333 ≤ 43523922928609^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292192723 10000000000 43523922928609 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341500143/625000000 : ℝ)^4357 ≤ (11345043273859/25000000000000 : ℝ)^3333 := by
    have hnat : (341500143 : ℕ)^4357*25000000000000^3333 ≤ 11345043273859^3333*625000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341500143 625000000 11345043273859 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (930127473/5000000000 : ℝ)^4357 ≤ (11095903959883/100000000000000 : ℝ)^3333 := by
    have hnat : (930127473 : ℕ)^4357*100000000000000^3333 ≤ 11095903959883^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      930127473 5000000000 11095903959883 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292192723/10000000000 : ℝ), (341500143/625000000 : ℝ), (-930127473/5000000000 : ℝ)] ![(43523922928609/100000000000000 : ℝ), (11345043273859/25000000000000 : ℝ), (11095903959883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292192723/10000000000 : ℝ)|^4357 ≤ (43523922928609/100000000000000 : ℝ)^3333
        have hw : |(5292192723/10000000000 : ℝ)|=(5292192723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341500143/625000000 : ℝ)|^4357 ≤ (11345043273859/25000000000000 : ℝ)^3333
        have hw : |(341500143/625000000 : ℝ)|=(341500143/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-930127473/5000000000 : ℝ)|^4357 ≤ (11095903959883/100000000000000 : ℝ)^3333
        have hw : |(-930127473/5000000000 : ℝ)|=(930127473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s2_7 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4307587943/10000000000 : ℝ)*x 0 + (4601602309/10000000000 : ℝ)*x 1 + (1007748147/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307587943/10000000000 : ℝ)^4357 ≤ (16627603173359/50000000000000 : ℝ)^3333 := by
    have hnat : (4307587943 : ℕ)^4357*50000000000000^3333 ≤ 16627603173359^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307587943 10000000000 16627603173359 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4601602309/10000000000 : ℝ)^4357 ≤ (9063259283869/25000000000000 : ℝ)^3333 := by
    have hnat : (4601602309 : ℕ)^4357*25000000000000^3333 ≤ 9063259283869^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4601602309 10000000000 9063259283869 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007748147/2500000000 : ℝ)^4357 ≤ (15245878249113/50000000000000 : ℝ)^3333 := by
    have hnat : (1007748147 : ℕ)^4357*50000000000000^3333 ≤ 15245878249113^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007748147 2500000000 15245878249113 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307587943/10000000000 : ℝ), (4601602309/10000000000 : ℝ), (1007748147/2500000000 : ℝ)] ![(16627603173359/50000000000000 : ℝ), (9063259283869/25000000000000 : ℝ), (15245878249113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307587943/10000000000 : ℝ)|^4357 ≤ (16627603173359/50000000000000 : ℝ)^3333
        have hw : |(4307587943/10000000000 : ℝ)|=(4307587943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4601602309/10000000000 : ℝ)|^4357 ≤ (9063259283869/25000000000000 : ℝ)^3333
        have hw : |(4601602309/10000000000 : ℝ)|=(4601602309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1007748147/2500000000 : ℝ)|^4357 ≤ (15245878249113/50000000000000 : ℝ)^3333
        have hw : |(1007748147/2500000000 : ℝ)|=(1007748147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1397_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2383/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3691/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1019/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15903/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2383/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3691/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2383/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3691/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2383/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3691/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2383/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3691/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2383/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3691/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2383/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3691/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3691/50000 : ℝ) ^ (1089/256 : ℝ) ≤ (1532210656413239/100000000000000000000 : ℝ) := by
    have hpowers : (3691/50000 : ℝ)^1089 ≤ (1532210656413239/100000000000000000000 : ℝ)^256 := by
      have hnat : (3691 : ℕ)^1089*100000000000000000000^256 ≤ 1532210656413239^256*50000^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3691 50000 1532210656413239 100000000000000000000 1089 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3691/50000 : ℝ)) (X := (1532210656413239/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2383/12500 : ℝ) ^ (1089/256 : ℝ) ≤ (10839468153557937/12500000000000000000 : ℝ) := by
    have hpowers : (2383/12500 : ℝ)^1089 ≤ (10839468153557937/12500000000000000000 : ℝ)^256 := by
      have hnat : (2383 : ℕ)^1089*12500000000000000000^256 ≤ 10839468153557937^256*12500^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2383 12500 10839468153557937 12500000000000000000 1089 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2383/12500 : ℝ)) (X := (10839468153557937/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001532210656413239/50000000000000000000 : ℝ) ≤ (625004502310961/625000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (50001532210656413239/50000000000000000000 : ℝ)^256 ≤ (625004502310961/625000000000000 : ℝ)^1089 := by
      have hnat : (50001532210656413239 : ℕ)^256*625000000000000^1089 ≤ 625004502310961^1089*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001532210656413239 50000000000000000000 625004502310961 625000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625004502310961/625000000000000 : ℝ)) (X := (50001532210656413239/50000000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20017649591176975347/20000000000000000000 : ℝ) ≤ (1250259226994069/1250000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (20017649591176975347/20000000000000000000 : ℝ)^256 ≤ (1250259226994069/1250000000000000 : ℝ)^1089 := by
      have hnat : (20017649591176975347 : ℕ)^256*1250000000000000^1089 ≤ 1250259226994069^1089*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20017649591176975347 20000000000000000000 1250259226994069 1250000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250259226994069/1250000000000000 : ℝ)) (X := (20017649591176975347/20000000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6260839468153557937/6250000000000000000 : ℝ) ≤ (156313681170777/156250000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (6260839468153557937/6250000000000000000 : ℝ)^256 ≤ (156313681170777/156250000000000 : ℝ)^1089 := by
      have hnat : (6260839468153557937 : ℕ)^256*156250000000000^1089 ≤ 156313681170777^1089*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6260839468153557937 6250000000000000000 156313681170777 156250000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156313681170777/156250000000000 : ℝ)) (X := (6260839468153557937/6250000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1532210656413239/100000000000000000000 : ℝ) ≤ ((20737089359220049/20742187500000000 : ℝ)+2*(22747488377/13275000000000 : ℝ)*(3691/50000 : ℝ))^(1089/256 : ℝ) := by
    rw [show (20737089359220049/20742187500000000 : ℝ)+2*(22747488377/13275000000000 : ℝ)*(3691/50000 : ℝ)=(625004502310961/625000000000000 : ℝ) by norm_num, show 1+2*(1532210656413239/100000000000000000000 : ℝ)=(50001532210656413239/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10839468153557937/12500000000000000000 : ℝ)+(1532210656413239/100000000000000000000 : ℝ) ≤ ((20737089359220049/20742187500000000 : ℝ)+(22747488377/13275000000000 : ℝ)*((2383/12500 : ℝ)+(3691/50000 : ℝ)))^(1089/256 : ℝ) := by
    rw [show (20737089359220049/20742187500000000 : ℝ)+(22747488377/13275000000000 : ℝ)*((2383/12500 : ℝ)+(3691/50000 : ℝ))=(1250259226994069/1250000000000000 : ℝ) by norm_num, show 1+(10839468153557937/12500000000000000000 : ℝ)+(1532210656413239/100000000000000000000 : ℝ)=(20017649591176975347/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10839468153557937/12500000000000000000 : ℝ) ≤ ((20737089359220049/20742187500000000 : ℝ)+2*(22747488377/13275000000000 : ℝ)*(2383/12500 : ℝ))^(1089/256 : ℝ) := by
    rw [show (20737089359220049/20742187500000000 : ℝ)+2*(22747488377/13275000000000 : ℝ)*(2383/12500 : ℝ)=(156313681170777/156250000000000 : ℝ) by norm_num, show 1+2*(10839468153557937/12500000000000000000 : ℝ)=(6260839468153557937/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (20737089359220049/20742187500000000 : ℝ)*(X 1 0+X 2 0)+(22747488377/13275000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (3691/50000 : ℝ)) (hi := (2383/12500 : ℝ)) (c := (20737089359220049/20742187500000000 : ℝ)) (alpha := (22747488377/13275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (20737089359220049/20742187500000000 : ℝ)*(X 0 1+X 2 1)+(22747488377/13275000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (3691/50000 : ℝ)) (hi := (2383/12500 : ℝ)) (c := (20737089359220049/20742187500000000 : ℝ)) (alpha := (22747488377/13275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (20737089359220049/20742187500000000 : ℝ)*(X 0 2+X 1 2)+(22747488377/13275000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (3691/50000 : ℝ)) (hi := (2383/12500 : ℝ)) (c := (20737089359220049/20742187500000000 : ℝ)) (alpha := (22747488377/13275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1989574789/10000000000 : ℝ)*X 0 0+(1366403191/2500000000 : ℝ)*X 0 1+(207820659/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5362208141/10000000000 : ℝ)*X 1 0+(-1064371211/5000000000 : ℝ)*X 1 1+(103910329/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5362207963/10000000000 : ℝ)*X 2 0+(103910333/200000000 : ℝ)*X 2 1+(-2128742397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1076869051/2500000000 : ℝ)*X 0 0+(1006887641/2500000000 : ℝ)*X 0 1+(4605015811/10000000000 : ℝ)*X 0 2+(1076869051/2500000000 : ℝ)*X 1 0+(1006887641/2500000000 : ℝ)*X 1 1+(4605015811/10000000000 : ℝ)*X 1 2+(1076869051/2500000000 : ℝ)*X 2 0+(1006887641/2500000000 : ℝ)*X 2 1+(4605015811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1989626427/10000000000 : ℝ)*X 0 0+(1039422661/2000000000 : ℝ)*X 0 1+(2732001301/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646095653/5000000000 : ℝ)*X 1 0+(-372051377/2000000000 : ℝ)*X 1 1+(2732001149/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5292192723/10000000000 : ℝ)*X 2 0+(341500143/625000000 : ℝ)*X 2 1+(-930127473/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4307587943/10000000000 : ℝ)*X 0 0+(4601602309/10000000000 : ℝ)*X 0 1+(1007748147/2500000000 : ℝ)*X 0 2+(4307587943/10000000000 : ℝ)*X 1 0+(4601602309/10000000000 : ℝ)*X 1 1+(1007748147/2500000000 : ℝ)*X 1 2+(4307587943/10000000000 : ℝ)*X 2 0+(4601602309/10000000000 : ℝ)*X 2 1+(1007748147/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7616333538323357554208389/1382812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (113905027/12500000000000 : ℝ)*(base19) + (8266521/1250000000000 : ℝ)*(base23) + (68108737/100000000000000 : ℝ)*(lower2) + (87920311/50000000000000 : ℝ)*(upper3) + (3544533/5000000000000 : ℝ)*(upper5) + (339632557568101/12500000000000 : ℝ)*(major0) + (339632557568101/12500000000000 : ℝ)*(major1) + (339632557568101/12500000000000 : ℝ)*(major2) + (3702394819994351/100000000000000 : ℝ)*(sp0) + (185120166052769/5000000000000 : ℝ)*(sp1) + (925600892743479/25000000000000 : ℝ)*(sp2) + (865855330553229/50000000000000 : ℝ)*(sp3) + (1882460249/20000000000000 : ℝ)*(sp4) + (2922046161/50000000000000 : ℝ)*(sp7) + (86585825259939/5000000000000 : ℝ)*(f.failure) + (925601058073899/25000000000000 : ℝ)*(f.sum) + (1678727876189/663750000000000000000000000 : ℝ)*base66 + (18221907919635581/2765625000000000000000000000000 : ℝ)*base67 + (3447356601145669/2765625000000000000000000000000 : ℝ)*base70 + (10978203071200603/1382812500000000000000000000000 : ℝ)*base71 + (457509863357/1327500000000000000000000000 : ℝ)*base73 + (5694102988919353/1382812500000000000000000000000 : ℝ)*base75 + (7254780559825603/1382812500000000000000000000000 : ℝ)*base77 + (10490115128200603/1382812500000000000000000000000 : ℝ)*base79 + (5323243768723/1327500000000000000000000000 : ℝ)*base82 + (985181/250000000000000000000 : ℝ)*base90 + (985181/250000000000000000000 : ℝ)*base92 + (985181/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (342933363636833519383777/36875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (684324907/50000000000000 : ℝ)*(base19) + (3539778303/100000000000000 : ℝ)*(base23) + (277970679/100000000000000 : ℝ)*(upper3) + (327953253/100000000000000 : ℝ)*(lower4) + (53875709/50000000000000 : ℝ)*(upper5) + (54993853540047/2000000000000 : ℝ)*(major0) + (54993853540047/2000000000000 : ℝ)*(major1) + (54993853540047/2000000000000 : ℝ)*(major2) + (8527216723/100000000000000 : ℝ)*(sp1) + (3122742579/6250000000000 : ℝ)*(sp2) + (1873435209711209/50000000000000 : ℝ)*(sp4) + (3746860523555881/100000000000000 : ℝ)*(sp5) + (3746816915762851/100000000000000 : ℝ)*(sp6) + (876257312293007/50000000000000 : ℝ)*(sp7) + (876257312293007/50000000000000 : ℝ)*(f.failure) + (1873435209711209/50000000000000 : ℝ)*(f.sum) + (93075795047/44250000000000000000000000 : ℝ)*base65 + (32234436478359/9218750000000000000000000000 : ℝ)*base67 + (8906692515371/2304687500000000000000000000 : ℝ)*base69 + (44156076547811/36875000000000000000000000000 : ℝ)*base71 + (17035216169/7080000000000000000000000 : ℝ)*base73 + (29285410863359/9218750000000000000000000000 : ℝ)*base75 + (173663806182811/36875000000000000000000000000 : ℝ)*base77 + (103899730868593/18437500000000000000000000000 : ℝ)*base79 + (23780557493/88500000000000000000000000 : ℝ)*base82 + (21997553/2500000000000000000000 : ℝ)*base90 + (21997553/2500000000000000000000 : ℝ)*base92 + (21997553/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1397_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2383/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3691/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1019/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15903/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1397_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1397_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1019/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15903/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1397_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1397_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1397_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1019/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15903/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1397_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

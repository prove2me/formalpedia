-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1416_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:50:11.993162+00:00
-- url     : https://prove2.me/submissions/9ef8ba19-c54e-48d0-8def-1901f84d7aec

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
theorem support_rectangle_w1416_s6_0 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-123857781/625000000 : ℝ)*x 0 + (2704448347/5000000000 : ℝ)*x 1 + (655825369/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (123857781/625000000 : ℝ)^547 ≤ (3021604073973/25000000000000 : ℝ)^419 := by
    have hnat : (123857781 : ℕ)^547*25000000000000^419 ≤ 3021604073973^419*625000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123857781 625000000 3021604073973 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2704448347/5000000000 : ℝ)^547 ≤ (44830776066067/100000000000000 : ℝ)^419 := by
    have hnat : (2704448347 : ℕ)^547*100000000000000^419 ≤ 44830776066067^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704448347 5000000000 44830776066067 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655825369/1250000000 : ℝ)^547 ≤ (8616561523363/20000000000000 : ℝ)^419 := by
    have hnat : (655825369 : ℕ)^547*20000000000000^419 ≤ 8616561523363^419*1250000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655825369 1250000000 8616561523363 20000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-123857781/625000000 : ℝ), (2704448347/5000000000 : ℝ), (655825369/1250000000 : ℝ)] ![(3021604073973/25000000000000 : ℝ), (44830776066067/100000000000000 : ℝ), (8616561523363/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-123857781/625000000 : ℝ)|^547 ≤ (3021604073973/25000000000000 : ℝ)^419
        have hw : |(-123857781/625000000 : ℝ)|=(123857781/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2704448347/5000000000 : ℝ)|^547 ≤ (44830776066067/100000000000000 : ℝ)^419
        have hw : |(2704448347/5000000000 : ℝ)|=(2704448347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655825369/1250000000 : ℝ)|^547 ≤ (8616561523363/20000000000000 : ℝ)^419
        have hw : |(655825369/1250000000 : ℝ)|=(655825369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s6_1 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5347599711/10000000000 : ℝ)*x 0 + (-2064359851/10000000000 : ℝ)*x 1 + (5246603069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347599711/10000000000 : ℝ)^547 ≤ (5521084129821/12500000000000 : ℝ)^419 := by
    have hnat : (5347599711 : ℕ)^547*12500000000000^419 ≤ 5521084129821^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347599711 10000000000 5521084129821 12500000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064359851/10000000000 : ℝ)^547 ≤ (398391189879/3125000000000 : ℝ)^419 := by
    have hnat : (2064359851 : ℕ)^547*3125000000000^419 ≤ 398391189879^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064359851 10000000000 398391189879 3125000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246603069/10000000000 : ℝ)^547 ≤ (43082808871067/100000000000000 : ℝ)^419 := by
    have hnat : (5246603069 : ℕ)^547*100000000000000^419 ≤ 43082808871067^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246603069 10000000000 43082808871067 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347599711/10000000000 : ℝ), (-2064359851/10000000000 : ℝ), (5246603069/10000000000 : ℝ)] ![(5521084129821/12500000000000 : ℝ), (398391189879/3125000000000 : ℝ), (43082808871067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347599711/10000000000 : ℝ)|^547 ≤ (5521084129821/12500000000000 : ℝ)^419
        have hw : |(5347599711/10000000000 : ℝ)|=(5347599711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2064359851/10000000000 : ℝ)|^547 ≤ (398391189879/3125000000000 : ℝ)^419
        have hw : |(-2064359851/10000000000 : ℝ)|=(2064359851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246603069/10000000000 : ℝ)|^547 ≤ (43082808871067/100000000000000 : ℝ)^419
        have hw : |(5246603069/10000000000 : ℝ)|=(5246603069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s6_2 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5347599551/10000000000 : ℝ)*x 0 + (5246603093/10000000000 : ℝ)*x 1 + (-2064360033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347599551/10000000000 : ℝ)^547 ≤ (44168671313331/100000000000000 : ℝ)^419 := by
    have hnat : (5347599551 : ℕ)^547*100000000000000^419 ≤ 44168671313331^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347599551 10000000000 44168671313331 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246603093/10000000000 : ℝ)^547 ≤ (861656182567/2000000000000 : ℝ)^419 := by
    have hnat : (5246603093 : ℕ)^547*2000000000000^419 ≤ 861656182567^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246603093 10000000000 861656182567 2000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2064360033/10000000000 : ℝ)^547 ≤ (3187129885857/25000000000000 : ℝ)^419 := by
    have hnat : (2064360033 : ℕ)^547*25000000000000^419 ≤ 3187129885857^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064360033 10000000000 3187129885857 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347599551/10000000000 : ℝ), (5246603093/10000000000 : ℝ), (-2064360033/10000000000 : ℝ)] ![(44168671313331/100000000000000 : ℝ), (861656182567/2000000000000 : ℝ), (3187129885857/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347599551/10000000000 : ℝ)|^547 ≤ (44168671313331/100000000000000 : ℝ)^419
        have hw : |(5347599551/10000000000 : ℝ)|=(5347599551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246603093/10000000000 : ℝ)|^547 ≤ (861656182567/2000000000000 : ℝ)^419
        have hw : |(5246603093/10000000000 : ℝ)|=(5246603093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2064360033/10000000000 : ℝ)|^547 ≤ (3187129885857/25000000000000 : ℝ)^419
        have hw : |(-2064360033/10000000000 : ℝ)|=(2064360033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s6_3 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4307634131/10000000000 : ℝ)*x 0 + (413612753/1000000000 : ℝ)*x 1 + (4485551123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307634131/10000000000 : ℝ)^547 ≤ (33304482813413/100000000000000 : ℝ)^419 := by
    have hnat : (4307634131 : ℕ)^547*100000000000000^419 ≤ 33304482813413^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307634131 10000000000 33304482813413 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (413612753/1000000000 : ℝ)^547 ≤ (493500398363/1562500000000 : ℝ)^419 := by
    have hnat : (413612753 : ℕ)^547*1562500000000^419 ≤ 493500398363^419*1000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413612753 1000000000 493500398363 1562500000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4485551123/10000000000 : ℝ)^547 ≤ (35111491679349/100000000000000 : ℝ)^419 := by
    have hnat : (4485551123 : ℕ)^547*100000000000000^419 ≤ 35111491679349^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485551123 10000000000 35111491679349 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307634131/10000000000 : ℝ), (413612753/1000000000 : ℝ), (4485551123/10000000000 : ℝ)] ![(33304482813413/100000000000000 : ℝ), (493500398363/1562500000000 : ℝ), (35111491679349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307634131/10000000000 : ℝ)|^547 ≤ (33304482813413/100000000000000 : ℝ)^419
        have hw : |(4307634131/10000000000 : ℝ)|=(4307634131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(413612753/1000000000 : ℝ)|^547 ≤ (493500398363/1562500000000 : ℝ)^419
        have hw : |(413612753/1000000000 : ℝ)|=(413612753/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4485551123/10000000000 : ℝ)|^547 ≤ (35111491679349/100000000000000 : ℝ)^419
        have hw : |(4485551123/10000000000 : ℝ)|=(4485551123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s6_4 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1981735951/10000000000 : ℝ)*x 0 + (655898467/1250000000 : ℝ)*x 1 + (5408308879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1981735951/10000000000 : ℝ)^547 ≤ (12086507501817/100000000000000 : ℝ)^419 := by
    have hnat : (1981735951 : ℕ)^547*100000000000000^419 ≤ 12086507501817^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981735951 10000000000 12086507501817 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655898467/1250000000 : ℝ)^547 ≤ (1723563066813/4000000000000 : ℝ)^419 := by
    have hnat : (655898467 : ℕ)^547*4000000000000^419 ≤ 1723563066813^419*1250000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655898467 1250000000 1723563066813 4000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408308879/10000000000 : ℝ)^547 ≤ (4482441581399/10000000000000 : ℝ)^419 := by
    have hnat : (5408308879 : ℕ)^547*10000000000000^419 ≤ 4482441581399^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408308879 10000000000 4482441581399 10000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1981735951/10000000000 : ℝ), (655898467/1250000000 : ℝ), (5408308879/10000000000 : ℝ)] ![(12086507501817/100000000000000 : ℝ), (1723563066813/4000000000000 : ℝ), (4482441581399/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1981735951/10000000000 : ℝ)|^547 ≤ (12086507501817/100000000000000 : ℝ)^419
        have hw : |(-1981735951/10000000000 : ℝ)|=(1981735951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655898467/1250000000 : ℝ)|^547 ≤ (1723563066813/4000000000000 : ℝ)^419
        have hw : |(655898467/1250000000 : ℝ)|=(655898467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408308879/10000000000 : ℝ)|^547 ≤ (4482441581399/10000000000000 : ℝ)^419
        have hw : |(5408308879/10000000000 : ℝ)|=(5408308879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s6_5 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305462049/10000000000 : ℝ)*x 0 + (-1902654027/10000000000 : ℝ)*x 1 + (5408308879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305462049/10000000000 : ℝ)^547 ≤ (43714861832883/100000000000000 : ℝ)^419 := by
    have hnat : (5305462049 : ℕ)^547*100000000000000^419 ≤ 43714861832883^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305462049 10000000000 43714861832883 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1902654027/10000000000 : ℝ)^547 ≤ (1432590291421/12500000000000 : ℝ)^419 := by
    have hnat : (1902654027 : ℕ)^547*12500000000000^419 ≤ 1432590291421^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902654027 10000000000 1432590291421 12500000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408308879/10000000000 : ℝ)^547 ≤ (4482441581399/10000000000000 : ℝ)^419 := by
    have hnat : (5408308879 : ℕ)^547*10000000000000^419 ≤ 4482441581399^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408308879 10000000000 4482441581399 10000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305462049/10000000000 : ℝ), (-1902654027/10000000000 : ℝ), (5408308879/10000000000 : ℝ)] ![(43714861832883/100000000000000 : ℝ), (1432590291421/12500000000000 : ℝ), (4482441581399/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305462049/10000000000 : ℝ)|^547 ≤ (43714861832883/100000000000000 : ℝ)^419
        have hw : |(5305462049/10000000000 : ℝ)|=(5305462049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1902654027/10000000000 : ℝ)|^547 ≤ (1432590291421/12500000000000 : ℝ)^419
        have hw : |(-1902654027/10000000000 : ℝ)|=(1902654027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408308879/10000000000 : ℝ)|^547 ≤ (4482441581399/10000000000000 : ℝ)^419
        have hw : |(5408308879/10000000000 : ℝ)|=(5408308879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s6_6 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1061092409/2000000000 : ℝ)*x 0 + (1352077221/2500000000 : ℝ)*x 1 + (-1902654027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061092409/2000000000 : ℝ)^547 ≤ (1366089430933/3125000000000 : ℝ)^419 := by
    have hnat : (1061092409 : ℕ)^547*3125000000000^419 ≤ 1366089430933^419*2000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061092409 2000000000 1366089430933 3125000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352077221/2500000000 : ℝ)^547 ≤ (4482441586809/10000000000000 : ℝ)^419 := by
    have hnat : (1352077221 : ℕ)^547*10000000000000^419 ≤ 4482441586809^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352077221 2500000000 4482441586809 10000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1902654027/10000000000 : ℝ)^547 ≤ (1432590291421/12500000000000 : ℝ)^419 := by
    have hnat : (1902654027 : ℕ)^547*12500000000000^419 ≤ 1432590291421^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902654027 10000000000 1432590291421 12500000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061092409/2000000000 : ℝ), (1352077221/2500000000 : ℝ), (-1902654027/10000000000 : ℝ)] ![(1366089430933/3125000000000 : ℝ), (4482441586809/10000000000000 : ℝ), (1432590291421/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061092409/2000000000 : ℝ)|^547 ≤ (1366089430933/3125000000000 : ℝ)^419
        have hw : |(1061092409/2000000000 : ℝ)|=(1061092409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352077221/2500000000 : ℝ)|^547 ≤ (4482441586809/10000000000000 : ℝ)^419
        have hw : |(1352077221/2500000000 : ℝ)|=(1352077221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1902654027/10000000000 : ℝ)|^547 ≤ (1432590291421/12500000000000 : ℝ)^419
        have hw : |(-1902654027/10000000000 : ℝ)|=(1902654027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s6_7 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4307658923/10000000000 : ℝ)*x 0 + (4484292221/10000000000 : ℝ)*x 1 + (827478559/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307658923/10000000000 : ℝ)^547 ≤ (6660946609807/20000000000000 : ℝ)^419 := by
    have hnat : (4307658923 : ℕ)^547*20000000000000^419 ≤ 6660946609807^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307658923 10000000000 6660946609807 20000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484292221/10000000000 : ℝ)^547 ≤ (3509862755951/10000000000000 : ℝ)^419 := by
    have hnat : (4484292221 : ℕ)^547*10000000000000^419 ≤ 3509862755951^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484292221 10000000000 3509862755951 10000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (827478559/2000000000 : ℝ)^547 ≤ (15798319686951/50000000000000 : ℝ)^419 := by
    have hnat : (827478559 : ℕ)^547*50000000000000^419 ≤ 15798319686951^419*2000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827478559 2000000000 15798319686951 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307658923/10000000000 : ℝ), (4484292221/10000000000 : ℝ), (827478559/2000000000 : ℝ)] ![(6660946609807/20000000000000 : ℝ), (3509862755951/10000000000000 : ℝ), (15798319686951/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307658923/10000000000 : ℝ)|^547 ≤ (6660946609807/20000000000000 : ℝ)^419
        have hw : |(4307658923/10000000000 : ℝ)|=(4307658923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484292221/10000000000 : ℝ)|^547 ≤ (3509862755951/10000000000000 : ℝ)^419
        have hw : |(4484292221/10000000000 : ℝ)|=(4484292221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(827478559/2000000000 : ℝ)|^547 ≤ (15798319686951/50000000000000 : ℝ)^419
        have hw : |(827478559/2000000000 : ℝ)|=(827478559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1416_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157651737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11313/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (59/400 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11309/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11309/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11309/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11309/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11309/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11309/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11309/100000 : ℝ) ^ (4375/1024 : ℝ) ≤ (1806433103165669/20000000000000000000 : ℝ) := by
    have hpowers : (11309/100000 : ℝ)^4375 ≤ (1806433103165669/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11309 : ℕ)^4375*20000000000000000000^1024 ≤ 1806433103165669^1024*100000^4375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11309 100000 1806433103165669 20000000000000000000 4375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11309/100000 : ℝ)) (X := (1806433103165669/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2951/20000 : ℝ) ^ (4375/1024 : ℝ) ≤ (14070037624008013/50000000000000000000 : ℝ) := by
    have hpowers : (2951/20000 : ℝ)^4375 ≤ (14070037624008013/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2951 : ℕ)^4375*50000000000000000000^1024 ≤ 14070037624008013^1024*20000^4375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2951 20000 14070037624008013 50000000000000000000 4375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2951/20000 : ℝ)) (X := (14070037624008013/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001806433103165669/10000000000000000000 : ℝ) ≤ (156256605926931/156250000000000 : ℝ) ^ (4375/1024 : ℝ) := by
    have hpowers : (10001806433103165669/10000000000000000000 : ℝ)^1024 ≤ (156256605926931/156250000000000 : ℝ)^4375 := by
      have hnat : (10001806433103165669 : ℕ)^1024*156250000000000^4375 ≤ 156256605926931^4375*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001806433103165669 10000000000000000000 156256605926931 156250000000000 1024 4375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156256605926931/156250000000000 : ℝ)) (X := (10001806433103165669/10000000000000000000 : ℝ)) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037172240763844371/100000000000000000000 : ℝ) ≤ (10000869919015291/10000000000000000 : ℝ) ^ (4375/1024 : ℝ) := by
    have hpowers : (100037172240763844371/100000000000000000000 : ℝ)^1024 ≤ (10000869919015291/10000000000000000 : ℝ)^4375 := by
      have hnat : (100037172240763844371 : ℕ)^1024*10000000000000000^4375 ≤ 10000869919015291^4375*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037172240763844371 100000000000000000000 10000869919015291 10000000000000000 1024 4375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000869919015291/10000000000000000 : ℝ)) (X := (100037172240763844371/100000000000000000000 : ℝ)) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014070037624008013/25000000000000000000 : ℝ) ≤ (5000658529353499/5000000000000000 : ℝ) ^ (4375/1024 : ℝ) := by
    have hpowers : (25014070037624008013/25000000000000000000 : ℝ)^1024 ≤ (5000658529353499/5000000000000000 : ℝ)^4375 := by
      have hnat : (25014070037624008013 : ℕ)^1024*5000000000000000^4375 ≤ 5000658529353499^4375*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014070037624008013 25000000000000000000 5000658529353499 5000000000000000 1024 4375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000658529353499/5000000000000000 : ℝ)) (X := (25014070037624008013/25000000000000000000 : ℝ)) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1806433103165669/20000000000000000000 : ℝ) ≤ ((17225671746001020769/17230000000000000000 : ℝ)+2*(447139691707/344600000000000 : ℝ)*(11309/100000 : ℝ))^(4375/1024 : ℝ) := by
    rw [show (17225671746001020769/17230000000000000000 : ℝ)+2*(447139691707/344600000000000 : ℝ)*(11309/100000 : ℝ)=(156256605926931/156250000000000 : ℝ) by norm_num, show 1+2*(1806433103165669/20000000000000000000 : ℝ)=(10001806433103165669/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14070037624008013/50000000000000000000 : ℝ)+(1806433103165669/20000000000000000000 : ℝ) ≤ ((17225671746001020769/17230000000000000000 : ℝ)+(447139691707/344600000000000 : ℝ)*((2951/20000 : ℝ)+(11309/100000 : ℝ)))^(4375/1024 : ℝ) := by
    rw [show (17225671746001020769/17230000000000000000 : ℝ)+(447139691707/344600000000000 : ℝ)*((2951/20000 : ℝ)+(11309/100000 : ℝ))=(10000869919015291/10000000000000000 : ℝ) by norm_num, show 1+(14070037624008013/50000000000000000000 : ℝ)+(1806433103165669/20000000000000000000 : ℝ)=(100037172240763844371/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14070037624008013/50000000000000000000 : ℝ) ≤ ((17225671746001020769/17230000000000000000 : ℝ)+2*(447139691707/344600000000000 : ℝ)*(2951/20000 : ℝ))^(4375/1024 : ℝ) := by
    rw [show (17225671746001020769/17230000000000000000 : ℝ)+2*(447139691707/344600000000000 : ℝ)*(2951/20000 : ℝ)=(5000658529353499/5000000000000000 : ℝ) by norm_num, show 1+2*(14070037624008013/50000000000000000000 : ℝ)=(25014070037624008013/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17225671746001020769/17230000000000000000 : ℝ)*(X 1 0+X 2 0)+(447139691707/344600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4375/1024 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (17225671746001020769/17230000000000000000 : ℝ)) (alpha := (447139691707/344600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17225671746001020769/17230000000000000000 : ℝ)*(X 0 1+X 2 1)+(447139691707/344600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4375/1024 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (17225671746001020769/17230000000000000000 : ℝ)) (alpha := (447139691707/344600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17225671746001020769/17230000000000000000 : ℝ)*(X 0 2+X 1 2)+(447139691707/344600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4375/1024 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (17225671746001020769/17230000000000000000 : ℝ)) (alpha := (447139691707/344600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-123857781/625000000 : ℝ)*X 0 0+(2704448347/5000000000 : ℝ)*X 0 1+(655825369/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347599711/10000000000 : ℝ)*X 1 0+(-2064359851/10000000000 : ℝ)*X 1 1+(5246603069/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347599551/10000000000 : ℝ)*X 2 0+(5246603093/10000000000 : ℝ)*X 2 1+(-2064360033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4307634131/10000000000 : ℝ)*X 0 0+(413612753/1000000000 : ℝ)*X 0 1+(4485551123/10000000000 : ℝ)*X 0 2+(4307634131/10000000000 : ℝ)*X 1 0+(413612753/1000000000 : ℝ)*X 1 1+(4485551123/10000000000 : ℝ)*X 1 2+(4307634131/10000000000 : ℝ)*X 2 0+(413612753/1000000000 : ℝ)*X 2 1+(4485551123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1981735951/10000000000 : ℝ)*X 0 0+(655898467/1250000000 : ℝ)*X 0 1+(5408308879/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305462049/10000000000 : ℝ)*X 1 0+(-1902654027/10000000000 : ℝ)*X 1 1+(5408308879/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061092409/2000000000 : ℝ)*X 2 0+(1352077221/2500000000 : ℝ)*X 2 1+(-1902654027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4307658923/10000000000 : ℝ)*X 0 0+(4484292221/10000000000 : ℝ)*X 0 1+(827478559/2000000000 : ℝ)*X 0 2+(4307658923/10000000000 : ℝ)*X 1 0+(4484292221/10000000000 : ℝ)*X 1 1+(827478559/2000000000 : ℝ)*X 1 2+(4307658923/10000000000 : ℝ)*X 2 0+(4484292221/10000000000 : ℝ)*X 2 1+(827478559/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (619450764345419335087572093/86150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (994286003/100000000000000 : ℝ)*(base19) + (835070851/100000000000000 : ℝ)*(base23) + (242695303/100000000000000 : ℝ)*(upper3) + (3379207/25000000000000 : ℝ)*(lower4) + (451179522060801/10000000000000 : ℝ)*(major0) + (451179522060801/10000000000000 : ℝ)*(major1) + (451179522060801/10000000000000 : ℝ)*(major2) + (616169679566931/10000000000000 : ℝ)*(sp0) + (3080857239260071/50000000000000 : ℝ)*(sp1) + (1540428655204557/25000000000000 : ℝ)*(sp2) + (357732989346537/12500000000000 : ℝ)*(sp3) + (3735427367/20000000000000 : ℝ)*(sp4) + (8458533/50000000000000 : ℝ)*(sp6) + (540697921/5000000000000 : ℝ)*(sp7) + (715468682182679/25000000000000 : ℝ)*(f.failure) + (24069201065649/390625000000 : ℝ)*(f.sum) + (7176820564993/861500000000000000000000000 : ℝ)*base66 + (109253840627125969/172300000000000000000000000000000 : ℝ)*base67 + (758970090733225969/172300000000000000000000000000000 : ℝ)*base69 + (1282537142728274031/172300000000000000000000000000000 : ℝ)*base72 + (2210277021027/1723000000000000000000000000 : ℝ)*base74 + (2498294703683325969/172300000000000000000000000000000 : ℝ)*base75 + (561340453111074031/172300000000000000000000000000000 : ℝ)*base78 + (630896079716725969/172300000000000000000000000000000 : ℝ)*base79 + (6359132044139/1723000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (45663423/2500000000000000000000 : ℝ)*base89 + (45663423/2500000000000000000000 : ℝ)*base91 + (45663423/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (611014471177641081319347681/215375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (486394297/100000000000000 : ℝ)*(base19) + (529941217/100000000000000 : ℝ)*(base23) + (165319897/100000000000000 : ℝ)*(lower1) + (29008673/50000000000000 : ℝ)*(upper3) + (42363/195312500000 : ℝ)*(lower4) + (7109331/12500000000000 : ℝ)*(upper5) + (2272293579131683/50000000000000 : ℝ)*(major0) + (2272293579131683/50000000000000 : ℝ)*(major1) + (2272293579131683/50000000000000 : ℝ)*(major2) + (924681891/100000000000000 : ℝ)*(sp2) + (1551624813625417/25000000000000 : ℝ)*(sp4) + (6206498768107371/100000000000000 : ℝ)*(sp5) + (38790611249241/625000000000 : ℝ)*(sp6) + (720668741864761/25000000000000 : ℝ)*(sp7) + (720668741864761/25000000000000 : ℝ)*(f.failure) + (1551624813625417/25000000000000 : ℝ)*(f.sum) + (14729680544321/8615000000000000000000000000 : ℝ)*base65 + (65139082083165025773/861500000000000000000000000000000 : ℝ)*base68 + (8840796060635025773/861500000000000000000000000000000 : ℝ)*base70 + (155764723122133525773/861500000000000000000000000000000 : ℝ)*base72 + (5652712929269/2153750000000000000000000000 : ℝ)*base73 + (38679598268139474227/861500000000000000000000000000000 : ℝ)*base75 + (2780434403896525773/861500000000000000000000000000000 : ℝ)*base78 + (8633014730847525773/861500000000000000000000000000000 : ℝ)*base80 + (15595776372087/4307500000000000000000000000 : ℝ)*base82 + (40739857/2500000000000000000000 : ℝ)*base89 + (40739857/2500000000000000000000 : ℝ)*base91 + (40739857/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1416_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157651737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (59/400 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1416_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1416_s7_0 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1981729999/10000000000 : ℝ)*x 0 + (5408862343/10000000000 : ℝ)*x 1 + (5246633537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1981729999/10000000000 : ℝ)^547 ≤ (6043230055671/50000000000000 : ℝ)^419 := by
    have hnat : (1981729999 : ℕ)^547*50000000000000^419 ≤ 6043230055671^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981729999 10000000000 6043230055671 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408862343/10000000000 : ℝ)^547 ≤ (22415202188479/50000000000000 : ℝ)^419 := by
    have hnat : (5408862343 : ℕ)^547*50000000000000^419 ≤ 22415202188479^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408862343 10000000000 22415202188479 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246633537/10000000000 : ℝ)^547 ≤ (8616627098313/20000000000000 : ℝ)^419 := by
    have hnat : (5246633537 : ℕ)^547*20000000000000^419 ≤ 8616627098313^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246633537 10000000000 8616627098313 20000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1981729999/10000000000 : ℝ), (5408862343/10000000000 : ℝ), (5246633537/10000000000 : ℝ)] ![(6043230055671/50000000000000 : ℝ), (22415202188479/50000000000000 : ℝ), (8616627098313/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1981729999/10000000000 : ℝ)|^547 ≤ (6043230055671/50000000000000 : ℝ)^419
        have hw : |(-1981729999/10000000000 : ℝ)|=(1981729999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408862343/10000000000 : ℝ)|^547 ≤ (22415202188479/50000000000000 : ℝ)^419
        have hw : |(5408862343/10000000000 : ℝ)|=(5408862343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246633537/10000000000 : ℝ)|^547 ≤ (8616627098313/20000000000000 : ℝ)^419
        have hw : |(5246633537/10000000000 : ℝ)|=(5246633537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s7_1 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5347590377/10000000000 : ℝ)*x 0 + (-2064331843/10000000000 : ℝ)*x 1 + (5246633521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347590377/10000000000 : ℝ)^547 ≤ (8833714478517/20000000000000 : ℝ)^419 := by
    have hnat : (5347590377 : ℕ)^547*20000000000000^419 ≤ 8833714478517^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347590377 10000000000 8833714478517 20000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064331843/10000000000 : ℝ)^547 ≤ (12748292273599/100000000000000 : ℝ)^419 := by
    have hnat : (2064331843 : ℕ)^547*100000000000000^419 ≤ 12748292273599^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064331843 10000000000 12748292273599 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246633521/10000000000 : ℝ)^547 ≤ (43083135320043/100000000000000 : ℝ)^419 := by
    have hnat : (5246633521 : ℕ)^547*100000000000000^419 ≤ 43083135320043^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246633521 10000000000 43083135320043 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347590377/10000000000 : ℝ), (-2064331843/10000000000 : ℝ), (5246633521/10000000000 : ℝ)] ![(8833714478517/20000000000000 : ℝ), (12748292273599/100000000000000 : ℝ), (43083135320043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347590377/10000000000 : ℝ)|^547 ≤ (8833714478517/20000000000000 : ℝ)^419
        have hw : |(5347590377/10000000000 : ℝ)|=(5347590377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2064331843/10000000000 : ℝ)|^547 ≤ (12748292273599/100000000000000 : ℝ)^419
        have hw : |(-2064331843/10000000000 : ℝ)|=(2064331843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246633521/10000000000 : ℝ)|^547 ≤ (43083135320043/100000000000000 : ℝ)^419
        have hw : |(5246633521/10000000000 : ℝ)|=(5246633521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s7_2 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2673795199/5000000000 : ℝ)*x 0 + (1311658377/2500000000 : ℝ)*x 1 + (-258041479/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673795199/5000000000 : ℝ)^547 ≤ (22084286309511/50000000000000 : ℝ)^419 := by
    have hnat : (2673795199 : ℕ)^547*50000000000000^419 ≤ 22084286309511^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673795199 5000000000 22084286309511 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311658377/2500000000 : ℝ)^547 ≤ (21541567590341/50000000000000 : ℝ)^419 := by
    have hnat : (1311658377 : ℕ)^547*50000000000000^419 ≤ 21541567590341^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311658377 2500000000 21541567590341 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258041479/1250000000 : ℝ)^547 ≤ (3187073046229/25000000000000 : ℝ)^419 := by
    have hnat : (258041479 : ℕ)^547*25000000000000^419 ≤ 3187073046229^419*1250000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258041479 1250000000 3187073046229 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673795199/5000000000 : ℝ), (1311658377/2500000000 : ℝ), (-258041479/1250000000 : ℝ)] ![(22084286309511/50000000000000 : ℝ), (21541567590341/50000000000000 : ℝ), (3187073046229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673795199/5000000000 : ℝ)|^547 ≤ (22084286309511/50000000000000 : ℝ)^419
        have hw : |(2673795199/5000000000 : ℝ)|=(2673795199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311658377/2500000000 : ℝ)|^547 ≤ (21541567590341/50000000000000 : ℝ)^419
        have hw : |(1311658377/2500000000 : ℝ)|=(1311658377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258041479/1250000000 : ℝ)|^547 ≤ (3187073046229/25000000000000 : ℝ)^419
        have hw : |(-258041479/1250000000 : ℝ)|=(258041479/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s7_3 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1076909137/2500000000 : ℝ)*x 0 + (517024603/1250000000 : ℝ)*x 1 + (280342571/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076909137/2500000000 : ℝ)^547 ≤ (33304507209147/100000000000000 : ℝ)^419 := by
    have hnat : (1076909137 : ℕ)^547*100000000000000^419 ≤ 33304507209147^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076909137 2500000000 33304507209147 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517024603/1250000000 : ℝ)^547 ≤ (31584716281359/100000000000000 : ℝ)^419 := by
    have hnat : (517024603 : ℕ)^547*100000000000000^419 ≤ 31584716281359^419*1250000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517024603 1250000000 31584716281359 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280342571/625000000 : ℝ)^547 ≤ (35110776486579/100000000000000 : ℝ)^419 := by
    have hnat : (280342571 : ℕ)^547*100000000000000^419 ≤ 35110776486579^419*625000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280342571 625000000 35110776486579 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076909137/2500000000 : ℝ), (517024603/1250000000 : ℝ), (280342571/625000000 : ℝ)] ![(33304507209147/100000000000000 : ℝ), (31584716281359/100000000000000 : ℝ), (35110776486579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076909137/2500000000 : ℝ)|^547 ≤ (33304507209147/100000000000000 : ℝ)^419
        have hw : |(1076909137/2500000000 : ℝ)|=(1076909137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517024603/1250000000 : ℝ)|^547 ≤ (31584716281359/100000000000000 : ℝ)^419
        have hw : |(517024603/1250000000 : ℝ)|=(517024603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280342571/625000000 : ℝ)|^547 ≤ (35110776486579/100000000000000 : ℝ)^419
        have hw : |(280342571/625000000 : ℝ)|=(280342571/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s7_4 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-990870973/5000000000 : ℝ)*x 0 + (5247217527/10000000000 : ℝ)*x 1 + (108165499/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (990870973/5000000000 : ℝ)^547 ≤ (12086555234707/100000000000000 : ℝ)^419 := by
    have hnat : (990870973 : ℕ)^547*100000000000000^419 ≤ 12086555234707^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990870973 5000000000 12086555234707 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247217527/10000000000 : ℝ)^547 ≤ (4308939604417/10000000000000 : ℝ)^419 := by
    have hnat : (5247217527 : ℕ)^547*10000000000000^419 ≤ 4308939604417^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247217527 10000000000 4308939604417 10000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108165499/200000000 : ℝ)^547 ≤ (44824048703243/100000000000000 : ℝ)^419 := by
    have hnat : (108165499 : ℕ)^547*100000000000000^419 ≤ 44824048703243^419*200000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108165499 200000000 44824048703243 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-990870973/5000000000 : ℝ), (5247217527/10000000000 : ℝ), (108165499/200000000 : ℝ)] ![(12086555234707/100000000000000 : ℝ), (4308939604417/10000000000000 : ℝ), (44824048703243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-990870973/5000000000 : ℝ)|^547 ≤ (12086555234707/100000000000000 : ℝ)^419
        have hw : |(-990870973/5000000000 : ℝ)|=(990870973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247217527/10000000000 : ℝ)|^547 ≤ (4308939604417/10000000000000 : ℝ)^419
        have hw : |(5247217527/10000000000 : ℝ)|=(5247217527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108165499/200000000 : ℝ)|^547 ≤ (44824048703243/100000000000000 : ℝ)^419
        have hw : |(108165499/200000000 : ℝ)|=(108165499/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_s7_5 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1076915437/2500000000 : ℝ)*x 0 + (4484222629/10000000000 : ℝ)*x 1 + (4137461261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076915437/2500000000 : ℝ)^547 ≤ (8326190390731/25000000000000 : ℝ)^419 := by
    have hnat : (1076915437 : ℕ)^547*25000000000000^419 ≤ 8326190390731^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076915437 2500000000 8326190390731 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484222629/10000000000 : ℝ)^547 ≤ (3509791646419/10000000000000 : ℝ)^419 := by
    have hnat : (4484222629 : ℕ)^547*10000000000000^419 ≤ 3509791646419^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484222629 10000000000 3509791646419 10000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4137461261/10000000000 : ℝ)^547 ≤ (31597321969521/100000000000000 : ℝ)^419 := by
    have hnat : (4137461261 : ℕ)^547*100000000000000^419 ≤ 31597321969521^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137461261 10000000000 31597321969521 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076915437/2500000000 : ℝ), (4484222629/10000000000 : ℝ), (4137461261/10000000000 : ℝ)] ![(8326190390731/25000000000000 : ℝ), (3509791646419/10000000000000 : ℝ), (31597321969521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076915437/2500000000 : ℝ)|^547 ≤ (8326190390731/25000000000000 : ℝ)^419
        have hw : |(1076915437/2500000000 : ℝ)|=(1076915437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484222629/10000000000 : ℝ)|^547 ≤ (3509791646419/10000000000000 : ℝ)^419
        have hw : |(4484222629/10000000000 : ℝ)|=(4484222629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4137461261/10000000000 : ℝ)|^547 ≤ (31597321969521/100000000000000 : ℝ)^419
        have hw : |(4137461261/10000000000 : ℝ)|=(4137461261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1416_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157651737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5657/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (59/400 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11313/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11313/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11313/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11313/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11313/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11313/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11313/100000 : ℝ) ^ (4375/1024 : ℝ) ≤ (4522911286253629/50000000000000000000 : ℝ) := by
    have hpowers : (11313/100000 : ℝ)^4375 ≤ (4522911286253629/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11313 : ℕ)^4375*50000000000000000000^1024 ≤ 4522911286253629^1024*100000^4375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11313 100000 4522911286253629 50000000000000000000 4375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11313/100000 : ℝ)) (X := (4522911286253629/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (59/400 : ℝ) ^ (4375/1024 : ℝ) ≤ (7024839150250219/25000000000000000000 : ℝ) := by
    have hpowers : (59/400 : ℝ)^4375 ≤ (7024839150250219/25000000000000000000 : ℝ)^1024 := by
      have hnat : (59 : ℕ)^4375*25000000000000000000^1024 ≤ 7024839150250219^1024*400^4375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59 400 7024839150250219 25000000000000000000 4375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59/400 : ℝ)) (X := (7024839150250219/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004522911286253629/25000000000000000000 : ℝ) ≤ (10000423418541409/10000000000000000 : ℝ) ^ (4375/1024 : ℝ) := by
    have hpowers : (25004522911286253629/25000000000000000000 : ℝ)^1024 ≤ (10000423418541409/10000000000000000 : ℝ)^4375 := by
      have hnat : (25004522911286253629 : ℕ)^1024*10000000000000000^4375 ≤ 10000423418541409^4375*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004522911286253629 25000000000000000000 10000423418541409 10000000000000000 1024 4375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000423418541409/10000000000000000 : ℝ)) (X := (25004522911286253629/25000000000000000000 : ℝ)) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018572589586754067/50000000000000000000 : ℝ) ≤ (5000434642899827/5000000000000000 : ℝ) ^ (4375/1024 : ℝ) := by
    have hpowers : (50018572589586754067/50000000000000000000 : ℝ)^1024 ≤ (5000434642899827/5000000000000000 : ℝ)^4375 := by
      have hnat : (50018572589586754067 : ℕ)^1024*5000000000000000^4375 ≤ 5000434642899827^4375*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018572589586754067 50000000000000000000 5000434642899827 5000000000000000 1024 4375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000434642899827/5000000000000000 : ℝ)) (X := (50018572589586754067/50000000000000000000 : ℝ)) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507024839150250219/12500000000000000000 : ℝ) ≤ (10001315153057899/10000000000000000 : ℝ) ^ (4375/1024 : ℝ) := by
    have hpowers : (12507024839150250219/12500000000000000000 : ℝ)^1024 ≤ (10001315153057899/10000000000000000 : ℝ)^4375 := by
      have hnat : (12507024839150250219 : ℕ)^1024*10000000000000000^4375 ≤ 10001315153057899^4375*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507024839150250219 12500000000000000000 10001315153057899 10000000000000000 1024 4375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001315153057899/10000000000000000 : ℝ)) (X := (12507024839150250219/12500000000000000000 : ℝ)) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4522911286253629/50000000000000000000 : ℝ) ≤ ((34361367096941771363/34370000000000000000 : ℝ)+2*(89173451649/68740000000000 : ℝ)*(11313/100000 : ℝ))^(4375/1024 : ℝ) := by
    rw [show (34361367096941771363/34370000000000000000 : ℝ)+2*(89173451649/68740000000000 : ℝ)*(11313/100000 : ℝ)=(10000423418541409/10000000000000000 : ℝ) by norm_num, show 1+2*(4522911286253629/50000000000000000000 : ℝ)=(25004522911286253629/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7024839150250219/25000000000000000000 : ℝ)+(4522911286253629/50000000000000000000 : ℝ) ≤ ((34361367096941771363/34370000000000000000 : ℝ)+(89173451649/68740000000000 : ℝ)*((59/400 : ℝ)+(11313/100000 : ℝ)))^(4375/1024 : ℝ) := by
    rw [show (34361367096941771363/34370000000000000000 : ℝ)+(89173451649/68740000000000 : ℝ)*((59/400 : ℝ)+(11313/100000 : ℝ))=(5000434642899827/5000000000000000 : ℝ) by norm_num, show 1+(7024839150250219/25000000000000000000 : ℝ)+(4522911286253629/50000000000000000000 : ℝ)=(50018572589586754067/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7024839150250219/25000000000000000000 : ℝ) ≤ ((34361367096941771363/34370000000000000000 : ℝ)+2*(89173451649/68740000000000 : ℝ)*(59/400 : ℝ))^(4375/1024 : ℝ) := by
    rw [show (34361367096941771363/34370000000000000000 : ℝ)+2*(89173451649/68740000000000 : ℝ)*(59/400 : ℝ)=(10001315153057899/10000000000000000 : ℝ) by norm_num, show 1+2*(7024839150250219/25000000000000000000 : ℝ)=(12507024839150250219/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34361367096941771363/34370000000000000000 : ℝ)*(X 1 0+X 2 0)+(89173451649/68740000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4375/1024 : ℝ)) (lo := (11313/100000 : ℝ)) (hi := (59/400 : ℝ)) (c := (34361367096941771363/34370000000000000000 : ℝ)) (alpha := (89173451649/68740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34361367096941771363/34370000000000000000 : ℝ)*(X 0 1+X 2 1)+(89173451649/68740000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4375/1024 : ℝ)) (lo := (11313/100000 : ℝ)) (hi := (59/400 : ℝ)) (c := (34361367096941771363/34370000000000000000 : ℝ)) (alpha := (89173451649/68740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34361367096941771363/34370000000000000000 : ℝ)*(X 0 2+X 1 2)+(89173451649/68740000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4375/1024 : ℝ)) (lo := (11313/100000 : ℝ)) (hi := (59/400 : ℝ)) (c := (34361367096941771363/34370000000000000000 : ℝ)) (alpha := (89173451649/68740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1981729999/10000000000 : ℝ)*X 0 0+(5408862343/10000000000 : ℝ)*X 0 1+(5246633537/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347590377/10000000000 : ℝ)*X 1 0+(-2064331843/10000000000 : ℝ)*X 1 1+(5246633521/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673795199/5000000000 : ℝ)*X 2 0+(1311658377/2500000000 : ℝ)*X 2 1+(-258041479/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1076909137/2500000000 : ℝ)*X 0 0+(517024603/1250000000 : ℝ)*X 0 1+(280342571/625000000 : ℝ)*X 0 2+(1076909137/2500000000 : ℝ)*X 1 0+(517024603/1250000000 : ℝ)*X 1 1+(280342571/625000000 : ℝ)*X 1 2+(1076909137/2500000000 : ℝ)*X 2 0+(517024603/1250000000 : ℝ)*X 2 1+(280342571/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-990870973/5000000000 : ℝ)*X 0 0+(5247217527/10000000000 : ℝ)*X 0 1+(108165499/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1076915437/2500000000 : ℝ)*X 0 0+(4484222629/10000000000 : ℝ)*X 0 1+(4137461261/10000000000 : ℝ)*X 0 2+(1076915437/2500000000 : ℝ)*X 1 0+(4484222629/10000000000 : ℝ)*X 1 1+(4137461261/10000000000 : ℝ)*X 1 2+(1076915437/2500000000 : ℝ)*X 2 0+(4484222629/10000000000 : ℝ)*X 2 1+(4137461261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (163496013062906454126972039/53703125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (521227621/100000000000000 : ℝ)*(base19) + (481875743/100000000000000 : ℝ)*(base23) + (16994247/50000000000000 : ℝ)*(lower2) + (33740003/50000000000000 : ℝ)*(upper3) + (9768349/25000000000000 : ℝ)*(upper5) + (70524703942037/1562500000000 : ℝ)*(major0) + (70524703942037/1562500000000 : ℝ)*(major1) + (70524703942037/1562500000000 : ℝ)*(major2) + (6164143961465543/100000000000000 : ℝ)*(sp0) + (770519247884607/12500000000000 : ℝ)*(sp1) + (1232830804485747/20000000000000 : ℝ)*(sp2) + (1431500965741149/50000000000000 : ℝ)*(sp3) + (5271419467/50000000000000 : ℝ)*(sp4) + (2783656287/50000000000000 : ℝ)*(sp5) + (357875937349359/12500000000000 : ℝ)*(f.failure) + (6164154504304477/100000000000000 : ℝ)*(f.sum) + (33989063817663/3437000000000000000000000000 : ℝ)*base66 + (100016755571516653/26851562500000000000000000000000 : ℝ)*base67 + (238424182462983347/26851562500000000000000000000000 : ℝ)*base70 + (20157079511611431/53703125000000000000000000000000 : ℝ)*base71 + (9825527934899/1718500000000000000000000000 : ℝ)*base74 + (210644483212392681/53703125000000000000000000000000 : ℝ)*base75 + (1264865892964419819/53703125000000000000000000000000 : ℝ)*base78 + (353328602799580181/53703125000000000000000000000000 : ℝ)*base79 + (7588729764691/1718500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (22186583/1250000000000000000000 : ℝ)*base89 + (22186583/1250000000000000000000 : ℝ)*base91 + (22186583/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1416_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157651737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11313/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (59/400 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1416_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1416_box_0 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1820120249/10000000000 : ℝ)*x 0 + (2693406559/5000000000 : ℝ)*x 1 + (5386813597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1820120249/10000000000 : ℝ)^547 ≤ (10816047914389/100000000000000 : ℝ)^419 := by
    have hnat : (1820120249 : ℕ)^547*100000000000000^419 ≤ 10816047914389^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1820120249 10000000000 10816047914389 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693406559/5000000000 : ℝ)^547 ≤ (44591973442493/100000000000000 : ℝ)^419 := by
    have hnat : (2693406559 : ℕ)^547*100000000000000^419 ≤ 44591973442493^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693406559 5000000000 44591973442493 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386813597/10000000000 : ℝ)^547 ≤ (44591978618961/100000000000000 : ℝ)^419 := by
    have hnat : (5386813597 : ℕ)^547*100000000000000^419 ≤ 44591978618961^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386813597 10000000000 44591978618961 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1820120249/10000000000 : ℝ), (2693406559/5000000000 : ℝ), (5386813597/10000000000 : ℝ)] ![(10816047914389/100000000000000 : ℝ), (44591973442493/100000000000000 : ℝ), (44591978618961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1820120249/10000000000 : ℝ)|^547 ≤ (10816047914389/100000000000000 : ℝ)^419
        have hw : |(-1820120249/10000000000 : ℝ)|=(1820120249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693406559/5000000000 : ℝ)|^547 ≤ (44591973442493/100000000000000 : ℝ)^419
        have hw : |(2693406559/5000000000 : ℝ)|=(2693406559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386813597/10000000000 : ℝ)|^547 ≤ (44591978618961/100000000000000 : ℝ)^419
        have hw : |(5386813597/10000000000 : ℝ)|=(5386813597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_box_1 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5285966019/10000000000 : ℝ)*x 0 + (-391723331/2000000000 : ℝ)*x 1 + (53868133/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285966019/10000000000 : ℝ)^547 ≤ (271907916423/625000000000 : ℝ)^419 := by
    have hnat : (5285966019 : ℕ)^547*625000000000^419 ≤ 271907916423^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285966019 10000000000 271907916423 625000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (391723331/2000000000 : ℝ)^547 ≤ (11902757961073/100000000000000 : ℝ)^419 := by
    have hnat : (391723331 : ℕ)^547*100000000000000^419 ≤ 11902757961073^419*2000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391723331 2000000000 11902757961073 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53868133/100000000 : ℝ)^547 ≤ (8918395081867/20000000000000 : ℝ)^419 := by
    have hnat : (53868133 : ℕ)^547*20000000000000^419 ≤ 8918395081867^419*100000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53868133 100000000 8918395081867 20000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285966019/10000000000 : ℝ), (-391723331/2000000000 : ℝ), (53868133/100000000 : ℝ)] ![(271907916423/625000000000 : ℝ), (11902757961073/100000000000000 : ℝ), (8918395081867/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285966019/10000000000 : ℝ)|^547 ≤ (271907916423/625000000000 : ℝ)^419
        have hw : |(5285966019/10000000000 : ℝ)|=(5285966019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-391723331/2000000000 : ℝ)|^547 ≤ (11902757961073/100000000000000 : ℝ)^419
        have hw : |(-391723331/2000000000 : ℝ)|=(391723331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53868133/100000000 : ℝ)|^547 ≤ (8918395081867/20000000000000 : ℝ)^419
        have hw : |(53868133/100000000 : ℝ)|=(53868133/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_box_2 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (660745849/1250000000 : ℝ)*x 0 + (5386813241/10000000000 : ℝ)*x 1 + (-1958615687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660745849/1250000000 : ℝ)^547 ≤ (21752637466633/50000000000000 : ℝ)^419 := by
    have hnat : (660745849 : ℕ)^547*50000000000000^419 ≤ 21752637466633^419*1250000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660745849 1250000000 21752637466633 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386813241/10000000000 : ℝ)^547 ≤ (11147993692933/25000000000000 : ℝ)^419 := by
    have hnat : (5386813241 : ℕ)^547*25000000000000^419 ≤ 11147993692933^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386813241 10000000000 11147993692933 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1958615687/10000000000 : ℝ)^547 ≤ (743921892583/6250000000000 : ℝ)^419 := by
    have hnat : (1958615687 : ℕ)^547*6250000000000^419 ≤ 743921892583^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958615687 10000000000 743921892583 6250000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660745849/1250000000 : ℝ), (5386813241/10000000000 : ℝ), (-1958615687/10000000000 : ℝ)] ![(21752637466633/50000000000000 : ℝ), (11147993692933/25000000000000 : ℝ), (743921892583/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660745849/1250000000 : ℝ)|^547 ≤ (21752637466633/50000000000000 : ℝ)^419
        have hw : |(660745849/1250000000 : ℝ)|=(660745849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386813241/10000000000 : ℝ)|^547 ≤ (11147993692933/25000000000000 : ℝ)^419
        have hw : |(5386813241/10000000000 : ℝ)|=(5386813241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1958615687/10000000000 : ℝ)|^547 ≤ (743921892583/6250000000000 : ℝ)^419
        have hw : |(-1958615687/10000000000 : ℝ)|=(1958615687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_box_3 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4454197893/10000000000 : ℝ)*x 0 + (847617963/2000000000 : ℝ)*x 1 + (847617939/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4454197893/10000000000 : ℝ)^547 ≤ (2174464803247/6250000000000 : ℝ)^419 := by
    have hnat : (4454197893 : ℕ)^547*6250000000000^419 ≤ 2174464803247^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4454197893 10000000000 2174464803247 6250000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (847617963/2000000000 : ℝ)^547 ≤ (32604282170353/100000000000000 : ℝ)^419 := by
    have hnat : (847617963 : ℕ)^547*100000000000000^419 ≤ 32604282170353^419*2000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847617963 2000000000 32604282170353 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847617939/2000000000 : ℝ)^547 ≤ (32604280965153/100000000000000 : ℝ)^419 := by
    have hnat : (847617939 : ℕ)^547*100000000000000^419 ≤ 32604280965153^419*2000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847617939 2000000000 32604280965153 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4454197893/10000000000 : ℝ), (847617963/2000000000 : ℝ), (847617939/2000000000 : ℝ)] ![(2174464803247/6250000000000 : ℝ), (32604282170353/100000000000000 : ℝ), (32604280965153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4454197893/10000000000 : ℝ)|^547 ≤ (2174464803247/6250000000000 : ℝ)^419
        have hw : |(4454197893/10000000000 : ℝ)|=(4454197893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(847617963/2000000000 : ℝ)|^547 ≤ (32604282170353/100000000000000 : ℝ)^419
        have hw : |(847617963/2000000000 : ℝ)|=(847617963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(847617939/2000000000 : ℝ)|^547 ≤ (32604280965153/100000000000000 : ℝ)^419
        have hw : |(847617939/2000000000 : ℝ)|=(847617939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_box_4 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-268259023/1250000000 : ℝ)*x 0 + (658290987/1250000000 : ℝ)*x 1 + (5266327697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268259023/1250000000 : ℝ)^547 ≤ (3352809309609/25000000000000 : ℝ)^419 := by
    have hnat : (268259023 : ℕ)^547*25000000000000^419 ≤ 3352809309609^419*1250000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268259023 1250000000 3352809309609 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658290987/1250000000 : ℝ)^547 ≤ (10823595610109/25000000000000 : ℝ)^419 := by
    have hnat : (658290987 : ℕ)^547*25000000000000^419 ≤ 10823595610109^419*1250000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658290987 1250000000 10823595610109 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266327697/10000000000 : ℝ)^547 ≤ (43294380304687/100000000000000 : ℝ)^419 := by
    have hnat : (5266327697 : ℕ)^547*100000000000000^419 ≤ 43294380304687^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266327697 10000000000 43294380304687 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-268259023/1250000000 : ℝ), (658290987/1250000000 : ℝ), (5266327697/10000000000 : ℝ)] ![(3352809309609/25000000000000 : ℝ), (10823595610109/25000000000000 : ℝ), (43294380304687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-268259023/1250000000 : ℝ)|^547 ≤ (3352809309609/25000000000000 : ℝ)^419
        have hw : |(-268259023/1250000000 : ℝ)|=(268259023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658290987/1250000000 : ℝ)|^547 ≤ (10823595610109/25000000000000 : ℝ)^419
        have hw : |(658290987/1250000000 : ℝ)|=(658290987/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266327697/10000000000 : ℝ)|^547 ≤ (43294380304687/100000000000000 : ℝ)^419
        have hw : |(5266327697/10000000000 : ℝ)|=(5266327697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_box_5 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2685166443/5000000000 : ℝ)*x 0 + (-2007451473/10000000000 : ℝ)*x 1 + (5266327689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2685166443/5000000000 : ℝ)^547 ≤ (5551744719663/12500000000000 : ℝ)^419 := by
    have hnat : (2685166443 : ℕ)^547*12500000000000^419 ≤ 5551744719663^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685166443 5000000000 5551744719663 12500000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2007451473/10000000000 : ℝ)^547 ≤ (12291662008793/100000000000000 : ℝ)^419 := by
    have hnat : (2007451473 : ℕ)^547*100000000000000^419 ≤ 12291662008793^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007451473 10000000000 12291662008793 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266327689/10000000000 : ℝ)^547 ≤ (10823595054707/25000000000000 : ℝ)^419 := by
    have hnat : (5266327689 : ℕ)^547*25000000000000^419 ≤ 10823595054707^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266327689 10000000000 10823595054707 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2685166443/5000000000 : ℝ), (-2007451473/10000000000 : ℝ), (5266327689/10000000000 : ℝ)] ![(5551744719663/12500000000000 : ℝ), (12291662008793/100000000000000 : ℝ), (10823595054707/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2685166443/5000000000 : ℝ)|^547 ≤ (5551744719663/12500000000000 : ℝ)^419
        have hw : |(2685166443/5000000000 : ℝ)|=(2685166443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2007451473/10000000000 : ℝ)|^547 ≤ (12291662008793/100000000000000 : ℝ)^419
        have hw : |(-2007451473/10000000000 : ℝ)|=(2007451473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266327689/10000000000 : ℝ)|^547 ≤ (10823595054707/25000000000000 : ℝ)^419
        have hw : |(5266327689/10000000000 : ℝ)|=(5266327689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_box_6 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5370332893/10000000000 : ℝ)*x 0 + (526632803/1000000000 : ℝ)*x 1 + (-1003725503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370332893/10000000000 : ℝ)^547 ≤ (44413957832881/100000000000000 : ℝ)^419 := by
    have hnat : (5370332893 : ℕ)^547*100000000000000^419 ≤ 44413957832881^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370332893 10000000000 44413957832881 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526632803/1000000000 : ℝ)^547 ≤ (21647191939289/50000000000000 : ℝ)^419 := by
    have hnat : (526632803 : ℕ)^547*50000000000000^419 ≤ 21647191939289^419*1000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526632803 1000000000 21647191939289 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003725503/5000000000 : ℝ)^547 ≤ (12291658275813/100000000000000 : ℝ)^419 := by
    have hnat : (1003725503 : ℕ)^547*100000000000000^419 ≤ 12291658275813^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003725503 5000000000 12291658275813 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370332893/10000000000 : ℝ), (526632803/1000000000 : ℝ), (-1003725503/5000000000 : ℝ)] ![(44413957832881/100000000000000 : ℝ), (21647191939289/50000000000000 : ℝ), (12291658275813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370332893/10000000000 : ℝ)|^547 ≤ (44413957832881/100000000000000 : ℝ)^419
        have hw : |(5370332893/10000000000 : ℝ)|=(5370332893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526632803/1000000000 : ℝ)|^547 ≤ (21647191939289/50000000000000 : ℝ)^419
        have hw : |(526632803/1000000000 : ℝ)|=(526632803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1003725503/5000000000 : ℝ)|^547 ≤ (12291658275813/100000000000000 : ℝ)^419
        have hw : |(-1003725503/5000000000 : ℝ)|=(1003725503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_box_7 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (520005519/1250000000 : ℝ)*x 0 + (4385115139/10000000000 : ℝ)*x 1 + (4385115571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520005519/1250000000 : ℝ)^547 ≤ (15911329000801/50000000000000 : ℝ)^419 := by
    have hnat : (520005519 : ℕ)^547*50000000000000^419 ≤ 15911329000801^419*1250000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520005519 1250000000 15911329000801 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4385115139/10000000000 : ℝ)^547 ≤ (17044334401153/50000000000000 : ℝ)^419 := by
    have hnat : (4385115139 : ℕ)^547*50000000000000^419 ≤ 17044334401153^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4385115139 10000000000 17044334401153 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4385115571/10000000000 : ℝ)^547 ≤ (34088673186463/100000000000000 : ℝ)^419 := by
    have hnat : (4385115571 : ℕ)^547*100000000000000^419 ≤ 34088673186463^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4385115571 10000000000 34088673186463 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(520005519/1250000000 : ℝ), (4385115139/10000000000 : ℝ), (4385115571/10000000000 : ℝ)] ![(15911329000801/50000000000000 : ℝ), (17044334401153/50000000000000 : ℝ), (34088673186463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(520005519/1250000000 : ℝ)|^547 ≤ (15911329000801/50000000000000 : ℝ)^419
        have hw : |(520005519/1250000000 : ℝ)|=(520005519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4385115139/10000000000 : ℝ)|^547 ≤ (17044334401153/50000000000000 : ℝ)^419
        have hw : |(4385115139/10000000000 : ℝ)|=(4385115139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4385115571/10000000000 : ℝ)|^547 ≤ (34088673186463/100000000000000 : ℝ)^419
        have hw : |(4385115571/10000000000 : ℝ)|=(4385115571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_box_8 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2077446183/10000000000 : ℝ)*x 0 + (2591523323/5000000000 : ℝ)*x 1 + (5400795203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077446183/10000000000 : ℝ)^547 ≤ (2570824651923/20000000000000 : ℝ)^419 := by
    have hnat : (2077446183 : ℕ)^547*20000000000000^419 ≤ 2570824651923^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077446183 10000000000 2570824651923 20000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591523323/5000000000 : ℝ)^547 ≤ (10600685369139/25000000000000 : ℝ)^419 := by
    have hnat : (2591523323 : ℕ)^547*25000000000000^419 ≤ 10600685369139^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591523323 5000000000 10600685369139 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400795203/10000000000 : ℝ)^547 ≤ (44743135248001/100000000000000 : ℝ)^419 := by
    have hnat : (5400795203 : ℕ)^547*100000000000000^419 ≤ 44743135248001^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400795203 10000000000 44743135248001 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2077446183/10000000000 : ℝ), (2591523323/5000000000 : ℝ), (5400795203/10000000000 : ℝ)] ![(2570824651923/20000000000000 : ℝ), (10600685369139/25000000000000 : ℝ), (44743135248001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2077446183/10000000000 : ℝ)|^547 ≤ (2570824651923/20000000000000 : ℝ)^419
        have hw : |(-2077446183/10000000000 : ℝ)|=(2077446183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591523323/5000000000 : ℝ)|^547 ≤ (10600685369139/25000000000000 : ℝ)^419
        have hw : |(2591523323/5000000000 : ℝ)|=(2591523323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400795203/10000000000 : ℝ)|^547 ≤ (44743135248001/100000000000000 : ℝ)^419
        have hw : |(5400795203/10000000000 : ℝ)|=(5400795203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_box_9 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1319043039/2500000000 : ℝ)*x 0 + (-976410837/5000000000 : ℝ)*x 1 + (2700397417/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319043039/2500000000 : ℝ)^547 ≤ (43400065155431/100000000000000 : ℝ)^419 := by
    have hnat : (1319043039 : ℕ)^547*100000000000000^419 ≤ 43400065155431^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319043039 2500000000 43400065155431 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (976410837/5000000000 : ℝ)^547 ≤ (5928401784223/50000000000000 : ℝ)^419 := by
    have hnat : (976410837 : ℕ)^547*50000000000000^419 ≤ 5928401784223^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976410837 5000000000 5928401784223 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700397417/5000000000 : ℝ)^547 ≤ (11185782814281/25000000000000 : ℝ)^419 := by
    have hnat : (2700397417 : ℕ)^547*25000000000000^419 ≤ 11185782814281^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700397417 5000000000 11185782814281 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319043039/2500000000 : ℝ), (-976410837/5000000000 : ℝ), (2700397417/5000000000 : ℝ)] ![(43400065155431/100000000000000 : ℝ), (5928401784223/50000000000000 : ℝ), (11185782814281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319043039/2500000000 : ℝ)|^547 ≤ (43400065155431/100000000000000 : ℝ)^419
        have hw : |(1319043039/2500000000 : ℝ)|=(1319043039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-976410837/5000000000 : ℝ)|^547 ≤ (5928401784223/50000000000000 : ℝ)^419
        have hw : |(-976410837/5000000000 : ℝ)|=(976410837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700397417/5000000000 : ℝ)|^547 ≤ (11185782814281/25000000000000 : ℝ)^419
        have hw : |(2700397417/5000000000 : ℝ)|=(2700397417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_box_10 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (211046871/400000000 : ℝ)*x 0 + (5400795179/10000000000 : ℝ)*x 1 + (-48820543/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211046871/400000000 : ℝ)^547 ≤ (10850015266013/25000000000000 : ℝ)^419 := by
    have hnat : (211046871 : ℕ)^547*25000000000000^419 ≤ 10850015266013^419*400000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211046871 400000000 10850015266013 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400795179/10000000000 : ℝ)^547 ≤ (2796445936777/6250000000000 : ℝ)^419 := by
    have hnat : (5400795179 : ℕ)^547*6250000000000^419 ≤ 2796445936777^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400795179 10000000000 2796445936777 6250000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (48820543/250000000 : ℝ)^547 ≤ (5928401966531/50000000000000 : ℝ)^419 := by
    have hnat : (48820543 : ℕ)^547*50000000000000^419 ≤ 5928401966531^419*250000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48820543 250000000 5928401966531 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211046871/400000000 : ℝ), (5400795179/10000000000 : ℝ), (-48820543/250000000 : ℝ)] ![(10850015266013/25000000000000 : ℝ), (2796445936777/6250000000000 : ℝ), (5928401966531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211046871/400000000 : ℝ)|^547 ≤ (10850015266013/25000000000000 : ℝ)^419
        have hw : |(211046871/400000000 : ℝ)|=(211046871/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400795179/10000000000 : ℝ)|^547 ≤ (2796445936777/6250000000000 : ℝ)^419
        have hw : |(5400795179/10000000000 : ℝ)|=(5400795179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-48820543/250000000 : ℝ)|^547 ≤ (5928401966531/50000000000000 : ℝ)^419
        have hw : |(-48820543/250000000 : ℝ)|=(48820543/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_box_11 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2243887993/5000000000 : ℝ)*x 0 + (4221012937/10000000000 : ℝ)*x 1 + (1055253549/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2243887993/5000000000 : ℝ)^547 ≤ (7026845838307/20000000000000 : ℝ)^419 := by
    have hnat : (2243887993 : ℕ)^547*20000000000000^419 ≤ 7026845838307^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243887993 5000000000 7026845838307 20000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4221012937/10000000000 : ℝ)^547 ≤ (32432879083043/100000000000000 : ℝ)^419 := by
    have hnat : (4221012937 : ℕ)^547*100000000000000^419 ≤ 32432879083043^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4221012937 10000000000 32432879083043 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055253549/2500000000 : ℝ)^547 ≤ (8108222928003/25000000000000 : ℝ)^419 := by
    have hnat : (1055253549 : ℕ)^547*25000000000000^419 ≤ 8108222928003^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055253549 2500000000 8108222928003 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2243887993/5000000000 : ℝ), (4221012937/10000000000 : ℝ), (1055253549/2500000000 : ℝ)] ![(7026845838307/20000000000000 : ℝ), (32432879083043/100000000000000 : ℝ), (8108222928003/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2243887993/5000000000 : ℝ)|^547 ≤ (7026845838307/20000000000000 : ℝ)^419
        have hw : |(2243887993/5000000000 : ℝ)|=(2243887993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4221012937/10000000000 : ℝ)|^547 ≤ (32432879083043/100000000000000 : ℝ)^419
        have hw : |(4221012937/10000000000 : ℝ)|=(4221012937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055253549/2500000000 : ℝ)|^547 ≤ (8108222928003/25000000000000 : ℝ)^419
        have hw : |(1055253549/2500000000 : ℝ)|=(1055253549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_box_12 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-944474589/5000000000 : ℝ)*x 0 + (2734022629/5000000000 : ℝ)*x 1 + (1313802039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (944474589/5000000000 : ℝ)^547 ≤ (2270614128841/20000000000000 : ℝ)^419 := by
    have hnat : (944474589 : ℕ)^547*20000000000000^419 ≤ 2270614128841^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      944474589 5000000000 2270614128841 20000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734022629/5000000000 : ℝ)^547 ≤ (88812206869/195312500000 : ℝ)^419 := by
    have hnat : (2734022629 : ℕ)^547*195312500000^419 ≤ 88812206869^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734022629 5000000000 88812206869 195312500000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313802039/2500000000 : ℝ)^547 ≤ (10793769855563/25000000000000 : ℝ)^419 := by
    have hnat : (1313802039 : ℕ)^547*25000000000000^419 ≤ 10793769855563^419*2500000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313802039 2500000000 10793769855563 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-944474589/5000000000 : ℝ), (2734022629/5000000000 : ℝ), (1313802039/2500000000 : ℝ)] ![(2270614128841/20000000000000 : ℝ), (88812206869/195312500000 : ℝ), (10793769855563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-944474589/5000000000 : ℝ)|^547 ≤ (2270614128841/20000000000000 : ℝ)^419
        have hw : |(-944474589/5000000000 : ℝ)|=(944474589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734022629/5000000000 : ℝ)|^547 ≤ (88812206869/195312500000 : ℝ)^419
        have hw : |(2734022629/5000000000 : ℝ)|=(2734022629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313802039/2500000000 : ℝ)|^547 ≤ (10793769855563/25000000000000 : ℝ)^419
        have hw : |(1313802039/2500000000 : ℝ)|=(1313802039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_box_13 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2689058359/5000000000 : ℝ)*x 0 + (-2011857917/10000000000 : ℝ)*x 1 + (2627604429/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689058359/5000000000 : ℝ)^547 ≤ (22249008079821/50000000000000 : ℝ)^419 := by
    have hnat : (2689058359 : ℕ)^547*50000000000000^419 ≤ 22249008079821^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689058359 5000000000 22249008079821 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2011857917/10000000000 : ℝ)^547 ≤ (616344843743/5000000000000 : ℝ)^419 := by
    have hnat : (2011857917 : ℕ)^547*5000000000000^419 ≤ 616344843743^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011857917 10000000000 616344843743 5000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627604429/5000000000 : ℝ)^547 ≤ (2698442934471/6250000000000 : ℝ)^419 := by
    have hnat : (2627604429 : ℕ)^547*6250000000000^419 ≤ 2698442934471^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627604429 5000000000 2698442934471 6250000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689058359/5000000000 : ℝ), (-2011857917/10000000000 : ℝ), (2627604429/5000000000 : ℝ)] ![(22249008079821/50000000000000 : ℝ), (616344843743/5000000000000 : ℝ), (2698442934471/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689058359/5000000000 : ℝ)|^547 ≤ (22249008079821/50000000000000 : ℝ)^419
        have hw : |(2689058359/5000000000 : ℝ)|=(2689058359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2011857917/10000000000 : ℝ)|^547 ≤ (616344843743/5000000000000 : ℝ)^419
        have hw : |(-2011857917/10000000000 : ℝ)|=(2011857917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627604429/5000000000 : ℝ)|^547 ≤ (2698442934471/6250000000000 : ℝ)^419
        have hw : |(2627604429/5000000000 : ℝ)|=(2627604429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_box_14 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2689058347/5000000000 : ℝ)*x 0 + (2627604399/5000000000 : ℝ)*x 1 + (-201185803/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689058347/5000000000 : ℝ)^547 ≤ (22249007950203/50000000000000 : ℝ)^419 := by
    have hnat : (2689058347 : ℕ)^547*50000000000000^419 ≤ 22249007950203^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689058347 5000000000 22249007950203 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627604399/5000000000 : ℝ)^547 ≤ (43175086308007/100000000000000 : ℝ)^419 := by
    have hnat : (2627604399 : ℕ)^547*100000000000000^419 ≤ 43175086308007^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627604399 5000000000 43175086308007 100000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201185803/1000000000 : ℝ)^547 ≤ (2465379555747/20000000000000 : ℝ)^419 := by
    have hnat : (201185803 : ℕ)^547*20000000000000^419 ≤ 2465379555747^419*1000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201185803 1000000000 2465379555747 20000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689058347/5000000000 : ℝ), (2627604399/5000000000 : ℝ), (-201185803/1000000000 : ℝ)] ![(22249007950203/50000000000000 : ℝ), (43175086308007/100000000000000 : ℝ), (2465379555747/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689058347/5000000000 : ℝ)|^547 ≤ (22249007950203/50000000000000 : ℝ)^419
        have hw : |(2689058347/5000000000 : ℝ)|=(2689058347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627604399/5000000000 : ℝ)|^547 ≤ (43175086308007/100000000000000 : ℝ)^419
        have hw : |(2627604399/5000000000 : ℝ)|=(2627604399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-201185803/1000000000 : ℝ)|^547 ≤ (2465379555747/20000000000000 : ℝ)^419
        have hw : |(-201185803/1000000000 : ℝ)|=(201185803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1416_box_15 (p : ℝ) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4132447359/10000000000 : ℝ)*x 0 + (2199336301/5000000000 : ℝ)*x 1 + (879734779/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4132447359/10000000000 : ℝ)^547 ≤ (15773671628667/50000000000000 : ℝ)^419 := by
    have hnat : (4132447359 : ℕ)^547*50000000000000^419 ≤ 15773671628667^419*10000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132447359 10000000000 15773671628667 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2199336301/5000000000 : ℝ)^547 ≤ (17113160899231/50000000000000 : ℝ)^419 := by
    have hnat : (2199336301 : ℕ)^547*50000000000000^419 ≤ 17113160899231^419*5000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199336301 5000000000 17113160899231 50000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (879734779/2000000000 : ℝ)^547 ≤ (8556583733217/25000000000000 : ℝ)^419 := by
    have hnat : (879734779 : ℕ)^547*25000000000000^419 ≤ 8556583733217^419*2000000000^547 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879734779 2000000000 8556583733217 25000000000000 547 419 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (547/128 : ℝ)) 547 419 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4132447359/10000000000 : ℝ), (2199336301/5000000000 : ℝ), (879734779/2000000000 : ℝ)] ![(15773671628667/50000000000000 : ℝ), (17113160899231/50000000000000 : ℝ), (8556583733217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4132447359/10000000000 : ℝ)|^547 ≤ (15773671628667/50000000000000 : ℝ)^419
        have hw : |(4132447359/10000000000 : ℝ)|=(4132447359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2199336301/5000000000 : ℝ)|^547 ≤ (17113160899231/50000000000000 : ℝ)^419
        have hw : |(2199336301/5000000000 : ℝ)|=(2199336301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(879734779/2000000000 : ℝ)|^547 ≤ (8556583733217/25000000000000 : ℝ)^419
        have hw : |(879734779/2000000000 : ℝ)|=(879734779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1416_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157651737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15723/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59087/100000 : ℝ) ∧ (80377/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21159/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5657/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (59/400 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5657/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5657/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (59/400 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5657/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5657/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (59/400 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5657/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5657/50000 : ℝ) ^ (4375/1024 : ℝ) ≤ (1809847861336401/20000000000000000000 : ℝ) := by
    have hpowers : (5657/50000 : ℝ)^4375 ≤ (1809847861336401/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5657 : ℕ)^4375*20000000000000000000^1024 ≤ 1809847861336401^1024*50000^4375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5657 50000 1809847861336401 20000000000000000000 4375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5657/50000 : ℝ)) (X := (1809847861336401/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (59/400 : ℝ) ^ (4375/1024 : ℝ) ≤ (7024839150250219/25000000000000000000 : ℝ) := by
    have hpowers : (59/400 : ℝ)^4375 ≤ (7024839150250219/25000000000000000000 : ℝ)^1024 := by
      have hnat : (59 : ℕ)^4375*25000000000000000000^1024 ≤ 7024839150250219^1024*400^4375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59 400 7024839150250219 25000000000000000000 4375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59/400 : ℝ)) (X := (7024839150250219/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001809847861336401/10000000000000000000 : ℝ) ≤ (10000423578461453/10000000000000000 : ℝ) ^ (4375/1024 : ℝ) := by
    have hpowers : (10001809847861336401/10000000000000000000 : ℝ)^1024 ≤ (10000423578461453/10000000000000000 : ℝ)^4375 := by
      have hnat : (10001809847861336401 : ℕ)^1024*10000000000000000^4375 ≤ 10000423578461453^4375*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001809847861336401 10000000000000000000 10000423578461453 10000000000000000 1024 4375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000423578461453/10000000000000000 : ℝ)) (X := (10001809847861336401/10000000000000000000 : ℝ)) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037148595907682881/100000000000000000000 : ℝ) ≤ (10000869365748011/10000000000000000 : ℝ) ^ (4375/1024 : ℝ) := by
    have hpowers : (100037148595907682881/100000000000000000000 : ℝ)^1024 ≤ (10000869365748011/10000000000000000 : ℝ)^4375 := by
      have hnat : (100037148595907682881 : ℕ)^1024*10000000000000000^4375 ≤ 10000869365748011^4375*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037148595907682881 100000000000000000000 10000869365748011 10000000000000000 1024 4375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000869365748011/10000000000000000 : ℝ)) (X := (100037148595907682881/100000000000000000000 : ℝ)) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507024839150250219/12500000000000000000 : ℝ) ≤ (10001315153034569/10000000000000000 : ℝ) ^ (4375/1024 : ℝ) := by
    have hpowers : (12507024839150250219/12500000000000000000 : ℝ)^1024 ≤ (10001315153034569/10000000000000000 : ℝ)^4375 := by
      have hnat : (12507024839150250219 : ℕ)^1024*10000000000000000^4375 ≤ 10001315153034569^4375*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507024839150250219 12500000000000000000 10001315153034569 10000000000000000 1024 4375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001315153034569/10000000000000000 : ℝ)) (X := (12507024839150250219/12500000000000000000 : ℝ)) (by norm_num) 4375 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1809847861336401/20000000000000000000 : ℝ) ≤ ((8587842035218329521/8590000000000000000 : ℝ)+2*(222893643279/171800000000000 : ℝ)*(5657/50000 : ℝ))^(4375/1024 : ℝ) := by
    rw [show (8587842035218329521/8590000000000000000 : ℝ)+2*(222893643279/171800000000000 : ℝ)*(5657/50000 : ℝ)=(10000423578461453/10000000000000000 : ℝ) by norm_num, show 1+2*(1809847861336401/20000000000000000000 : ℝ)=(10001809847861336401/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7024839150250219/25000000000000000000 : ℝ)+(1809847861336401/20000000000000000000 : ℝ) ≤ ((8587842035218329521/8590000000000000000 : ℝ)+(222893643279/171800000000000 : ℝ)*((59/400 : ℝ)+(5657/50000 : ℝ)))^(4375/1024 : ℝ) := by
    rw [show (8587842035218329521/8590000000000000000 : ℝ)+(222893643279/171800000000000 : ℝ)*((59/400 : ℝ)+(5657/50000 : ℝ))=(10000869365748011/10000000000000000 : ℝ) by norm_num, show 1+(7024839150250219/25000000000000000000 : ℝ)+(1809847861336401/20000000000000000000 : ℝ)=(100037148595907682881/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7024839150250219/25000000000000000000 : ℝ) ≤ ((8587842035218329521/8590000000000000000 : ℝ)+2*(222893643279/171800000000000 : ℝ)*(59/400 : ℝ))^(4375/1024 : ℝ) := by
    rw [show (8587842035218329521/8590000000000000000 : ℝ)+2*(222893643279/171800000000000 : ℝ)*(59/400 : ℝ)=(10001315153034569/10000000000000000 : ℝ) by norm_num, show 1+2*(7024839150250219/25000000000000000000 : ℝ)=(12507024839150250219/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8587842035218329521/8590000000000000000 : ℝ)*(X 1 0+X 2 0)+(222893643279/171800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4375/1024 : ℝ)) (lo := (5657/50000 : ℝ)) (hi := (59/400 : ℝ)) (c := (8587842035218329521/8590000000000000000 : ℝ)) (alpha := (222893643279/171800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8587842035218329521/8590000000000000000 : ℝ)*(X 0 1+X 2 1)+(222893643279/171800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4375/1024 : ℝ)) (lo := (5657/50000 : ℝ)) (hi := (59/400 : ℝ)) (c := (8587842035218329521/8590000000000000000 : ℝ)) (alpha := (222893643279/171800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8587842035218329521/8590000000000000000 : ℝ)*(X 0 2+X 1 2)+(222893643279/171800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4375/1024 : ℝ)) (lo := (5657/50000 : ℝ)) (hi := (59/400 : ℝ)) (c := (8587842035218329521/8590000000000000000 : ℝ)) (alpha := (222893643279/171800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1820120249/10000000000 : ℝ)*X 0 0+(2693406559/5000000000 : ℝ)*X 0 1+(5386813597/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285966019/10000000000 : ℝ)*X 1 0+(-391723331/2000000000 : ℝ)*X 1 1+(53868133/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((660745849/1250000000 : ℝ)*X 2 0+(5386813241/10000000000 : ℝ)*X 2 1+(-1958615687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4454197893/10000000000 : ℝ)*X 0 0+(847617963/2000000000 : ℝ)*X 0 1+(847617939/2000000000 : ℝ)*X 0 2+(4454197893/10000000000 : ℝ)*X 1 0+(847617963/2000000000 : ℝ)*X 1 1+(847617939/2000000000 : ℝ)*X 1 2+(4454197893/10000000000 : ℝ)*X 2 0+(847617963/2000000000 : ℝ)*X 2 1+(847617939/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-268259023/1250000000 : ℝ)*X 0 0+(658290987/1250000000 : ℝ)*X 0 1+(5266327697/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2685166443/5000000000 : ℝ)*X 1 0+(-2007451473/10000000000 : ℝ)*X 1 1+(5266327689/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5370332893/10000000000 : ℝ)*X 2 0+(526632803/1000000000 : ℝ)*X 2 1+(-1003725503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((520005519/1250000000 : ℝ)*X 0 0+(4385115139/10000000000 : ℝ)*X 0 1+(4385115571/10000000000 : ℝ)*X 0 2+(520005519/1250000000 : ℝ)*X 1 0+(4385115139/10000000000 : ℝ)*X 1 1+(4385115571/10000000000 : ℝ)*X 1 2+(520005519/1250000000 : ℝ)*X 2 0+(4385115139/10000000000 : ℝ)*X 2 1+(4385115571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2077446183/10000000000 : ℝ)*X 0 0+(2591523323/5000000000 : ℝ)*X 0 1+(5400795203/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1319043039/2500000000 : ℝ)*X 1 0+(-976410837/5000000000 : ℝ)*X 1 1+(2700397417/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((211046871/400000000 : ℝ)*X 2 0+(5400795179/10000000000 : ℝ)*X 2 1+(-48820543/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2243887993/5000000000 : ℝ)*X 0 0+(4221012937/10000000000 : ℝ)*X 0 1+(1055253549/2500000000 : ℝ)*X 0 2+(2243887993/5000000000 : ℝ)*X 1 0+(4221012937/10000000000 : ℝ)*X 1 1+(1055253549/2500000000 : ℝ)*X 1 2+(2243887993/5000000000 : ℝ)*X 2 0+(4221012937/10000000000 : ℝ)*X 2 1+(1055253549/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-944474589/5000000000 : ℝ)*X 0 0+(2734022629/5000000000 : ℝ)*X 0 1+(1313802039/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2689058359/5000000000 : ℝ)*X 1 0+(-2011857917/10000000000 : ℝ)*X 1 1+(2627604429/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2689058347/5000000000 : ℝ)*X 2 0+(2627604399/5000000000 : ℝ)*X 2 1+(-201185803/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4132447359/10000000000 : ℝ)*X 0 0+(2199336301/5000000000 : ℝ)*X 0 1+(879734779/2000000000 : ℝ)*X 0 2+(4132447359/10000000000 : ℝ)*X 1 0+(2199336301/5000000000 : ℝ)*X 1 1+(879734779/2000000000 : ℝ)*X 1 2+(4132447359/10000000000 : ℝ)*X 2 0+(2199336301/5000000000 : ℝ)*X 2 1+(879734779/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1416_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15723/25000 : ℝ) ≤ (-2701087690531883246797900588089/4295000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (102018997/100000000000000 : ℝ)*(upper0) + (1531271/5000000000000 : ℝ)*(lower1) + (153163299/100000000000000 : ℝ)*(lower2) + (56788939/100000000000000 : ℝ)*(lower3) + (60051717560197/2000000000000 : ℝ)*(major0) + (60051717560197/2000000000000 : ℝ)*(major1) + (60051717560197/2000000000000 : ℝ)*(major2) + (138566189/6250000000000 : ℝ)*(sp1) + (412156225658171/10000000000000 : ℝ)*(sp4) + (1030390931639363/25000000000000 : ℝ)*(sp5) + (515174613562501/12500000000000 : ℝ)*(sp6) + (1904568852298691/100000000000000 : ℝ)*(sp7) + (3687034767/100000000000000 : ℝ)*(sp8) + (42258779117/25000000000000 : ℝ)*(sp14) + (1904568852298691/100000000000000 : ℝ)*(f.failure) + (1030391485904119/25000000000000 : ℝ)*(f.sum) + (2157818575407/429500000000000000000000000 : ℝ)*base66 + (37537720553554363/17180000000000000000000000000000 : ℝ)*base68 + (92224331029934363/17180000000000000000000000000000 : ℝ)*base70 + (58184133774974363/17180000000000000000000000000000 : ℝ)*base72 + (1601157759629/107375000000000000000000000 : ℝ)*base74 + (69214522349194363/17180000000000000000000000000000 : ℝ)*base76 + (127127611352414363/17180000000000000000000000000000 : ℝ)*base78 + (147786614901285637/17180000000000000000000000000000 : ℝ)*base79 + (1229269816373/214750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (78976267/10000000000000000000000 : ℝ)*base89 + (78976267/10000000000000000000000 : ℝ)*base91 + (78976267/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59087/100000 : ℝ) ≤ (63447417561788115234004462062747/107375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (90115051/50000000000000 : ℝ)*(lower1) + (7666667/50000000000000 : ℝ)*(lower2) + (45985137/50000000000000 : ℝ)*(lower3) + (492365557/100000000000000 : ℝ)*(upper4) + (1536874748658631/50000000000000 : ℝ)*(major0) + (1536874748658631/50000000000000 : ℝ)*(major1) + (1536874748658631/50000000000000 : ℝ)*(major2) + (4178093859279033/100000000000000 : ℝ)*(sp0) + (4177941980939889/100000000000000 : ℝ)*(sp1) + (1044522398494817/25000000000000 : ℝ)*(sp2) + (974851298320339/50000000000000 : ℝ)*(sp3) + (853059953/20000000000000 : ℝ)*(sp6) + (1203587009/20000000000000 : ℝ)*(sp7) + (18984792393/12500000000000 : ℝ)*(sp9) + (974854307287861/50000000000000 : ℝ)*(f.failure) + (4178093859279033/100000000000000 : ℝ)*(f.sum) + (9612719372333/2147500000000000000000000000 : ℝ)*base66 + (3910478782540695751/429500000000000000000000000000000 : ℝ)*base67 + (440327138574195751/429500000000000000000000000000000 : ℝ)*base69 + (3799964597105695751/429500000000000000000000000000000 : ℝ)*base71 + (10335748234781/4295000000000000000000000000 : ℝ)*base74 + (2308255575228304249/429500000000000000000000000000000 : ℝ)*base76 + (3698674733348695751/429500000000000000000000000000000 : ℝ)*base77 + (2825112678442695751/429500000000000000000000000000000 : ℝ)*base79 + (11829603777957/536875000000000000000000000 : ℝ)*base82 + (54335443/5000000000000000000000 : ℝ)*base90 + (54335443/5000000000000000000000 : ℝ)*base92 + (54335443/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (80377/100000 : ℝ) ≤ (43153481429035443813697373945061/53687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22011153/50000000000000 : ℝ)*(upper0) + (15845213/20000000000000 : ℝ)*(lower1) + (17497279/10000000000000 : ℝ)*(upper2) + (113221331/50000000000000 : ℝ)*(lower3) + (786807/781250000000 : ℝ)*(lower5) + (422794806615247/12500000000000 : ℝ)*(major0) + (422794806615247/12500000000000 : ℝ)*(major1) + (422794806615247/12500000000000 : ℝ)*(major2) + (15910360163/100000000000000 : ℝ)*(sp0) + (62598922931/100000000000000 : ℝ)*(sp3) + (2296222887077661/50000000000000 : ℝ)*(sp8) + (918492336903097/20000000000000 : ℝ)*(sp9) + (918492336903097/20000000000000 : ℝ)*(sp10) + (2145399618801937/100000000000000 : ℝ)*(sp11) + (536365554431217/25000000000000 : ℝ)*(f.failure) + (918492336903097/20000000000000 : ℝ)*(f.sum) + (107427257453/1073750000000000000000000000 : ℝ)*base65 + (3075311162276956687/107375000000000000000000000000000 : ℝ)*base67 + (820294145653793313/107375000000000000000000000000000 : ℝ)*base70 + (464158603067418313/107375000000000000000000000000000 : ℝ)*base72 + (1065923281583/268437500000000000000000000 : ℝ)*base74 + (340429667074668313/107375000000000000000000000000000 : ℝ)*base76 + (270840676153043313/107375000000000000000000000000000 : ℝ)*base78 + (1248789550930581687/107375000000000000000000000000000 : ℝ)*base79 + (20117857639963/4295000000000000000000000000 : ℝ)*base82 + (7073929/2500000000000000000000 : ℝ)*base89 + (7073929/2500000000000000000000 : ℝ)*base91 + (7073929/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-21159/25000 : ℝ) ≤ (-90875122787018511379904155846233/107375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9436749/6250000000000 : ℝ)*(lower1) + (170781583/100000000000000 : ℝ)*(upper3) + (3651227/3125000000000 : ℝ)*(lower4) + (30692589/10000000000000 : ℝ)*(upper5) + (1709842615625909/50000000000000 : ℝ)*(major0) + (1709842615625909/50000000000000 : ℝ)*(major1) + (1709842615625909/50000000000000 : ℝ)*(major2) + (1449899247/20000000000000 : ℝ)*(sp4) + (135618833827/100000000000000 : ℝ)*(sp6) + (145408130569/100000000000000 : ℝ)*(sp7) + (2349217700084161/50000000000000 : ℝ)*(sp12) + (2349221324832279/50000000000000 : ℝ)*(sp13) + (469830703083073/10000000000000 : ℝ)*(sp14) + (2168993541002493/100000000000000 : ℝ)*(sp15) + (1084569474566531/50000000000000 : ℝ)*(f.failure) + (2349221324832279/50000000000000 : ℝ)*(f.sum) + (431960386753/2147500000000000000000000000 : ℝ)*base65 + (2122386606774209589/429500000000000000000000000000000 : ℝ)*base67 + (745297124041790411/429500000000000000000000000000000 : ℝ)*base70 + (3246732594002790411/429500000000000000000000000000000 : ℝ)*base72 + (7743353335133/2147500000000000000000000000 : ℝ)*base73 + (2766223361083290411/429500000000000000000000000000000 : ℝ)*base76 + (1815852264669290411/429500000000000000000000000000000 : ℝ)*base78 + (1633867797888790411/429500000000000000000000000000000 : ℝ)*base80 + (45740716387371/4295000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (34214347/5000000000000000000000 : ℝ)*base89 + (34214347/5000000000000000000000 : ℝ)*base91 + (34214347/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1416_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157651737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (59/400 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15723/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59087/100000 : ℝ) else (80377/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21159/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1416_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1416_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157651737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15723/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59087/100000 : ℝ) else (80377/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21159/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1416_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1416_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1416_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4375/1024 : ℝ) ≤ p) (hpb : p ≤ (547/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (157651737/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15723/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(59087/100000 : ℝ) else (80377/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21159/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1416_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

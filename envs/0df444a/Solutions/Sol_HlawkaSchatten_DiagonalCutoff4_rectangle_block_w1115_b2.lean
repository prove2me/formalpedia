-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1115_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:07:14.640848+00:00
-- url     : https://prove2.me/submissions/e1abae17-723c-4a81-b3c2-54588f066466

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
theorem support_rectangle_w1115_s6_0 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-544957157/2500000000 : ℝ)*x 0 + (5393923951/10000000000 : ℝ)*x 1 + (5264911389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544957157/2500000000 : ℝ)^2077 ≤ (1655361706203/12500000000000 : ℝ)^1565 := by
    have hnat : (544957157 : ℕ)^2077*12500000000000^1565 ≤ 1655361706203^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544957157 2500000000 1655361706203 12500000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393923951/10000000000 : ℝ)^2077 ≤ (44075345432609/100000000000000 : ℝ)^1565 := by
    have hnat : (5393923951 : ℕ)^2077*100000000000000^1565 ≤ 44075345432609^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393923951 10000000000 44075345432609 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264911389/10000000000 : ℝ)^2077 ≤ (8536352183087/20000000000000 : ℝ)^1565 := by
    have hnat : (5264911389 : ℕ)^2077*20000000000000^1565 ≤ 8536352183087^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264911389 10000000000 8536352183087 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-544957157/2500000000 : ℝ), (5393923951/10000000000 : ℝ), (5264911389/10000000000 : ℝ)] ![(1655361706203/12500000000000 : ℝ), (44075345432609/100000000000000 : ℝ), (8536352183087/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-544957157/2500000000 : ℝ)|^2077 ≤ (1655361706203/12500000000000 : ℝ)^1565
        have hw : |(-544957157/2500000000 : ℝ)|=(544957157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393923951/10000000000 : ℝ)|^2077 ≤ (44075345432609/100000000000000 : ℝ)^1565
        have hw : |(5393923951/10000000000 : ℝ)|=(5393923951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264911389/10000000000 : ℝ)|^2077 ≤ (8536352183087/20000000000000 : ℝ)^1565
        have hw : |(5264911389/10000000000 : ℝ)|=(5264911389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s6_1 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344952771/10000000000 : ℝ)*x 0 + (-2245278697/10000000000 : ℝ)*x 1 + (1316227857/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344952771/10000000000 : ℝ)^2077 ≤ (21772531737881/50000000000000 : ℝ)^1565 := by
    have hnat : (5344952771 : ℕ)^2077*50000000000000^1565 ≤ 21772531737881^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344952771 10000000000 21772531737881 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245278697/10000000000 : ℝ)^2077 ≤ (3443293794039/25000000000000 : ℝ)^1565 := by
    have hnat : (2245278697 : ℕ)^2077*25000000000000^1565 ≤ 3443293794039^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245278697 10000000000 3443293794039 25000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316227857/2500000000 : ℝ)^2077 ≤ (42681761335037/100000000000000 : ℝ)^1565 := by
    have hnat : (1316227857 : ℕ)^2077*100000000000000^1565 ≤ 42681761335037^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316227857 2500000000 42681761335037 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344952771/10000000000 : ℝ), (-2245278697/10000000000 : ℝ), (1316227857/2500000000 : ℝ)] ![(21772531737881/50000000000000 : ℝ), (3443293794039/25000000000000 : ℝ), (42681761335037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344952771/10000000000 : ℝ)|^2077 ≤ (21772531737881/50000000000000 : ℝ)^1565
        have hw : |(5344952771/10000000000 : ℝ)|=(5344952771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2245278697/10000000000 : ℝ)|^2077 ≤ (3443293794039/25000000000000 : ℝ)^1565
        have hw : |(-2245278697/10000000000 : ℝ)|=(2245278697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316227857/2500000000 : ℝ)|^2077 ≤ (42681761335037/100000000000000 : ℝ)^1565
        have hw : |(1316227857/2500000000 : ℝ)|=(1316227857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s6_2 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672476361/5000000000 : ℝ)*x 0 + (1316227873/2500000000 : ℝ)*x 1 + (-2245278677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672476361/5000000000 : ℝ)^2077 ≤ (1088626573649/2500000000000 : ℝ)^1565 := by
    have hnat : (2672476361 : ℕ)^2077*2500000000000^1565 ≤ 1088626573649^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672476361 5000000000 1088626573649 2500000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316227873/2500000000 : ℝ)^2077 ≤ (666902531619/1562500000000 : ℝ)^1565 := by
    have hnat : (1316227873 : ℕ)^2077*1562500000000^1565 ≤ 666902531619^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316227873 2500000000 666902531619 1562500000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2245278677/10000000000 : ℝ)^2077 ≤ (13773175013333/100000000000000 : ℝ)^1565 := by
    have hnat : (2245278677 : ℕ)^2077*100000000000000^1565 ≤ 13773175013333^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245278677 10000000000 13773175013333 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672476361/5000000000 : ℝ), (1316227873/2500000000 : ℝ), (-2245278677/10000000000 : ℝ)] ![(1088626573649/2500000000000 : ℝ), (666902531619/1562500000000 : ℝ), (13773175013333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672476361/5000000000 : ℝ)|^2077 ≤ (1088626573649/2500000000000 : ℝ)^1565
        have hw : |(2672476361/5000000000 : ℝ)|=(2672476361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316227873/2500000000 : ℝ)|^2077 ≤ (666902531619/1562500000000 : ℝ)^1565
        have hw : |(1316227873/2500000000 : ℝ)|=(1316227873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2245278677/10000000000 : ℝ)|^2077 ≤ (13773175013333/100000000000000 : ℝ)^1565
        have hw : |(-2245278677/10000000000 : ℝ)|=(2245278677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s6_3 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (174738829/400000000 : ℝ)*x 0 + (212134211/500000000 : ℝ)*x 1 + (2248996281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174738829/400000000 : ℝ)^2077 ≤ (33316613210051/100000000000000 : ℝ)^1565 := by
    have hnat : (174738829 : ℕ)^2077*100000000000000^1565 ≤ 33316613210051^1565*400000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174738829 400000000 33316613210051 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212134211/500000000 : ℝ)^2077 ≤ (8012368898643/25000000000000 : ℝ)^1565 := by
    have hnat : (212134211 : ℕ)^2077*25000000000000^1565 ≤ 8012368898643^1565*500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212134211 500000000 8012368898643 25000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248996281/5000000000 : ℝ)^2077 ≤ (34633911180843/100000000000000 : ℝ)^1565 := by
    have hnat : (2248996281 : ℕ)^2077*100000000000000^1565 ≤ 34633911180843^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248996281 5000000000 34633911180843 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174738829/400000000 : ℝ), (212134211/500000000 : ℝ), (2248996281/5000000000 : ℝ)] ![(33316613210051/100000000000000 : ℝ), (8012368898643/25000000000000 : ℝ), (34633911180843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174738829/400000000 : ℝ)|^2077 ≤ (33316613210051/100000000000000 : ℝ)^1565
        have hw : |(174738829/400000000 : ℝ)|=(174738829/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(212134211/500000000 : ℝ)|^2077 ≤ (8012368898643/25000000000000 : ℝ)^1565
        have hw : |(212134211/500000000 : ℝ)|=(212134211/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248996281/5000000000 : ℝ)|^2077 ≤ (34633911180843/100000000000000 : ℝ)^1565
        have hw : |(2248996281/5000000000 : ℝ)|=(2248996281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s6_4 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2179833717/10000000000 : ℝ)*x 0 + (82269331/156250000 : ℝ)*x 1 + (1078719387/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179833717/10000000000 : ℝ)^2077 ≤ (13242934680927/100000000000000 : ℝ)^1565 := by
    have hnat : (2179833717 : ℕ)^2077*100000000000000^1565 ≤ 13242934680927^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179833717 10000000000 13242934680927 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82269331/156250000 : ℝ)^2077 ≤ (8537053238301/20000000000000 : ℝ)^1565 := by
    have hnat : (82269331 : ℕ)^2077*20000000000000^1565 ≤ 8537053238301^1565*156250000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82269331 156250000 8537053238301 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078719387/2000000000 : ℝ)^2077 ≤ (8814359822793/20000000000000 : ℝ)^1565 := by
    have hnat : (1078719387 : ℕ)^2077*20000000000000^1565 ≤ 8814359822793^1565*2000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078719387 2000000000 8814359822793 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2179833717/10000000000 : ℝ), (82269331/156250000 : ℝ), (1078719387/2000000000 : ℝ)] ![(13242934680927/100000000000000 : ℝ), (8537053238301/20000000000000 : ℝ), (8814359822793/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2179833717/10000000000 : ℝ)|^2077 ≤ (13242934680927/100000000000000 : ℝ)^1565
        have hw : |(-2179833717/10000000000 : ℝ)|=(2179833717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82269331/156250000 : ℝ)|^2077 ≤ (8537053238301/20000000000000 : ℝ)^1565
        have hw : |(82269331/156250000 : ℝ)|=(82269331/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078719387/2000000000 : ℝ)|^2077 ≤ (8814359822793/20000000000000 : ℝ)^1565
        have hw : |(1078719387/2000000000 : ℝ)|=(1078719387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s6_5 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312333117/10000000000 : ℝ)*x 0 + (-1058296597/5000000000 : ℝ)*x 1 + (5393596891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312333117/10000000000 : ℝ)^2077 ≤ (8638544655827/20000000000000 : ℝ)^1565 := by
    have hnat : (5312333117 : ℕ)^2077*20000000000000^1565 ≤ 8638544655827^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312333117 10000000000 8638544655827 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058296597/5000000000 : ℝ)^2077 ≤ (12735478072233/100000000000000 : ℝ)^1565 := by
    have hnat : (1058296597 : ℕ)^2077*100000000000000^1565 ≤ 12735478072233^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058296597 5000000000 12735478072233 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393596891/10000000000 : ℝ)^2077 ≤ (11017949659203/25000000000000 : ℝ)^1565 := by
    have hnat : (5393596891 : ℕ)^2077*25000000000000^1565 ≤ 11017949659203^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393596891 10000000000 11017949659203 25000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312333117/10000000000 : ℝ), (-1058296597/5000000000 : ℝ), (5393596891/10000000000 : ℝ)] ![(8638544655827/20000000000000 : ℝ), (12735478072233/100000000000000 : ℝ), (11017949659203/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312333117/10000000000 : ℝ)|^2077 ≤ (8638544655827/20000000000000 : ℝ)^1565
        have hw : |(5312333117/10000000000 : ℝ)|=(5312333117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1058296597/5000000000 : ℝ)|^2077 ≤ (12735478072233/100000000000000 : ℝ)^1565
        have hw : |(-1058296597/5000000000 : ℝ)|=(1058296597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393596891/10000000000 : ℝ)|^2077 ≤ (11017949659203/25000000000000 : ℝ)^1565
        have hw : |(5393596891/10000000000 : ℝ)|=(5393596891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s6_6 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656166579/5000000000 : ℝ)*x 0 + (539359683/1000000000 : ℝ)*x 1 + (-105829661/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656166579/5000000000 : ℝ)^2077 ≤ (43192723721551/100000000000000 : ℝ)^1565 := by
    have hnat : (2656166579 : ℕ)^2077*100000000000000^1565 ≤ 43192723721551^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656166579 5000000000 43192723721551 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539359683/1000000000 : ℝ)^2077 ≤ (8814359595061/20000000000000 : ℝ)^1565 := by
    have hnat : (539359683 : ℕ)^2077*20000000000000^1565 ≤ 8814359595061^1565*1000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539359683 1000000000 8814359595061 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105829661/500000000 : ℝ)^2077 ≤ (2547095655971/20000000000000 : ℝ)^1565 := by
    have hnat : (105829661 : ℕ)^2077*20000000000000^1565 ≤ 2547095655971^1565*500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105829661 500000000 2547095655971 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656166579/5000000000 : ℝ), (539359683/1000000000 : ℝ), (-105829661/500000000 : ℝ)] ![(43192723721551/100000000000000 : ℝ), (8814359595061/20000000000000 : ℝ), (2547095655971/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656166579/5000000000 : ℝ)|^2077 ≤ (43192723721551/100000000000000 : ℝ)^1565
        have hw : |(2656166579/5000000000 : ℝ)|=(2656166579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539359683/1000000000 : ℝ)|^2077 ≤ (8814359595061/20000000000000 : ℝ)^1565
        have hw : |(539359683/1000000000 : ℝ)|=(539359683/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105829661/500000000 : ℝ)|^2077 ≤ (2547095655971/20000000000000 : ℝ)^1565
        have hw : |(-105829661/500000000 : ℝ)|=(105829661/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s6_7 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (6825751/15625000 : ℝ)*x 0 + (4497347851/10000000000 : ℝ)*x 1 + (2121665667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6825751/15625000 : ℝ)^2077 ≤ (33316713566769/100000000000000 : ℝ)^1565 := by
    have hnat : (6825751 : ℕ)^2077*100000000000000^1565 ≤ 33316713566769^1565*15625000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6825751 15625000 33316713566769 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497347851/10000000000 : ℝ)^2077 ≤ (8656830771443/25000000000000 : ℝ)^1565 := by
    have hnat : (4497347851 : ℕ)^2077*25000000000000^1565 ≤ 8656830771443^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497347851 10000000000 8656830771443 25000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121665667/5000000000 : ℝ)^2077 ≤ (32055963343049/100000000000000 : ℝ)^1565 := by
    have hnat : (2121665667 : ℕ)^2077*100000000000000^1565 ≤ 32055963343049^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121665667 5000000000 32055963343049 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6825751/15625000 : ℝ), (4497347851/10000000000 : ℝ), (2121665667/5000000000 : ℝ)] ![(33316713566769/100000000000000 : ℝ), (8656830771443/25000000000000 : ℝ), (32055963343049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6825751/15625000 : ℝ)|^2077 ≤ (33316713566769/100000000000000 : ℝ)^1565
        have hw : |(6825751/15625000 : ℝ)|=(6825751/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497347851/10000000000 : ℝ)|^2077 ≤ (8656830771443/25000000000000 : ℝ)^1565
        have hw : |(4497347851/10000000000 : ℝ)|=(4497347851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2121665667/5000000000 : ℝ)|^2077 ≤ (32055963343049/100000000000000 : ℝ)^1565
        have hw : |(2121665667/5000000000 : ℝ)|=(2121665667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1115_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (451/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (11309/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7021/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7039/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (451/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7039/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (451/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7039/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (451/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7039/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (451/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7039/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (451/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7039/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (451/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (451/4000 : ℝ) ^ (8307/2048 : ℝ) ≤ (2859369764635171/20000000000000000000 : ℝ) := by
    have hpowers : (451/4000 : ℝ)^8307 ≤ (2859369764635171/20000000000000000000 : ℝ)^2048 := by
      have hnat : (451 : ℕ)^8307*20000000000000000000^2048 ≤ 2859369764635171^2048*4000^8307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        451 4000 2859369764635171 20000000000000000000 8307 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (451/4000 : ℝ)) (X := (2859369764635171/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7039/50000 : ℝ) ^ (8307/2048 : ℝ) ≤ (35184584181530413/100000000000000000000 : ℝ) := by
    have hpowers : (7039/50000 : ℝ)^8307 ≤ (35184584181530413/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7039 : ℕ)^8307*100000000000000000000^2048 ≤ 35184584181530413^2048*50000^8307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7039 50000 35184584181530413 100000000000000000000 8307 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7039/50000 : ℝ)) (X := (35184584181530413/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002859369764635171/10000000000000000000 : ℝ) ≤ (10000704870418847/10000000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (10002859369764635171/10000000000000000000 : ℝ)^2048 ≤ (10000704870418847/10000000000000000 : ℝ)^8307 := by
      have hnat : (10002859369764635171 : ℕ)^2048*10000000000000000^8307 ≤ 10000704870418847^8307*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002859369764635171 10000000000000000000 10000704870418847 10000000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000704870418847/10000000000000000 : ℝ)) (X := (10002859369764635171/10000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012370358251176567/25000000000000000000 : ℝ) ≤ (5000609841637641/5000000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (25012370358251176567/25000000000000000000 : ℝ)^2048 ≤ (5000609841637641/5000000000000000 : ℝ)^8307 := by
      have hnat : (25012370358251176567 : ℕ)^2048*5000000000000000^8307 ≤ 5000609841637641^8307*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012370358251176567 25000000000000000000 5000609841637641 5000000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000609841637641/5000000000000000 : ℝ)) (X := (25012370358251176567/25000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035184584181530413/50000000000000000000 : ℝ) ≤ (10001734496131717/10000000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (50035184584181530413/50000000000000000000 : ℝ)^2048 ≤ (10001734496131717/10000000000000000 : ℝ)^8307 := by
      have hnat : (50035184584181530413 : ℕ)^2048*10000000000000000^8307 ≤ 10001734496131717^8307*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035184584181530413 50000000000000000000 10001734496131717 10000000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001734496131717/10000000000000000 : ℝ)) (X := (50035184584181530413/50000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2859369764635171/20000000000000000000 : ℝ) ≤ ((28020366721871418891/28030000000000000000 : ℝ)+2*(102962571287/56060000000000 : ℝ)*(451/4000 : ℝ))^(8307/2048 : ℝ) := by
    rw [show (28020366721871418891/28030000000000000000 : ℝ)+2*(102962571287/56060000000000 : ℝ)*(451/4000 : ℝ)=(10000704870418847/10000000000000000 : ℝ) by norm_num, show 1+2*(2859369764635171/20000000000000000000 : ℝ)=(10002859369764635171/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35184584181530413/100000000000000000000 : ℝ)+(2859369764635171/20000000000000000000 : ℝ) ≤ ((28020366721871418891/28030000000000000000 : ℝ)+(102962571287/56060000000000 : ℝ)*((7039/50000 : ℝ)+(451/4000 : ℝ)))^(8307/2048 : ℝ) := by
    rw [show (28020366721871418891/28030000000000000000 : ℝ)+(102962571287/56060000000000 : ℝ)*((7039/50000 : ℝ)+(451/4000 : ℝ))=(5000609841637641/5000000000000000 : ℝ) by norm_num, show 1+(35184584181530413/100000000000000000000 : ℝ)+(2859369764635171/20000000000000000000 : ℝ)=(25012370358251176567/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35184584181530413/100000000000000000000 : ℝ) ≤ ((28020366721871418891/28030000000000000000 : ℝ)+2*(102962571287/56060000000000 : ℝ)*(7039/50000 : ℝ))^(8307/2048 : ℝ) := by
    rw [show (28020366721871418891/28030000000000000000 : ℝ)+2*(102962571287/56060000000000 : ℝ)*(7039/50000 : ℝ)=(10001734496131717/10000000000000000 : ℝ) by norm_num, show 1+2*(35184584181530413/100000000000000000000 : ℝ)=(50035184584181530413/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28020366721871418891/28030000000000000000 : ℝ)*(X 1 0+X 2 0)+(102962571287/56060000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (451/4000 : ℝ)) (hi := (7039/50000 : ℝ)) (c := (28020366721871418891/28030000000000000000 : ℝ)) (alpha := (102962571287/56060000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28020366721871418891/28030000000000000000 : ℝ)*(X 0 1+X 2 1)+(102962571287/56060000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (451/4000 : ℝ)) (hi := (7039/50000 : ℝ)) (c := (28020366721871418891/28030000000000000000 : ℝ)) (alpha := (102962571287/56060000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28020366721871418891/28030000000000000000 : ℝ)*(X 0 2+X 1 2)+(102962571287/56060000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (451/4000 : ℝ)) (hi := (7039/50000 : ℝ)) (c := (28020366721871418891/28030000000000000000 : ℝ)) (alpha := (102962571287/56060000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-544957157/2500000000 : ℝ)*X 0 0+(5393923951/10000000000 : ℝ)*X 0 1+(5264911389/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344952771/10000000000 : ℝ)*X 1 0+(-2245278697/10000000000 : ℝ)*X 1 1+(1316227857/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672476361/5000000000 : ℝ)*X 2 0+(1316227873/2500000000 : ℝ)*X 2 1+(-2245278677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((174738829/400000000 : ℝ)*X 0 0+(212134211/500000000 : ℝ)*X 0 1+(2248996281/5000000000 : ℝ)*X 0 2+(174738829/400000000 : ℝ)*X 1 0+(212134211/500000000 : ℝ)*X 1 1+(2248996281/5000000000 : ℝ)*X 1 2+(174738829/400000000 : ℝ)*X 2 0+(212134211/500000000 : ℝ)*X 2 1+(2248996281/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2179833717/10000000000 : ℝ)*X 0 0+(82269331/156250000 : ℝ)*X 0 1+(1078719387/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312333117/10000000000 : ℝ)*X 1 0+(-1058296597/5000000000 : ℝ)*X 1 1+(5393596891/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656166579/5000000000 : ℝ)*X 2 0+(539359683/1000000000 : ℝ)*X 2 1+(-105829661/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((6825751/15625000 : ℝ)*X 0 0+(4497347851/10000000000 : ℝ)*X 0 1+(2121665667/5000000000 : ℝ)*X 0 2+(6825751/15625000 : ℝ)*X 1 0+(4497347851/10000000000 : ℝ)*X 1 1+(2121665667/5000000000 : ℝ)*X 1 2+(6825751/15625000 : ℝ)*X 2 0+(4497347851/10000000000 : ℝ)*X 2 1+(2121665667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6363945473435601385465537359/700750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (463572713/25000000000000 : ℝ)*(base19) + (1583863541/100000000000000 : ℝ)*(base23) + (53280409/50000000000000 : ℝ)*(lower2) + (51321847/20000000000000 : ℝ)*(upper3) + (25334869/20000000000000 : ℝ)*(upper5) + (2917042622910417/50000000000000 : ℝ)*(major0) + (2917042622910417/50000000000000 : ℝ)*(major1) + (2917042622910417/50000000000000 : ℝ)*(major2) + (7751237549065397/100000000000000 : ℝ)*(sp0) + (7751286333245707/100000000000000 : ℝ)*(sp1) + (7751286603673019/100000000000000 : ℝ)*(sp2) + (1958427751021783/50000000000000 : ℝ)*(sp3) + (25319235581/50000000000000 : ℝ)*(sp4) + (26499340853/100000000000000 : ℝ)*(sp7) + (195844100069221/5000000000000 : ℝ)*(f.failure) + (7751288187536559/100000000000000 : ℝ)*(f.sum) + (3426243078521/1401500000000000000000000000 : ℝ)*base66 + (10948897447746987547/1401500000000000000000000000000000 : ℝ)*base67 + (22410585717968487547/1401500000000000000000000000000000 : ℝ)*base69 + (24977431874736512453/1401500000000000000000000000000000 : ℝ)*base72 + (6341728622613/1401500000000000000000000000 : ℝ)*base73 + (20033579080728987547/1401500000000000000000000000000000 : ℝ)*base75 + (6825909699568012453/1401500000000000000000000000000000 : ℝ)*base78 + (8810596673057487547/1401500000000000000000000000000000 : ℝ)*base79 + (560438268433/560600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2677559/500000000000000000000 : ℝ)*base89 + (2677559/500000000000000000000 : ℝ)*base91 + (2677559/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8404189400931807653414826933/1401500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (86233449/6250000000000 : ℝ)*(base19) + (733526793/50000000000000 : ℝ)*(base23) + (2598981/2500000000000 : ℝ)*(upper3) + (5749521/25000000000000 : ℝ)*(lower4) + (21114993/12500000000000 : ℝ)*(upper5) + (5863678929878379/100000000000000 : ℝ)*(major0) + (5863678929878379/100000000000000 : ℝ)*(major1) + (5863678929878379/100000000000000 : ℝ)*(major2) + (19323228943/50000000000000 : ℝ)*(sp1) + (9006120037/25000000000000 : ℝ)*(sp2) + (3895303541042607/50000000000000 : ℝ)*(sp4) + (7790567055892143/100000000000000 : ℝ)*(sp5) + (194764239763787/2500000000000 : ℝ)*(sp6) + (1968375288892977/50000000000000 : ℝ)*(sp7) + (1968375288892977/50000000000000 : ℝ)*(f.failure) + (3895303541042607/50000000000000 : ℝ)*(f.sum) + (8573874548193/2803000000000000000000000000 : ℝ)*base66 + (2555588396010442311/2803000000000000000000000000000000 : ℝ)*base68 + (26477830956701557689/2803000000000000000000000000000000 : ℝ)*base69 + (10866904314111442311/2803000000000000000000000000000000 : ℝ)*base72 + (658161758937/2803000000000000000000000000 : ℝ)*base74 + (32647151181308557689/2803000000000000000000000000000000 : ℝ)*base75 + (22634453976111557689/2803000000000000000000000000000000 : ℝ)*base77 + (8652286036469557689/2803000000000000000000000000000000 : ℝ)*base79 + (8690318786747/2803000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (7061883/5000000000000000000000 : ℝ)*base89 + (7061883/5000000000000000000000 : ℝ)*base91 + (7061883/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1115_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (451/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1115_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1115_s7_0 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2179861571/10000000000 : ℝ)*x 0 + (84274347/156250000 : ℝ)*x 1 + (329078459/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179861571/10000000000 : ℝ)^2077 ≤ (3310789815287/25000000000000 : ℝ)^1565 := by
    have hnat : (2179861571 : ℕ)^2077*25000000000000^1565 ≤ 3310789815287^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179861571 10000000000 3310789815287 25000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84274347/156250000 : ℝ)^2077 ≤ (22035689572213/50000000000000 : ℝ)^1565 := by
    have hnat : (84274347 : ℕ)^2077*50000000000000^1565 ≤ 22035689572213^1565*156250000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84274347 156250000 22035689572213 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329078459/625000000 : ℝ)^2077 ≤ (4268546157969/10000000000000 : ℝ)^1565 := by
    have hnat : (329078459 : ℕ)^2077*10000000000000^1565 ≤ 4268546157969^1565*625000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329078459 625000000 4268546157969 10000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2179861571/10000000000 : ℝ), (84274347/156250000 : ℝ), (329078459/625000000 : ℝ)] ![(3310789815287/25000000000000 : ℝ), (22035689572213/50000000000000 : ℝ), (4268546157969/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2179861571/10000000000 : ℝ)|^2077 ≤ (3310789815287/25000000000000 : ℝ)^1565
        have hw : |(-2179861571/10000000000 : ℝ)|=(2179861571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84274347/156250000 : ℝ)|^2077 ≤ (22035689572213/50000000000000 : ℝ)^1565
        have hw : |(84274347/156250000 : ℝ)|=(84274347/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329078459/625000000 : ℝ)|^2077 ≤ (4268546157969/10000000000000 : ℝ)^1565
        have hw : |(329078459/625000000 : ℝ)|=(329078459/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s7_1 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672430301/5000000000 : ℝ)*x 0 + (-224494647/1000000000 : ℝ)*x 1 + (5265255433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672430301/5000000000 : ℝ)^2077 ≤ (21772033460853/50000000000000 : ℝ)^1565 := by
    have hnat : (2672430301 : ℕ)^2077*50000000000000^1565 ≤ 21772033460853^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672430301 5000000000 21772033460853 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224494647/1000000000 : ℝ)^2077 ≤ (6885235265227/50000000000000 : ℝ)^1565 := by
    have hnat : (224494647 : ℕ)^2077*50000000000000^1565 ≤ 6885235265227^1565*1000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224494647 1000000000 6885235265227 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265255433/10000000000 : ℝ)^2077 ≤ (8537092507453/20000000000000 : ℝ)^1565 := by
    have hnat : (5265255433 : ℕ)^2077*20000000000000^1565 ≤ 8537092507453^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265255433 10000000000 8537092507453 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672430301/5000000000 : ℝ), (-224494647/1000000000 : ℝ), (5265255433/10000000000 : ℝ)] ![(21772033460853/50000000000000 : ℝ), (6885235265227/50000000000000 : ℝ), (8537092507453/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672430301/5000000000 : ℝ)|^2077 ≤ (21772033460853/50000000000000 : ℝ)^1565
        have hw : |(2672430301/5000000000 : ℝ)|=(2672430301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-224494647/1000000000 : ℝ)|^2077 ≤ (6885235265227/50000000000000 : ℝ)^1565
        have hw : |(-224494647/1000000000 : ℝ)|=(224494647/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265255433/10000000000 : ℝ)|^2077 ≤ (8537092507453/20000000000000 : ℝ)^1565
        have hw : |(5265255433/10000000000 : ℝ)|=(5265255433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s7_2 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344860807/10000000000 : ℝ)*x 0 + (658156911/1250000000 : ℝ)*x 1 + (-561236597/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344860807/10000000000 : ℝ)^2077 ≤ (4354406913821/10000000000000 : ℝ)^1565 := by
    have hnat : (5344860807 : ℕ)^2077*10000000000000^1565 ≤ 4354406913821^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344860807 10000000000 4354406913821 10000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658156911/1250000000 : ℝ)^2077 ≤ (42685460977171/100000000000000 : ℝ)^1565 := by
    have hnat : (658156911 : ℕ)^2077*100000000000000^1565 ≤ 42685460977171^1565*1250000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658156911 1250000000 42685460977171 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561236597/2500000000 : ℝ)^2077 ≤ (26895448951/195312500000 : ℝ)^1565 := by
    have hnat : (561236597 : ℕ)^2077*195312500000^1565 ≤ 26895448951^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561236597 2500000000 26895448951 195312500000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344860807/10000000000 : ℝ), (658156911/1250000000 : ℝ), (-561236597/2500000000 : ℝ)] ![(4354406913821/10000000000000 : ℝ), (42685460977171/100000000000000 : ℝ), (26895448951/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344860807/10000000000 : ℝ)|^2077 ≤ (4354406913821/10000000000000 : ℝ)^1565
        have hw : |(5344860807/10000000000 : ℝ)|=(5344860807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658156911/1250000000 : ℝ)|^2077 ≤ (42685460977171/100000000000000 : ℝ)^1565
        have hw : |(658156911/1250000000 : ℝ)|=(658156911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-561236597/2500000000 : ℝ)|^2077 ≤ (26895448951/195312500000 : ℝ)^1565
        have hw : |(-561236597/2500000000 : ℝ)|=(561236597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s7_3 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2184244417/5000000000 : ℝ)*x 0 + (424338413/1000000000 : ℝ)*x 1 + (4497287931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184244417/5000000000 : ℝ)^2077 ≤ (33316796504087/100000000000000 : ℝ)^1565 := by
    have hnat : (2184244417 : ℕ)^2077*100000000000000^1565 ≤ 33316796504087^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184244417 5000000000 33316796504087 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424338413/1000000000 : ℝ)^2077 ≤ (6411298534473/20000000000000 : ℝ)^1565 := by
    have hnat : (424338413 : ℕ)^2077*20000000000000^1565 ≤ 6411298534473^1565*1000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424338413 1000000000 6411298534473 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497287931/10000000000 : ℝ)^2077 ≤ (34626710798189/100000000000000 : ℝ)^1565 := by
    have hnat : (4497287931 : ℕ)^2077*100000000000000^1565 ≤ 34626710798189^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497287931 10000000000 34626710798189 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184244417/5000000000 : ℝ), (424338413/1000000000 : ℝ), (4497287931/10000000000 : ℝ)] ![(33316796504087/100000000000000 : ℝ), (6411298534473/20000000000000 : ℝ), (34626710798189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184244417/5000000000 : ℝ)|^2077 ≤ (33316796504087/100000000000000 : ℝ)^1565
        have hw : |(2184244417/5000000000 : ℝ)|=(2184244417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(424338413/1000000000 : ℝ)|^2077 ≤ (6411298534473/20000000000000 : ℝ)^1565
        have hw : |(424338413/1000000000 : ℝ)|=(424338413/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497287931/10000000000 : ℝ)|^2077 ≤ (34626710798189/100000000000000 : ℝ)^1565
        have hw : |(4497287931/10000000000 : ℝ)|=(4497287931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s7_4 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1089933307/5000000000 : ℝ)*x 0 + (5265577579/10000000000 : ℝ)*x 1 + (1078646949/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089933307/5000000000 : ℝ)^2077 ≤ (6621599960883/50000000000000 : ℝ)^1565 := by
    have hnat : (1089933307 : ℕ)^2077*50000000000000^1565 ≤ 6621599960883^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089933307 5000000000 6621599960883 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265577579/10000000000 : ℝ)^2077 ≤ (1334029019591/3125000000000 : ℝ)^1565 := by
    have hnat : (5265577579 : ℕ)^2077*3125000000000^1565 ≤ 1334029019591^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265577579 10000000000 1334029019591 3125000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078646949/2000000000 : ℝ)^2077 ≤ (22033935716831/50000000000000 : ℝ)^1565 := by
    have hnat : (1078646949 : ℕ)^2077*50000000000000^1565 ≤ 22033935716831^1565*2000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078646949 2000000000 22033935716831 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1089933307/5000000000 : ℝ), (5265577579/10000000000 : ℝ), (1078646949/2000000000 : ℝ)] ![(6621599960883/50000000000000 : ℝ), (1334029019591/3125000000000 : ℝ), (22033935716831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1089933307/5000000000 : ℝ)|^2077 ≤ (6621599960883/50000000000000 : ℝ)^1565
        have hw : |(-1089933307/5000000000 : ℝ)|=(1089933307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265577579/10000000000 : ℝ)|^2077 ≤ (1334029019591/3125000000000 : ℝ)^1565
        have hw : |(5265577579/10000000000 : ℝ)|=(5265577579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078646949/2000000000 : ℝ)|^2077 ≤ (22033935716831/50000000000000 : ℝ)^1565
        have hw : |(1078646949/2000000000 : ℝ)|=(1078646949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s7_5 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656210161/5000000000 : ℝ)*x 0 + (-2116967129/10000000000 : ℝ)*x 1 + (5393234751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656210161/5000000000 : ℝ)^2077 ≤ (43193664279937/100000000000000 : ℝ)^1565 := by
    have hnat : (2656210161 : ℕ)^2077*100000000000000^1565 ≤ 43193664279937^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656210161 5000000000 43193664279937 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2116967129/10000000000 : ℝ)^2077 ≤ (3184616050503/25000000000000 : ℝ)^1565 := by
    have hnat : (2116967129 : ℕ)^2077*25000000000000^1565 ≤ 3184616050503^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116967129 10000000000 3184616050503 25000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393234751/10000000000 : ℝ)^2077 ≤ (22033935749363/50000000000000 : ℝ)^1565 := by
    have hnat : (5393234751 : ℕ)^2077*50000000000000^1565 ≤ 22033935749363^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393234751 10000000000 22033935749363 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656210161/5000000000 : ℝ), (-2116967129/10000000000 : ℝ), (5393234751/10000000000 : ℝ)] ![(43193664279937/100000000000000 : ℝ), (3184616050503/25000000000000 : ℝ), (22033935749363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656210161/5000000000 : ℝ)|^2077 ≤ (43193664279937/100000000000000 : ℝ)^1565
        have hw : |(2656210161/5000000000 : ℝ)|=(2656210161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2116967129/10000000000 : ℝ)|^2077 ≤ (3184616050503/25000000000000 : ℝ)^1565
        have hw : |(-2116967129/10000000000 : ℝ)|=(2116967129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393234751/10000000000 : ℝ)|^2077 ≤ (22033935749363/50000000000000 : ℝ)^1565
        have hw : |(5393234751/10000000000 : ℝ)|=(5393234751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s7_6 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (212496813/400000000 : ℝ)*x 0 + (5393234743/10000000000 : ℝ)*x 1 + (-66155223/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212496813/400000000 : ℝ)^2077 ≤ (4319366431231/10000000000000 : ℝ)^1565 := by
    have hnat : (212496813 : ℕ)^2077*10000000000000^1565 ≤ 4319366431231^1565*400000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212496813 400000000 4319366431231 10000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393234743/10000000000 : ℝ)^2077 ≤ (44067871411973/100000000000000 : ℝ)^1565 := by
    have hnat : (5393234743 : ℕ)^2077*100000000000000^1565 ≤ 44067871411973^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393234743 10000000000 44067871411973 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66155223/312500000 : ℝ)^2077 ≤ (12738464257913/100000000000000 : ℝ)^1565 := by
    have hnat : (66155223 : ℕ)^2077*100000000000000^1565 ≤ 12738464257913^1565*312500000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66155223 312500000 12738464257913 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212496813/400000000 : ℝ), (5393234743/10000000000 : ℝ), (-66155223/312500000 : ℝ)] ![(4319366431231/10000000000000 : ℝ), (44067871411973/100000000000000 : ℝ), (12738464257913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212496813/400000000 : ℝ)|^2077 ≤ (4319366431231/10000000000000 : ℝ)^1565
        have hw : |(212496813/400000000 : ℝ)|=(212496813/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393234743/10000000000 : ℝ)|^2077 ≤ (44067871411973/100000000000000 : ℝ)^1565
        have hw : |(5393234743/10000000000 : ℝ)|=(5393234743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-66155223/312500000 : ℝ)|^2077 ≤ (12738464257913/100000000000000 : ℝ)^1565
        have hw : |(-66155223/312500000 : ℝ)|=(66155223/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s7_7 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (546062321/1250000000 : ℝ)*x 0 + (35973203/80000000 : ℝ)*x 1 + (4244024067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546062321/1250000000 : ℝ)^2077 ≤ (3331689502891/10000000000000 : ℝ)^1565 := by
    have hnat : (546062321 : ℕ)^2077*10000000000000^1565 ≤ 3331689502891^1565*1250000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546062321 1250000000 3331689502891 10000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35973203/80000000 : ℝ)^2077 ≤ (8655049037503/25000000000000 : ℝ)^1565 := by
    have hnat : (35973203 : ℕ)^2077*25000000000000^1565 ≤ 8655049037503^1565*80000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35973203 80000000 8655049037503 25000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4244024067/10000000000 : ℝ)^2077 ≤ (6412581762217/20000000000000 : ℝ)^1565 := by
    have hnat : (4244024067 : ℕ)^2077*20000000000000^1565 ≤ 6412581762217^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244024067 10000000000 6412581762217 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546062321/1250000000 : ℝ), (35973203/80000000 : ℝ), (4244024067/10000000000 : ℝ)] ![(3331689502891/10000000000000 : ℝ), (8655049037503/25000000000000 : ℝ), (6412581762217/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546062321/1250000000 : ℝ)|^2077 ≤ (3331689502891/10000000000000 : ℝ)^1565
        have hw : |(546062321/1250000000 : ℝ)|=(546062321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35973203/80000000 : ℝ)|^2077 ≤ (8655049037503/25000000000000 : ℝ)^1565
        have hw : |(35973203/80000000 : ℝ)|=(35973203/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4244024067/10000000000 : ℝ)|^2077 ≤ (6412581762217/20000000000000 : ℝ)^1565
        have hw : |(4244024067/10000000000 : ℝ)|=(4244024067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1115_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11317/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7017/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7021/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11309/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7021/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11309/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7021/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11309/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7021/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11309/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7021/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11309/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7021/50000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (11309/100000 : ℝ) ^ (8307/2048 : ℝ) ≤ (3618131736152601/25000000000000000000 : ℝ) := by
    have hpowers : (11309/100000 : ℝ)^8307 ≤ (3618131736152601/25000000000000000000 : ℝ)^2048 := by
      have hnat : (11309 : ℕ)^8307*25000000000000000000^2048 ≤ 3618131736152601^2048*100000^8307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11309 100000 3618131736152601 25000000000000000000 8307 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11309/100000 : ℝ)) (X := (3618131736152601/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7021/50000 : ℝ) ^ (8307/2048 : ℝ) ≤ (34821062059124233/100000000000000000000 : ℝ) := by
    have hpowers : (7021/50000 : ℝ)^8307 ≤ (34821062059124233/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7021 : ℕ)^8307*100000000000000000000^2048 ≤ 34821062059124233^2048*50000^8307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7021 50000 34821062059124233 100000000000000000000 8307 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7021/50000 : ℝ)) (X := (34821062059124233/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503618131736152601/12500000000000000000 : ℝ) ≤ (2500178382711383/2500000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (12503618131736152601/12500000000000000000 : ℝ)^2048 ≤ (2500178382711383/2500000000000000 : ℝ)^8307 := by
      have hnat : (12503618131736152601 : ℕ)^2048*2500000000000000^8307 ≤ 2500178382711383^8307*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503618131736152601 12500000000000000000 2500178382711383 2500000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500178382711383/2500000000000000 : ℝ)) (X := (12503618131736152601/12500000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049293589003734637/100000000000000000000 : ℝ) ≤ (1000121505390943/1000000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (100049293589003734637/100000000000000000000 : ℝ)^2048 ≤ (1000121505390943/1000000000000000 : ℝ)^8307 := by
      have hnat : (100049293589003734637 : ℕ)^2048*1000000000000000^8307 ≤ 1000121505390943^8307*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049293589003734637 100000000000000000000 1000121505390943 1000000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000121505390943/1000000000000000 : ℝ)) (X := (100049293589003734637/100000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034821062059124233/50000000000000000000 : ℝ) ≤ (625107286060833/625000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (50034821062059124233/50000000000000000000 : ℝ)^2048 ≤ (625107286060833/625000000000000 : ℝ)^8307 := by
      have hnat : (50034821062059124233 : ℕ)^2048*625000000000000^8307 ≤ 625107286060833^8307*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034821062059124233 50000000000000000000 625107286060833 625000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625107286060833/625000000000000 : ℝ)) (X := (50034821062059124233/50000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3618131736152601/25000000000000000000 : ℝ) ≤ ((3415075828892699249/3416250000000000000 : ℝ)+2*(250761531949/136650000000000 : ℝ)*(11309/100000 : ℝ))^(8307/2048 : ℝ) := by
    rw [show (3415075828892699249/3416250000000000000 : ℝ)+2*(250761531949/136650000000000 : ℝ)*(11309/100000 : ℝ)=(2500178382711383/2500000000000000 : ℝ) by norm_num, show 1+2*(3618131736152601/25000000000000000000 : ℝ)=(12503618131736152601/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34821062059124233/100000000000000000000 : ℝ)+(3618131736152601/25000000000000000000 : ℝ) ≤ ((3415075828892699249/3416250000000000000 : ℝ)+(250761531949/136650000000000 : ℝ)*((7021/50000 : ℝ)+(11309/100000 : ℝ)))^(8307/2048 : ℝ) := by
    rw [show (3415075828892699249/3416250000000000000 : ℝ)+(250761531949/136650000000000 : ℝ)*((7021/50000 : ℝ)+(11309/100000 : ℝ))=(1000121505390943/1000000000000000 : ℝ) by norm_num, show 1+(34821062059124233/100000000000000000000 : ℝ)+(3618131736152601/25000000000000000000 : ℝ)=(100049293589003734637/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34821062059124233/100000000000000000000 : ℝ) ≤ ((3415075828892699249/3416250000000000000 : ℝ)+2*(250761531949/136650000000000 : ℝ)*(7021/50000 : ℝ))^(8307/2048 : ℝ) := by
    rw [show (3415075828892699249/3416250000000000000 : ℝ)+2*(250761531949/136650000000000 : ℝ)*(7021/50000 : ℝ)=(625107286060833/625000000000000 : ℝ) by norm_num, show 1+2*(34821062059124233/100000000000000000000 : ℝ)=(50034821062059124233/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3415075828892699249/3416250000000000000 : ℝ)*(X 1 0+X 2 0)+(250761531949/136650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (7021/50000 : ℝ)) (c := (3415075828892699249/3416250000000000000 : ℝ)) (alpha := (250761531949/136650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3415075828892699249/3416250000000000000 : ℝ)*(X 0 1+X 2 1)+(250761531949/136650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (7021/50000 : ℝ)) (c := (3415075828892699249/3416250000000000000 : ℝ)) (alpha := (250761531949/136650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3415075828892699249/3416250000000000000 : ℝ)*(X 0 2+X 1 2)+(250761531949/136650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (11309/100000 : ℝ)) (hi := (7021/50000 : ℝ)) (c := (3415075828892699249/3416250000000000000 : ℝ)) (alpha := (250761531949/136650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2179861571/10000000000 : ℝ)*X 0 0+(84274347/156250000 : ℝ)*X 0 1+(329078459/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672430301/5000000000 : ℝ)*X 1 0+(-224494647/1000000000 : ℝ)*X 1 1+(5265255433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344860807/10000000000 : ℝ)*X 2 0+(658156911/1250000000 : ℝ)*X 2 1+(-561236597/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184244417/5000000000 : ℝ)*X 0 0+(424338413/1000000000 : ℝ)*X 0 1+(4497287931/10000000000 : ℝ)*X 0 2+(2184244417/5000000000 : ℝ)*X 1 0+(424338413/1000000000 : ℝ)*X 1 1+(4497287931/10000000000 : ℝ)*X 1 2+(2184244417/5000000000 : ℝ)*X 2 0+(424338413/1000000000 : ℝ)*X 2 1+(4497287931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1089933307/5000000000 : ℝ)*X 0 0+(5265577579/10000000000 : ℝ)*X 0 1+(1078646949/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656210161/5000000000 : ℝ)*X 1 0+(-2116967129/10000000000 : ℝ)*X 1 1+(5393234751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212496813/400000000 : ℝ)*X 2 0+(5393234743/10000000000 : ℝ)*X 2 1+(-66155223/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((546062321/1250000000 : ℝ)*X 0 0+(35973203/80000000 : ℝ)*X 0 1+(4244024067/10000000000 : ℝ)*X 0 2+(546062321/1250000000 : ℝ)*X 1 0+(35973203/80000000 : ℝ)*X 1 1+(4244024067/10000000000 : ℝ)*X 1 2+(546062321/1250000000 : ℝ)*X 2 0+(35973203/80000000 : ℝ)*X 2 1+(4244024067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (140089091929803460232557899/56937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29746747/5000000000000 : ℝ)*(base19) + (680899679/100000000000000 : ℝ)*(base23) + (56916071/50000000000000 : ℝ)*(lower2) + (1527099/10000000000000 : ℝ)*(upper3) + (8585077/20000000000000 : ℝ)*(upper5) + (5866309954658649/100000000000000 : ℝ)*(major0) + (5866309954658649/100000000000000 : ℝ)*(major1) + (5866309954658649/100000000000000 : ℝ)*(major2) + (974259574700503/12500000000000 : ℝ)*(sp0) + (779410223993997/10000000000000 : ℝ)*(sp1) + (7794102153975231/100000000000000 : ℝ)*(sp2) + (1969253570308433/50000000000000 : ℝ)*(sp3) + (13118635443/50000000000000 : ℝ)*(sp4) + (492590607/5000000000000 : ℝ)*(sp7) + (3938516992429007/100000000000000 : ℝ)*(f.failure) + (779410283487491/10000000000000 : ℝ)*(f.sum) + (13366956411427/2277500000000000000000000000 : ℝ)*base65 + (555485674671309867/113875000000000000000000000000000 : ℝ)*base67 + (1928650449778059867/113875000000000000000000000000000 : ℝ)*base69 + (2228868378980940133/113875000000000000000000000000000 : ℝ)*base72 + (14820103616517/2277500000000000000000000000 : ℝ)*base73 + (183821409637559867/113875000000000000000000000000000 : ℝ)*base75 + (626819466825684867/113875000000000000000000000000000 : ℝ)*base77 + (240919355423940133/113875000000000000000000000000000 : ℝ)*base80 + (7737079379261/1138750000000000000000000000 : ℝ)*base81 + (50421253/10000000000000000000000 : ℝ)*base89 + (50421253/10000000000000000000000 : ℝ)*base91 + (50421253/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (99364151960440796154754793/28468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (628922623/100000000000000 : ℝ)*(base19) + (682934501/100000000000000 : ℝ)*(base23) + (31638303/50000000000000 : ℝ)*(upper3) + (1531327/6250000000000 : ℝ)*(lower4) + (35863321/50000000000000 : ℝ)*(upper5) + (5895948273741293/100000000000000 : ℝ)*(major0) + (5895948273741293/100000000000000 : ℝ)*(major1) + (5895948273741293/100000000000000 : ℝ)*(major2) + (1806177563/10000000000000 : ℝ)*(sp1) + (18629504217/100000000000000 : ℝ)*(sp2) + (122398138988953/1562500000000 : ℝ)*(sp4) + (3916731102297369/50000000000000 : ℝ)*(sp5) + (3916730791427137/50000000000000 : ℝ)*(sp6) + (494801941980829/12500000000000 : ℝ)*(sp7) + (494801941980829/12500000000000 : ℝ)*(f.failure) + (122398138988953/1562500000000 : ℝ)*(f.sum) + (36897537380297/6832500000000000000000000000 : ℝ)*base65 + (786086733363271319/113875000000000000000000000000000 : ℝ)*base67 + (639581124208728681/113875000000000000000000000000000 : ℝ)*base70 + (724058507970271319/113875000000000000000000000000000 : ℝ)*base71 + (991943733941/854062500000000000000000000 : ℝ)*base74 + (1987693797032771319/113875000000000000000000000000000 : ℝ)*base75 + (141126999757396319/113875000000000000000000000000000 : ℝ)*base77 + (819182827012021319/113875000000000000000000000000000 : ℝ)*base79 + (5753765725127/6832500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (10868609/1250000000000000000000 : ℝ)*base90 + (10868609/1250000000000000000000 : ℝ)*base92 + (10868609/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1115_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11309/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1115_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1115_s8_0 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2179867597/10000000000 : ℝ)*x 0 + (2696738129/5000000000 : ℝ)*x 1 + (2632666713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179867597/10000000000 : ℝ)^2077 ≤ (6621603923743/50000000000000 : ℝ)^1565 := by
    have hnat : (2179867597 : ℕ)^2077*50000000000000^1565 ≤ 6621603923743^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179867597 10000000000 6621603923743 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696738129/5000000000 : ℝ)^2077 ≤ (44070490452357/100000000000000 : ℝ)^1565 := by
    have hnat : (2696738129 : ℕ)^2077*100000000000000^1565 ≤ 44070490452357^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696738129 5000000000 44070490452357 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632666713/5000000000 : ℝ)^2077 ≤ (42686301686841/100000000000000 : ℝ)^1565 := by
    have hnat : (2632666713 : ℕ)^2077*100000000000000^1565 ≤ 42686301686841^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632666713 5000000000 42686301686841 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2179867597/10000000000 : ℝ), (2696738129/5000000000 : ℝ), (2632666713/5000000000 : ℝ)] ![(6621603923743/50000000000000 : ℝ), (44070490452357/100000000000000 : ℝ), (42686301686841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2179867597/10000000000 : ℝ)|^2077 ≤ (6621603923743/50000000000000 : ℝ)^1565
        have hw : |(-2179867597/10000000000 : ℝ)|=(2179867597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696738129/5000000000 : ℝ)|^2077 ≤ (44070490452357/100000000000000 : ℝ)^1565
        have hw : |(2696738129/5000000000 : ℝ)|=(2696738129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632666713/5000000000 : ℝ)|^2077 ≤ (42686301686841/100000000000000 : ℝ)^1565
        have hw : |(2632666713/5000000000 : ℝ)|=(2632666713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s8_1 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344840441/10000000000 : ℝ)*x 0 + (-448974033/2000000000 : ℝ)*x 1 + (5265333427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344840441/10000000000 : ℝ)^2077 ≤ (4354384893673/10000000000000 : ℝ)^1565 := by
    have hnat : (5344840441 : ℕ)^2077*10000000000000^1565 ≤ 4354384893673^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344840441 10000000000 4354384893673 10000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448974033/2000000000 : ℝ)^2077 ≤ (550793974129/4000000000000 : ℝ)^1565 := by
    have hnat : (448974033 : ℕ)^2077*4000000000000^1565 ≤ 550793974129^1565*2000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448974033 2000000000 550793974129 4000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265333427/10000000000 : ℝ)^2077 ≤ (26678938561/62500000000 : ℝ)^1565 := by
    have hnat : (5265333427 : ℕ)^2077*62500000000^1565 ≤ 26678938561^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265333427 10000000000 26678938561 62500000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344840441/10000000000 : ℝ), (-448974033/2000000000 : ℝ), (5265333427/10000000000 : ℝ)] ![(4354384893673/10000000000000 : ℝ), (550793974129/4000000000000 : ℝ), (26678938561/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344840441/10000000000 : ℝ)|^2077 ≤ (4354384893673/10000000000000 : ℝ)^1565
        have hw : |(5344840441/10000000000 : ℝ)|=(5344840441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-448974033/2000000000 : ℝ)|^2077 ≤ (550793974129/4000000000000 : ℝ)^1565
        have hw : |(-448974033/2000000000 : ℝ)|=(448974033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265333427/10000000000 : ℝ)|^2077 ≤ (26678938561/62500000000 : ℝ)^1565
        have hw : |(5265333427/10000000000 : ℝ)|=(5265333427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s8_2 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (133621011/250000000 : ℝ)*x 0 + (5265333427/10000000000 : ℝ)*x 1 + (-2244870167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133621011/250000000 : ℝ)^2077 ≤ (43543848925917/100000000000000 : ℝ)^1565 := by
    have hnat : (133621011 : ℕ)^2077*100000000000000^1565 ≤ 43543848925917^1565*250000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133621011 250000000 43543848925917 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265333427/10000000000 : ℝ)^2077 ≤ (26678938561/62500000000 : ℝ)^1565 := by
    have hnat : (5265333427 : ℕ)^2077*62500000000^1565 ≤ 26678938561^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265333427 10000000000 26678938561 62500000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2244870167/10000000000 : ℝ)^2077 ≤ (13769849369507/100000000000000 : ℝ)^1565 := by
    have hnat : (2244870167 : ℕ)^2077*100000000000000^1565 ≤ 13769849369507^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244870167 10000000000 13769849369507 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133621011/250000000 : ℝ), (5265333427/10000000000 : ℝ), (-2244870167/10000000000 : ℝ)] ![(43543848925917/100000000000000 : ℝ), (26678938561/62500000000 : ℝ), (13769849369507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133621011/250000000 : ℝ)|^2077 ≤ (43543848925917/100000000000000 : ℝ)^1565
        have hw : |(133621011/250000000 : ℝ)|=(133621011/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265333427/10000000000 : ℝ)|^2077 ≤ (26678938561/62500000000 : ℝ)^1565
        have hw : |(5265333427/10000000000 : ℝ)|=(5265333427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2244870167/10000000000 : ℝ)|^2077 ≤ (13769849369507/100000000000000 : ℝ)^1565
        have hw : |(-2244870167/10000000000 : ℝ)|=(2244870167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s8_3 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4368492833/10000000000 : ℝ)*x 0 + (4243541817/10000000000 : ℝ)*x 1 + (4497129251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368492833/10000000000 : ℝ)^2077 ≤ (33316836980837/100000000000000 : ℝ)^1565 := by
    have hnat : (4368492833 : ℕ)^2077*100000000000000^1565 ≤ 33316836980837^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368492833 10000000000 33316836980837 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4243541817/10000000000 : ℝ)^2077 ≤ (32058073644959/100000000000000 : ℝ)^1565 := by
    have hnat : (4243541817 : ℕ)^2077*100000000000000^1565 ≤ 32058073644959^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243541817 10000000000 32058073644959 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497129251/10000000000 : ℝ)^2077 ≤ (1385003574103/4000000000000 : ℝ)^1565 := by
    have hnat : (4497129251 : ℕ)^2077*4000000000000^1565 ≤ 1385003574103^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497129251 10000000000 1385003574103 4000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368492833/10000000000 : ℝ), (4243541817/10000000000 : ℝ), (4497129251/10000000000 : ℝ)] ![(33316836980837/100000000000000 : ℝ), (32058073644959/100000000000000 : ℝ), (1385003574103/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368492833/10000000000 : ℝ)|^2077 ≤ (33316836980837/100000000000000 : ℝ)^1565
        have hw : |(4368492833/10000000000 : ℝ)|=(4368492833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4243541817/10000000000 : ℝ)|^2077 ≤ (32058073644959/100000000000000 : ℝ)^1565
        have hw : |(4243541817/10000000000 : ℝ)|=(4243541817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497129251/10000000000 : ℝ)|^2077 ≤ (1385003574103/4000000000000 : ℝ)^1565
        have hw : |(4497129251/10000000000 : ℝ)|=(4497129251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s8_4 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2179872511/10000000000 : ℝ)*x 0 + (658206861/1250000000 : ℝ)*x 1 + (1078630731/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179872511/10000000000 : ℝ)^2077 ≤ (331081186701/2500000000000 : ℝ)^1565 := by
    have hnat : (2179872511 : ℕ)^2077*2500000000000^1565 ≤ 331081186701^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179872511 10000000000 331081186701 2500000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658206861/1250000000 : ℝ)^2077 ≤ (42689760433763/100000000000000 : ℝ)^1565 := by
    have hnat : (658206861 : ℕ)^2077*100000000000000^1565 ≤ 42689760433763^1565*1250000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658206861 1250000000 42689760433763 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078630731/2000000000 : ℝ)^2077 ≤ (44066992084939/100000000000000 : ℝ)^1565 := by
    have hnat : (1078630731 : ℕ)^2077*100000000000000^1565 ≤ 44066992084939^1565*2000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078630731 2000000000 44066992084939 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2179872511/10000000000 : ℝ), (658206861/1250000000 : ℝ), (1078630731/2000000000 : ℝ)] ![(331081186701/2500000000000 : ℝ), (42689760433763/100000000000000 : ℝ), (44066992084939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2179872511/10000000000 : ℝ)|^2077 ≤ (331081186701/2500000000000 : ℝ)^1565
        have hw : |(-2179872511/10000000000 : ℝ)|=(2179872511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658206861/1250000000 : ℝ)|^2077 ≤ (42689760433763/100000000000000 : ℝ)^1565
        have hw : |(658206861/1250000000 : ℝ)|=(658206861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078630731/2000000000 : ℝ)|^2077 ≤ (44066992084939/100000000000000 : ℝ)^1565
        have hw : |(1078630731/2000000000 : ℝ)|=(1078630731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s8_5 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (531244047/1000000000 : ℝ)*x 0 + (-2117049939/10000000000 : ℝ)*x 1 + (2696576859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531244047/1000000000 : ℝ)^2077 ≤ (21596940845587/50000000000000 : ℝ)^1565 := by
    have hnat : (531244047 : ℕ)^2077*50000000000000^1565 ≤ 21596940845587^1565*1000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531244047 1000000000 21596940845587 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117049939/10000000000 : ℝ)^2077 ≤ (2547825104103/20000000000000 : ℝ)^1565 := by
    have hnat : (2117049939 : ℕ)^2077*20000000000000^1565 ≤ 2547825104103^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117049939 10000000000 2547825104103 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696576859/5000000000 : ℝ)^2077 ≤ (11016748192029/25000000000000 : ℝ)^1565 := by
    have hnat : (2696576859 : ℕ)^2077*25000000000000^1565 ≤ 11016748192029^1565*5000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696576859 5000000000 11016748192029 25000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531244047/1000000000 : ℝ), (-2117049939/10000000000 : ℝ), (2696576859/5000000000 : ℝ)] ![(21596940845587/50000000000000 : ℝ), (2547825104103/20000000000000 : ℝ), (11016748192029/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531244047/1000000000 : ℝ)|^2077 ≤ (21596940845587/50000000000000 : ℝ)^1565
        have hw : |(531244047/1000000000 : ℝ)|=(531244047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2117049939/10000000000 : ℝ)|^2077 ≤ (2547825104103/20000000000000 : ℝ)^1565
        have hw : |(-2117049939/10000000000 : ℝ)|=(2117049939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696576859/5000000000 : ℝ)|^2077 ≤ (11016748192029/25000000000000 : ℝ)^1565
        have hw : |(2696576859/5000000000 : ℝ)|=(2696576859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s8_6 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312440557/10000000000 : ℝ)*x 0 + (1348288407/2500000000 : ℝ)*x 1 + (-264631243/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312440557/10000000000 : ℝ)^2077 ≤ (21596941314983/50000000000000 : ℝ)^1565 := by
    have hnat : (5312440557 : ℕ)^2077*50000000000000^1565 ≤ 21596941314983^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312440557 10000000000 21596941314983 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348288407/2500000000 : ℝ)^2077 ≤ (44066991792149/100000000000000 : ℝ)^1565 := by
    have hnat : (1348288407 : ℕ)^2077*100000000000000^1565 ≤ 44066991792149^1565*2500000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348288407 2500000000 44066991792149 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264631243/1250000000 : ℝ)^2077 ≤ (6369562780223/50000000000000 : ℝ)^1565 := by
    have hnat : (264631243 : ℕ)^2077*50000000000000^1565 ≤ 6369562780223^1565*1250000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264631243 1250000000 6369562780223 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312440557/10000000000 : ℝ), (1348288407/2500000000 : ℝ), (-264631243/1250000000 : ℝ)] ![(21596941314983/50000000000000 : ℝ), (44066991792149/100000000000000 : ℝ), (6369562780223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312440557/10000000000 : ℝ)|^2077 ≤ (21596941314983/50000000000000 : ℝ)^1565
        have hw : |(5312440557/10000000000 : ℝ)|=(5312440557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348288407/2500000000 : ℝ)|^2077 ≤ (44066991792149/100000000000000 : ℝ)^1565
        have hw : |(1348288407/2500000000 : ℝ)|=(1348288407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-264631243/1250000000 : ℝ)|^2077 ≤ (6369562780223/50000000000000 : ℝ)^1565
        have hw : |(-264631243/1250000000 : ℝ)|=(264631243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1115_s8_7 (p : ℝ) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4368502597/10000000000 : ℝ)*x 0 + (899298627/2000000000 : ℝ)*x 1 + (53052253/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368502597/10000000000 : ℝ)^2077 ≤ (33316935809341/100000000000000 : ℝ)^1565 := by
    have hnat : (4368502597 : ℕ)^2077*100000000000000^1565 ≤ 33316935809341^1565*10000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368502597 10000000000 33316935809341 100000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899298627/2000000000 : ℝ)^2077 ≤ (17309294746621/50000000000000 : ℝ)^1565 := by
    have hnat : (899298627 : ℕ)^2077*50000000000000^1565 ≤ 17309294746621^1565*2000000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899298627 2000000000 17309294746621 50000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53052253/125000000 : ℝ)^2077 ≤ (6412894936289/20000000000000 : ℝ)^1565 := by
    have hnat : (53052253 : ℕ)^2077*20000000000000^1565 ≤ 6412894936289^1565*125000000^2077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53052253 125000000 6412894936289 20000000000000 2077 1565 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2077/512 : ℝ)) 2077 1565 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368502597/10000000000 : ℝ), (899298627/2000000000 : ℝ), (53052253/125000000 : ℝ)] ![(33316935809341/100000000000000 : ℝ), (17309294746621/50000000000000 : ℝ), (6412894936289/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368502597/10000000000 : ℝ)|^2077 ≤ (33316935809341/100000000000000 : ℝ)^1565
        have hw : |(4368502597/10000000000 : ℝ)|=(4368502597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899298627/2000000000 : ℝ)|^2077 ≤ (17309294746621/50000000000000 : ℝ)^1565
        have hw : |(899298627/2000000000 : ℝ)|=(899298627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53052253/125000000 : ℝ)|^2077 ≤ (6412894936289/20000000000000 : ℝ)^1565
        have hw : |(53052253/125000000 : ℝ)|=(53052253/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1115_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5659/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14033/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7017/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11317/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7017/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11317/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7017/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11317/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7017/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11317/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7017/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11317/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7017/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11317/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11317/100000 : ℝ) ^ (8307/2048 : ℝ) ≤ (7257049133417089/50000000000000000000 : ℝ) := by
    have hpowers : (11317/100000 : ℝ)^8307 ≤ (7257049133417089/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11317 : ℕ)^8307*50000000000000000000^2048 ≤ 7257049133417089^2048*100000^8307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11317 100000 7257049133417089 50000000000000000000 8307 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11317/100000 : ℝ)) (X := (7257049133417089/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7017/50000 : ℝ) ^ (8307/2048 : ℝ) ≤ (1737033259032821/5000000000000000000 : ℝ) := by
    have hpowers : (7017/50000 : ℝ)^8307 ≤ (1737033259032821/5000000000000000000 : ℝ)^2048 := by
      have hnat : (7017 : ℕ)^8307*5000000000000000000^2048 ≤ 1737033259032821^2048*50000^8307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7017 50000 1737033259032821 5000000000000000000 8307 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7017/50000 : ℝ)) (X := (1737033259032821/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007257049133417089/25000000000000000000 : ℝ) ≤ (2000143116037787/2000000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (25007257049133417089/25000000000000000000 : ℝ)^2048 ≤ (2000143116037787/2000000000000000 : ℝ)^8307 := by
      have hnat : (25007257049133417089 : ℕ)^2048*2000000000000000^8307 ≤ 2000143116037787^8307*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007257049133417089 25000000000000000000 2000143116037787 2000000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000143116037787/2000000000000000 : ℝ)) (X := (25007257049133417089/25000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024627381723745299/50000000000000000000 : ℝ) ≤ (10001214097063021/10000000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (50024627381723745299/50000000000000000000 : ℝ)^2048 ≤ (10001214097063021/10000000000000000 : ℝ)^8307 := by
      have hnat : (50024627381723745299 : ℕ)^2048*10000000000000000^8307 ≤ 10001214097063021^8307*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024627381723745299 50000000000000000000 10001214097063021 10000000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001214097063021/10000000000000000 : ℝ)) (X := (50024627381723745299/50000000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501737033259032821/2500000000000000000 : ℝ) ≤ (10001712613937107/10000000000000000 : ℝ) ^ (8307/2048 : ℝ) := by
    have hpowers : (2501737033259032821/2500000000000000000 : ℝ)^2048 ≤ (10001712613937107/10000000000000000 : ℝ)^8307 := by
      have hnat : (2501737033259032821 : ℕ)^2048*10000000000000000^8307 ≤ 10001712613937107^8307*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501737033259032821 2500000000000000000 10001712613937107 10000000000000000 2048 8307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001712613937107/10000000000000000 : ℝ)) (X := (2501737033259032821/2500000000000000000 : ℝ)) (by norm_num) 8307 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7257049133417089/50000000000000000000 : ℝ) ≤ ((2469150981858661261/2470000000000000000 : ℝ)+2*(22659857913/12350000000000 : ℝ)*(11317/100000 : ℝ))^(8307/2048 : ℝ) := by
    rw [show (2469150981858661261/2470000000000000000 : ℝ)+2*(22659857913/12350000000000 : ℝ)*(11317/100000 : ℝ)=(2000143116037787/2000000000000000 : ℝ) by norm_num, show 1+2*(7257049133417089/50000000000000000000 : ℝ)=(25007257049133417089/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1737033259032821/5000000000000000000 : ℝ)+(7257049133417089/50000000000000000000 : ℝ) ≤ ((2469150981858661261/2470000000000000000 : ℝ)+(22659857913/12350000000000 : ℝ)*((7017/50000 : ℝ)+(11317/100000 : ℝ)))^(8307/2048 : ℝ) := by
    rw [show (2469150981858661261/2470000000000000000 : ℝ)+(22659857913/12350000000000 : ℝ)*((7017/50000 : ℝ)+(11317/100000 : ℝ))=(10001214097063021/10000000000000000 : ℝ) by norm_num, show 1+(1737033259032821/5000000000000000000 : ℝ)+(7257049133417089/50000000000000000000 : ℝ)=(50024627381723745299/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1737033259032821/5000000000000000000 : ℝ) ≤ ((2469150981858661261/2470000000000000000 : ℝ)+2*(22659857913/12350000000000 : ℝ)*(7017/50000 : ℝ))^(8307/2048 : ℝ) := by
    rw [show (2469150981858661261/2470000000000000000 : ℝ)+2*(22659857913/12350000000000 : ℝ)*(7017/50000 : ℝ)=(10001712613937107/10000000000000000 : ℝ) by norm_num, show 1+2*(1737033259032821/5000000000000000000 : ℝ)=(2501737033259032821/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2469150981858661261/2470000000000000000 : ℝ)*(X 1 0+X 2 0)+(22659857913/12350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (11317/100000 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (2469150981858661261/2470000000000000000 : ℝ)) (alpha := (22659857913/12350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2469150981858661261/2470000000000000000 : ℝ)*(X 0 1+X 2 1)+(22659857913/12350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (11317/100000 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (2469150981858661261/2470000000000000000 : ℝ)) (alpha := (22659857913/12350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2469150981858661261/2470000000000000000 : ℝ)*(X 0 2+X 1 2)+(22659857913/12350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8307/2048 : ℝ)) (lo := (11317/100000 : ℝ)) (hi := (7017/50000 : ℝ)) (c := (2469150981858661261/2470000000000000000 : ℝ)) (alpha := (22659857913/12350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2179867597/10000000000 : ℝ)*X 0 0+(2696738129/5000000000 : ℝ)*X 0 1+(2632666713/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344840441/10000000000 : ℝ)*X 1 0+(-448974033/2000000000 : ℝ)*X 1 1+(5265333427/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133621011/250000000 : ℝ)*X 2 0+(5265333427/10000000000 : ℝ)*X 2 1+(-2244870167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4368492833/10000000000 : ℝ)*X 0 0+(4243541817/10000000000 : ℝ)*X 0 1+(4497129251/10000000000 : ℝ)*X 0 2+(4368492833/10000000000 : ℝ)*X 1 0+(4243541817/10000000000 : ℝ)*X 1 1+(4497129251/10000000000 : ℝ)*X 1 2+(4368492833/10000000000 : ℝ)*X 2 0+(4243541817/10000000000 : ℝ)*X 2 1+(4497129251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2179872511/10000000000 : ℝ)*X 0 0+(658206861/1250000000 : ℝ)*X 0 1+(1078630731/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531244047/1000000000 : ℝ)*X 1 0+(-2117049939/10000000000 : ℝ)*X 1 1+(2696576859/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312440557/10000000000 : ℝ)*X 2 0+(1348288407/2500000000 : ℝ)*X 2 1+(-264631243/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4368502597/10000000000 : ℝ)*X 0 0+(899298627/2000000000 : ℝ)*X 0 1+(53052253/125000000 : ℝ)*X 0 2+(4368502597/10000000000 : ℝ)*X 1 0+(899298627/2000000000 : ℝ)*X 1 1+(53052253/125000000 : ℝ)*X 1 2+(4368502597/10000000000 : ℝ)*X 2 0+(899298627/2000000000 : ℝ)*X 2 1+(53052253/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1115_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (554330155196891138352790047/61750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1779878257/100000000000000 : ℝ)*(base19) + (165495149/10000000000000 : ℝ)*(base23) + (65990973/100000000000000 : ℝ)*(lower2) + (45623073/20000000000000 : ℝ)*(upper3) + (33389939/25000000000000 : ℝ)*(upper5) + (5873677093042009/100000000000000 : ℝ)*(major0) + (5873677093042009/100000000000000 : ℝ)*(major1) + (5873677093042009/100000000000000 : ℝ)*(major2) + (1560768521759151/20000000000000 : ℝ)*(sp0) + (3901944486471323/50000000000000 : ℝ)*(sp1) + (7803889097869413/100000000000000 : ℝ)*(sp2) + (1971718375942027/50000000000000 : ℝ)*(sp3) + (12036006287/25000000000000 : ℝ)*(sp4) + (26382145499/100000000000000 : ℝ)*(sp7) + (3943463134029553/100000000000000 : ℝ)*(f.failure) + (3901945376410451/50000000000000 : ℝ)*(f.sum) + (355272172559/308750000000000000000000000 : ℝ)*base66 + (440694684941686651/247000000000000000000000000000000 : ℝ)*base68 + (666374185130686651/247000000000000000000000000000000 : ℝ)*base70 + (2143752993780313349/247000000000000000000000000000000 : ℝ)*base71 + (1269000201579/1235000000000000000000000000 : ℝ)*base73 + (2835307187314686651/247000000000000000000000000000000 : ℝ)*base76 + (2136044370217686651/247000000000000000000000000000000 : ℝ)*base78 + (348059838780686651/247000000000000000000000000000000 : ℝ)*base80 + (4302730024171/1235000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (78019013/10000000000000000000000 : ℝ)*base90 + (78019013/10000000000000000000000 : ℝ)*base92 + (78019013/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (499929947491676661099/47500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1716732119/100000000000000 : ℝ)*(base19) + (513734767/25000000000000 : ℝ)*(base23) + (638213221/100000000000000 : ℝ)*(lower1) + (25258847/12500000000000 : ℝ)*(upper3) + (92883457/100000000000000 : ℝ)*(lower4) + (197430521/100000000000000 : ℝ)*(upper5) + (5903234834906487/100000000000000 : ℝ)*(major0) + (5903234834906487/100000000000000 : ℝ)*(major1) + (5903234834906487/100000000000000 : ℝ)*(major2) + (5725787081/100000000000000 : ℝ)*(sp2) + (1568632347877101/20000000000000 : ℝ)*(sp4) + (3921580011326693/50000000000000 : ℝ)*(sp5) + (1960788489664839/25000000000000 : ℝ)*(sp6) + (19816537897997/500000000000 : ℝ)*(sp7) + (19816537897997/500000000000 : ℝ)*(f.failure) + (1568632347877101/20000000000000 : ℝ)*(f.sum) + (143410566399/95000000000000000000000000 : ℝ)*base65 + (843591487185330761/19000000000000000000000000000000 : ℝ)*base68 + (71737135449669239/19000000000000000000000000000000 : ℝ)*base69 + (253412352994669239/19000000000000000000000000000000 : ℝ)*base71 + (14563511231/5937500000000000000000000 : ℝ)*base74 + (3712804813637330761/19000000000000000000000000000000 : ℝ)*base76 + (45337168266669239/19000000000000000000000000000000 : ℝ)*base77 + (554449519770330761/19000000000000000000000000000000 : ℝ)*base80 + (410191593319/95000000000000000000000000 : ℝ)*base81 + (599537/50000000000000000000 : ℝ)*base90 + (599537/50000000000000000000 : ℝ)*base92 + (599537/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1115_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7017/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11317/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1115_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1115_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (451/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1115_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1115_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1115_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8307/2048 : ℝ) ≤ p) (hpb : p ≤ (2077/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148947179/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7039/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (451/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5659/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14033/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1115_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1282_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:23:38.540752+00:00
-- url     : https://prove2.me/submissions/01413d82-a27e-4f5a-9698-e1c5a5ab1b4c

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
theorem support_rectangle_w1282_s3_0 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2094469267/10000000000 : ℝ)*x 0 + (5435595431/10000000000 : ℝ)*x 1 + (1044882173/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2094469267/10000000000 : ℝ)^2121 ≤ (6367997806469/50000000000000 : ℝ)^1609 := by
    have hnat : (2094469267 : ℕ)^2121*50000000000000^1609 ≤ 6367997806469^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2094469267 10000000000 6367997806469 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435595431/10000000000 : ℝ)^2121 ≤ (5596417519093/12500000000000 : ℝ)^1609 := by
    have hnat : (5435595431 : ℕ)^2121*12500000000000^1609 ≤ 5596417519093^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435595431 10000000000 5596417519093 12500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044882173/2000000000 : ℝ)^2121 ≤ (42492664225971/100000000000000 : ℝ)^1609 := by
    have hnat : (1044882173 : ℕ)^2121*100000000000000^1609 ≤ 42492664225971^1609*2000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044882173 2000000000 42492664225971 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2094469267/10000000000 : ℝ), (5435595431/10000000000 : ℝ), (1044882173/2000000000 : ℝ)] ![(6367997806469/50000000000000 : ℝ), (5596417519093/12500000000000 : ℝ), (42492664225971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2094469267/10000000000 : ℝ)|^2121 ≤ (6367997806469/50000000000000 : ℝ)^1609
        have hw : |(-2094469267/10000000000 : ℝ)|=(2094469267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435595431/10000000000 : ℝ)|^2121 ≤ (5596417519093/12500000000000 : ℝ)^1609
        have hw : |(5435595431/10000000000 : ℝ)|=(5435595431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1044882173/2000000000 : ℝ)|^2121 ≤ (42492664225971/100000000000000 : ℝ)^1609
        have hw : |(1044882173/2000000000 : ℝ)|=(1044882173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s3_1 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (167341871/312500000 : ℝ)*x 0 + (-220258451/1000000000 : ℝ)*x 1 + (5224410827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167341871/312500000 : ℝ)^2121 ≤ (8779536257109/20000000000000 : ℝ)^1609 := by
    have hnat : (167341871 : ℕ)^2121*20000000000000^1609 ≤ 8779536257109^1609*312500000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167341871 312500000 8779536257109 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220258451/1000000000 : ℝ)^2121 ≤ (3402413719443/25000000000000 : ℝ)^1609 := by
    have hnat : (220258451 : ℕ)^2121*25000000000000^1609 ≤ 3402413719443^1609*1000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220258451 1000000000 3402413719443 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5224410827/10000000000 : ℝ)^2121 ≤ (42492663818549/100000000000000 : ℝ)^1609 := by
    have hnat : (5224410827 : ℕ)^2121*100000000000000^1609 ≤ 42492663818549^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224410827 10000000000 42492663818549 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167341871/312500000 : ℝ), (-220258451/1000000000 : ℝ), (5224410827/10000000000 : ℝ)] ![(8779536257109/20000000000000 : ℝ), (3402413719443/25000000000000 : ℝ), (42492663818549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167341871/312500000 : ℝ)|^2121 ≤ (8779536257109/20000000000000 : ℝ)^1609
        have hw : |(167341871/312500000 : ℝ)|=(167341871/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-220258451/1000000000 : ℝ)|^2121 ≤ (3402413719443/25000000000000 : ℝ)^1609
        have hw : |(-220258451/1000000000 : ℝ)|=(220258451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5224410827/10000000000 : ℝ)|^2121 ≤ (42492663818549/100000000000000 : ℝ)^1609
        have hw : |(5224410827/10000000000 : ℝ)|=(5224410827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s3_2 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (214197591/400000000 : ℝ)*x 0 + (130610281/250000000 : ℝ)*x 1 + (-68830753/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214197591/400000000 : ℝ)^2121 ≤ (43897680237347/100000000000000 : ℝ)^1609 := by
    have hnat : (214197591 : ℕ)^2121*100000000000000^1609 ≤ 43897680237347^1609*400000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214197591 400000000 43897680237347 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130610281/250000000 : ℝ)^2121 ≤ (42492668246587/100000000000000 : ℝ)^1609 := by
    have hnat : (130610281 : ℕ)^2121*100000000000000^1609 ≤ 42492668246587^1609*250000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130610281 250000000 42492668246587 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (68830753/312500000 : ℝ)^2121 ≤ (170120643821/1250000000000 : ℝ)^1609 := by
    have hnat : (68830753 : ℕ)^2121*1250000000000^1609 ≤ 170120643821^1609*312500000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68830753 312500000 170120643821 1250000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214197591/400000000 : ℝ), (130610281/250000000 : ℝ), (-68830753/312500000 : ℝ)] ![(43897680237347/100000000000000 : ℝ), (42492668246587/100000000000000 : ℝ), (170120643821/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214197591/400000000 : ℝ)|^2121 ≤ (43897680237347/100000000000000 : ℝ)^1609
        have hw : |(214197591/400000000 : ℝ)|=(214197591/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130610281/250000000 : ℝ)|^2121 ≤ (42492668246587/100000000000000 : ℝ)^1609
        have hw : |(130610281/250000000 : ℝ)|=(130610281/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-68830753/312500000 : ℝ)|^2121 ≤ (170120643821/1250000000000 : ℝ)^1609
        have hw : |(-68830753/312500000 : ℝ)|=(68830753/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s3_3 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2170527237/5000000000 : ℝ)*x 0 + (2065016173/5000000000 : ℝ)*x 1 + (228120411/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170527237/5000000000 : ℝ)^2121 ≤ (16643489836437/50000000000000 : ℝ)^1609 := by
    have hnat : (2170527237 : ℕ)^2121*50000000000000^1609 ≤ 16643489836437^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170527237 5000000000 16643489836437 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065016173/5000000000 : ℝ)^2121 ≤ (3117065835141/10000000000000 : ℝ)^1609 := by
    have hnat : (2065016173 : ℕ)^2121*10000000000000^1609 ≤ 3117065835141^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065016173 5000000000 3117065835141 10000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228120411/500000000 : ℝ)^2121 ≤ (35542361958627/100000000000000 : ℝ)^1609 := by
    have hnat : (228120411 : ℕ)^2121*100000000000000^1609 ≤ 35542361958627^1609*500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228120411 500000000 35542361958627 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170527237/5000000000 : ℝ), (2065016173/5000000000 : ℝ), (228120411/500000000 : ℝ)] ![(16643489836437/50000000000000 : ℝ), (3117065835141/10000000000000 : ℝ), (35542361958627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170527237/5000000000 : ℝ)|^2121 ≤ (16643489836437/50000000000000 : ℝ)^1609
        have hw : |(2170527237/5000000000 : ℝ)|=(2170527237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2065016173/5000000000 : ℝ)|^2121 ≤ (3117065835141/10000000000000 : ℝ)^1609
        have hw : |(2065016173/5000000000 : ℝ)|=(2065016173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(228120411/500000000 : ℝ)|^2121 ≤ (35542361958627/100000000000000 : ℝ)^1609
        have hw : |(228120411/500000000 : ℝ)|=(228120411/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s3_4 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1047246309/5000000000 : ℝ)*x 0 + (5225327223/10000000000 : ℝ)*x 1 + (2717336633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047246309/5000000000 : ℝ)^2121 ≤ (12736182788777/100000000000000 : ℝ)^1609 := by
    have hnat : (1047246309 : ℕ)^2121*100000000000000^1609 ≤ 12736182788777^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047246309 5000000000 12736182788777 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5225327223/10000000000 : ℝ)^2121 ≤ (2125124468083/5000000000000 : ℝ)^1609 := by
    have hnat : (5225327223 : ℕ)^2121*5000000000000^1609 ≤ 2125124468083^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225327223 10000000000 2125124468083 5000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717336633/5000000000 : ℝ)^2121 ≤ (44761327837723/100000000000000 : ℝ)^1609 := by
    have hnat : (2717336633 : ℕ)^2121*100000000000000^1609 ≤ 44761327837723^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717336633 5000000000 44761327837723 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1047246309/5000000000 : ℝ), (5225327223/10000000000 : ℝ), (2717336633/5000000000 : ℝ)] ![(12736182788777/100000000000000 : ℝ), (2125124468083/5000000000000 : ℝ), (44761327837723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1047246309/5000000000 : ℝ)|^2121 ≤ (12736182788777/100000000000000 : ℝ)^1609
        have hw : |(-1047246309/5000000000 : ℝ)|=(1047246309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5225327223/10000000000 : ℝ)|^2121 ≤ (2125124468083/5000000000000 : ℝ)^1609
        have hw : |(5225327223/10000000000 : ℝ)|=(5225327223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717336633/5000000000 : ℝ)|^2121 ≤ (44761327837723/100000000000000 : ℝ)^1609
        have hw : |(2717336633/5000000000 : ℝ)|=(2717336633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s3_5 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2650467657/5000000000 : ℝ)*x 0 + (-1992322003/10000000000 : ℝ)*x 1 + (2717336601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650467657/5000000000 : ℝ)^2121 ≤ (21657518830371/50000000000000 : ℝ)^1609 := by
    have hnat : (2650467657 : ℕ)^2121*50000000000000^1609 ≤ 21657518830371^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650467657 5000000000 21657518830371 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1992322003/10000000000 : ℝ)^2121 ≤ (11923635183103/100000000000000 : ℝ)^1609 := by
    have hnat : (1992322003 : ℕ)^2121*100000000000000^1609 ≤ 11923635183103^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992322003 10000000000 11923635183103 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717336601/5000000000 : ℝ)^2121 ≤ (11190331785717/25000000000000 : ℝ)^1609 := by
    have hnat : (2717336601 : ℕ)^2121*25000000000000^1609 ≤ 11190331785717^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717336601 5000000000 11190331785717 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650467657/5000000000 : ℝ), (-1992322003/10000000000 : ℝ), (2717336601/5000000000 : ℝ)] ![(21657518830371/50000000000000 : ℝ), (11923635183103/100000000000000 : ℝ), (11190331785717/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650467657/5000000000 : ℝ)|^2121 ≤ (21657518830371/50000000000000 : ℝ)^1609
        have hw : |(2650467657/5000000000 : ℝ)|=(2650467657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1992322003/10000000000 : ℝ)|^2121 ≤ (11923635183103/100000000000000 : ℝ)^1609
        have hw : |(-1992322003/10000000000 : ℝ)|=(1992322003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717336601/5000000000 : ℝ)|^2121 ≤ (11190331785717/25000000000000 : ℝ)^1609
        have hw : |(2717336601/5000000000 : ℝ)|=(2717336601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s3_6 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1325233831/2500000000 : ℝ)*x 0 + (679334147/1250000000 : ℝ)*x 1 + (-79692881/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325233831/2500000000 : ℝ)^2121 ≤ (5414379721057/12500000000000 : ℝ)^1609 := by
    have hnat : (1325233831 : ℕ)^2121*12500000000000^1609 ≤ 5414379721057^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325233831 2500000000 5414379721057 12500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679334147/1250000000 : ℝ)^2121 ≤ (5595165857573/12500000000000 : ℝ)^1609 := by
    have hnat : (679334147 : ℕ)^2121*12500000000000^1609 ≤ 5595165857573^1609*1250000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679334147 1250000000 5595165857573 12500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79692881/400000000 : ℝ)^2121 ≤ (5961817678333/50000000000000 : ℝ)^1609 := by
    have hnat : (79692881 : ℕ)^2121*50000000000000^1609 ≤ 5961817678333^1609*400000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79692881 400000000 5961817678333 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325233831/2500000000 : ℝ), (679334147/1250000000 : ℝ), (-79692881/400000000 : ℝ)] ![(5414379721057/12500000000000 : ℝ), (5595165857573/12500000000000 : ℝ), (5961817678333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325233831/2500000000 : ℝ)|^2121 ≤ (5414379721057/12500000000000 : ℝ)^1609
        have hw : |(1325233831/2500000000 : ℝ)|=(1325233831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679334147/1250000000 : ℝ)|^2121 ≤ (5595165857573/12500000000000 : ℝ)^1609
        have hw : |(679334147/1250000000 : ℝ)|=(679334147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-79692881/400000000 : ℝ)|^2121 ≤ (5961817678333/50000000000000 : ℝ)^1609
        have hw : |(-79692881/400000000 : ℝ)|=(79692881/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s3_7 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4341102449/10000000000 : ℝ)*x 0 + (142516627/312500000 : ℝ)*x 1 + (413191989/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4341102449/10000000000 : ℝ)^2121 ≤ (8321866150851/25000000000000 : ℝ)^1609 := by
    have hnat : (4341102449 : ℕ)^2121*25000000000000^1609 ≤ 8321866150851^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341102449 10000000000 8321866150851 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142516627/312500000 : ℝ)^2121 ≤ (7104619318233/20000000000000 : ℝ)^1609 := by
    have hnat : (142516627 : ℕ)^2121*20000000000000^1609 ≤ 7104619318233^1609*312500000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142516627 312500000 7104619318233 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413191989/1000000000 : ℝ)^2121 ≤ (31189438793277/100000000000000 : ℝ)^1609 := by
    have hnat : (413191989 : ℕ)^2121*100000000000000^1609 ≤ 31189438793277^1609*1000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413191989 1000000000 31189438793277 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4341102449/10000000000 : ℝ), (142516627/312500000 : ℝ), (413191989/1000000000 : ℝ)] ![(8321866150851/25000000000000 : ℝ), (7104619318233/20000000000000 : ℝ), (31189438793277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4341102449/10000000000 : ℝ)|^2121 ≤ (8321866150851/25000000000000 : ℝ)^1609
        have hw : |(4341102449/10000000000 : ℝ)|=(4341102449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142516627/312500000 : ℝ)|^2121 ≤ (7104619318233/20000000000000 : ℝ)^1609
        have hw : |(142516627/312500000 : ℝ)|=(142516627/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(413191989/1000000000 : ℝ)|^2121 ≤ (31189438793277/100000000000000 : ℝ)^1609
        have hw : |(413191989/1000000000 : ℝ)|=(413191989/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1282_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (943/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10613/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (377/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4091/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (943/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4091/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (943/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4091/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (943/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4091/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (943/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4091/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (943/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4091/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (943/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (943/10000 : ℝ) ^ (4241/1024 : ℝ) ≤ (5660255355768909/100000000000000000000 : ℝ) := by
    have hpowers : (943/10000 : ℝ)^4241 ≤ (5660255355768909/100000000000000000000 : ℝ)^1024 := by
      have hnat : (943 : ℕ)^4241*100000000000000000000^1024 ≤ 5660255355768909^1024*10000^4241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        943 10000 5660255355768909 100000000000000000000 4241 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (943/10000 : ℝ)) (X := (5660255355768909/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4091/25000 : ℝ) ^ (4241/1024 : ℝ) ≤ (54193031721851/97656250000000000 : ℝ) := by
    have hpowers : (4091/25000 : ℝ)^4241 ≤ (54193031721851/97656250000000000 : ℝ)^1024 := by
      have hnat : (4091 : ℕ)^4241*97656250000000000^1024 ≤ 54193031721851^1024*25000^4241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4091 25000 54193031721851 97656250000000000 4241 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4091/25000 : ℝ)) (X := (54193031721851/97656250000000000 : ℝ)) (by norm_num) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005660255355768909/50000000000000000000 : ℝ) ≤ (250006833120303/250000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (50005660255355768909/50000000000000000000 : ℝ)^1024 ≤ (250006833120303/250000000000000 : ℝ)^4241 := by
      have hnat : (50005660255355768909 : ℕ)^1024*250000000000000^4241 ≤ 250006833120303^4241*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005660255355768909 50000000000000000000 250006833120303 250000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250006833120303/250000000000000 : ℝ)) (X := (50005660255355768909/50000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100061153919838944333/100000000000000000000 : ℝ) ≤ (10001476234251693/10000000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (100061153919838944333/100000000000000000000 : ℝ)^1024 ≤ (10001476234251693/10000000000000000 : ℝ)^4241 := by
      have hnat : (100061153919838944333 : ℕ)^1024*10000000000000000^4241 ≤ 10001476234251693^4241*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100061153919838944333 100000000000000000000 10001476234251693 10000000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001476234251693/10000000000000000 : ℝ)) (X := (100061153919838944333/100000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (48882318031721851/48828125000000000 : ℝ) ≤ (5001339571845633/5000000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (48882318031721851/48828125000000000 : ℝ)^1024 ≤ (5001339571845633/5000000000000000 : ℝ)^4241 := by
      have hnat : (48882318031721851 : ℕ)^1024*5000000000000000^4241 ≤ 5001339571845633^4241*48828125000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48882318031721851 48828125000000000 5001339571845633 5000000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001339571845633/5000000000000000 : ℝ)) (X := (48882318031721851/48828125000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5660255355768909/100000000000000000000 : ℝ) ≤ ((693192083622168933/693400000000000000 : ℝ)+2*(1202909439573/693400000000000 : ℝ)*(943/10000 : ℝ))^(4241/1024 : ℝ) := by
    rw [show (693192083622168933/693400000000000000 : ℝ)+2*(1202909439573/693400000000000 : ℝ)*(943/10000 : ℝ)=(250006833120303/250000000000000 : ℝ) by norm_num, show 1+2*(5660255355768909/100000000000000000000 : ℝ)=(50005660255355768909/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(54193031721851/97656250000000000 : ℝ)+(5660255355768909/100000000000000000000 : ℝ) ≤ ((693192083622168933/693400000000000000 : ℝ)+(1202909439573/693400000000000 : ℝ)*((4091/25000 : ℝ)+(943/10000 : ℝ)))^(4241/1024 : ℝ) := by
    rw [show (693192083622168933/693400000000000000 : ℝ)+(1202909439573/693400000000000 : ℝ)*((4091/25000 : ℝ)+(943/10000 : ℝ))=(10001476234251693/10000000000000000 : ℝ) by norm_num, show 1+(54193031721851/97656250000000000 : ℝ)+(5660255355768909/100000000000000000000 : ℝ)=(100061153919838944333/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(54193031721851/97656250000000000 : ℝ) ≤ ((693192083622168933/693400000000000000 : ℝ)+2*(1202909439573/693400000000000 : ℝ)*(4091/25000 : ℝ))^(4241/1024 : ℝ) := by
    rw [show (693192083622168933/693400000000000000 : ℝ)+2*(1202909439573/693400000000000 : ℝ)*(4091/25000 : ℝ)=(5001339571845633/5000000000000000 : ℝ) by norm_num, show 1+2*(54193031721851/97656250000000000 : ℝ)=(48882318031721851/48828125000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (693192083622168933/693400000000000000 : ℝ)*(X 1 0+X 2 0)+(1202909439573/693400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (943/10000 : ℝ)) (hi := (4091/25000 : ℝ)) (c := (693192083622168933/693400000000000000 : ℝ)) (alpha := (1202909439573/693400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (693192083622168933/693400000000000000 : ℝ)*(X 0 1+X 2 1)+(1202909439573/693400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (943/10000 : ℝ)) (hi := (4091/25000 : ℝ)) (c := (693192083622168933/693400000000000000 : ℝ)) (alpha := (1202909439573/693400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (693192083622168933/693400000000000000 : ℝ)*(X 0 2+X 1 2)+(1202909439573/693400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (943/10000 : ℝ)) (hi := (4091/25000 : ℝ)) (c := (693192083622168933/693400000000000000 : ℝ)) (alpha := (1202909439573/693400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2094469267/10000000000 : ℝ)*X 0 0+(5435595431/10000000000 : ℝ)*X 0 1+(1044882173/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167341871/312500000 : ℝ)*X 1 0+(-220258451/1000000000 : ℝ)*X 1 1+(5224410827/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214197591/400000000 : ℝ)*X 2 0+(130610281/250000000 : ℝ)*X 2 1+(-68830753/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2170527237/5000000000 : ℝ)*X 0 0+(2065016173/5000000000 : ℝ)*X 0 1+(228120411/500000000 : ℝ)*X 0 2+(2170527237/5000000000 : ℝ)*X 1 0+(2065016173/5000000000 : ℝ)*X 1 1+(228120411/500000000 : ℝ)*X 1 2+(2170527237/5000000000 : ℝ)*X 2 0+(2065016173/5000000000 : ℝ)*X 2 1+(228120411/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1047246309/5000000000 : ℝ)*X 0 0+(5225327223/10000000000 : ℝ)*X 0 1+(2717336633/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2650467657/5000000000 : ℝ)*X 1 0+(-1992322003/10000000000 : ℝ)*X 1 1+(2717336601/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325233831/2500000000 : ℝ)*X 2 0+(679334147/1250000000 : ℝ)*X 2 1+(-79692881/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4341102449/10000000000 : ℝ)*X 0 0+(142516627/312500000 : ℝ)*X 0 1+(413191989/1000000000 : ℝ)*X 0 2+(4341102449/10000000000 : ℝ)*X 1 0+(142516627/312500000 : ℝ)*X 1 1+(413191989/1000000000 : ℝ)*X 1 2+(4341102449/10000000000 : ℝ)*X 2 0+(142516627/312500000 : ℝ)*X 2 1+(413191989/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (129236036313808766523393/34670000000000000000000000000 : ℝ) := by norm_num
    linear_combination (149335173/25000000000000 : ℝ)*(base19) + (130671139/25000000000000 : ℝ)*(base23) + (14925901/50000000000000 : ℝ)*(upper4) + (78410569/100000000000000 : ℝ)*(upper5) + (3524023579439133/100000000000000 : ℝ)*(major0) + (3524023579439133/100000000000000 : ℝ)*(major1) + (3524023579439133/100000000000000 : ℝ)*(major2) + (4735210952908697/100000000000000 : ℝ)*(sp0) + (4735223066898199/100000000000000 : ℝ)*(sp1) + (2367614885832363/50000000000000 : ℝ)*(sp2) + (578202507560747/25000000000000 : ℝ)*(sp3) + (3868288117/20000000000000 : ℝ)*(sp4) + (6630110391/100000000000000 : ℝ)*(sp5) + (1677508129/25000000000000 : ℝ)*(sp7) + (144551046267219/6250000000000 : ℝ)*(f.failure) + (2367615147174641/50000000000000 : ℝ)*(f.sum) + (202419224476319/34670000000000000000000000000 : ℝ)*base65 + (291011985291704089/69340000000000000000000000000000 : ℝ)*base67 + (86680430833164089/69340000000000000000000000000000 : ℝ)*base69 + (972275856055911/69340000000000000000000000000000 : ℝ)*base72 + (283629925924179/34670000000000000000000000000 : ℝ)*base73 + (693058203600435911/69340000000000000000000000000000 : ℝ)*base76 + (507876655093624089/69340000000000000000000000000000 : ℝ)*base77 + (237012903658815911/69340000000000000000000000000000 : ℝ)*base80 + (4691157351471/34670000000000000000000000000 : ℝ)*base82 + (4851759/625000000000000000000 : ℝ)*base90 + (4851759/625000000000000000000 : ℝ)*base92 + (4851759/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (250615862301032574706994169/34670000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (172325399/10000000000000 : ℝ)*(base19) + (89684107/5000000000000 : ℝ)*(base23) + (164430777/100000000000000 : ℝ)*(upper3) + (32953639/100000000000000 : ℝ)*(lower4) + (96108351/50000000000000 : ℝ)*(upper5) + (3554945790804877/100000000000000 : ℝ)*(major0) + (3554945790804877/100000000000000 : ℝ)*(major1) + (3554945790804877/100000000000000 : ℝ)*(major2) + (28141962633/100000000000000 : ℝ)*(sp1) + (28068522571/100000000000000 : ℝ)*(sp2) + (2388390176245071/50000000000000 : ℝ)*(sp4) + (4776750487273519/100000000000000 : ℝ)*(sp5) + (4776750490285431/100000000000000 : ℝ)*(sp6) + (72909718380187/3125000000000 : ℝ)*(sp7) + (72909718380187/3125000000000 : ℝ)*(f.failure) + (2388390176245071/50000000000000 : ℝ)*(f.sum) + (187123681292679/34670000000000000000000000000 : ℝ)*base66 + (734320766424472759/69340000000000000000000000000000 : ℝ)*base68 + (17076050257072759/69340000000000000000000000000000 : ℝ)*base70 + (141866015807912759/69340000000000000000000000000000 : ℝ)*base72 + (254190526413109/34670000000000000000000000000 : ℝ)*base74 + (528265893019452759/69340000000000000000000000000000 : ℝ)*base76 + (608778917368092759/69340000000000000000000000000000 : ℝ)*base78 + (438492836112672759/69340000000000000000000000000000 : ℝ)*base80 + (23042709571709/34670000000000000000000000000 : ℝ)*base82 + (3261393/312500000000000000000 : ℝ)*base89 + (3261393/312500000000000000000 : ℝ)*base91 + (3261393/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1282_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (943/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10613/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (377/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1282_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1282_s4_0 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2096496579/10000000000 : ℝ)*x 0 + (2709856679/5000000000 : ℝ)*x 1 + (5238964649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096496579/10000000000 : ℝ)^2121 ≤ (12752248517573/100000000000000 : ℝ)^1609 := by
    have hnat : (2096496579 : ℕ)^2121*100000000000000^1609 ≤ 12752248517573^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096496579 10000000000 12752248517573 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709856679/5000000000 : ℝ)^2121 ≤ (8919795536923/20000000000000 : ℝ)^1609 := by
    have hnat : (2709856679 : ℕ)^2121*20000000000000^1609 ≤ 8919795536923^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709856679 5000000000 8919795536923 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238964649/10000000000 : ℝ)^2121 ≤ (42648773790461/100000000000000 : ℝ)^1609 := by
    have hnat : (5238964649 : ℕ)^2121*100000000000000^1609 ≤ 42648773790461^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238964649 10000000000 42648773790461 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2096496579/10000000000 : ℝ), (2709856679/5000000000 : ℝ), (5238964649/10000000000 : ℝ)] ![(12752248517573/100000000000000 : ℝ), (8919795536923/20000000000000 : ℝ), (42648773790461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2096496579/10000000000 : ℝ)|^2121 ≤ (12752248517573/100000000000000 : ℝ)^1609
        have hw : |(-2096496579/10000000000 : ℝ)|=(2096496579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709856679/5000000000 : ℝ)|^2121 ≤ (8919795536923/20000000000000 : ℝ)^1609
        have hw : |(2709856679/5000000000 : ℝ)|=(2709856679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238964649/10000000000 : ℝ)|^2121 ≤ (42648773790461/100000000000000 : ℝ)^1609
        have hw : |(5238964649/10000000000 : ℝ)|=(5238964649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s4_1 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267546653/500000000 : ℝ)*x 0 + (-547179937/2500000000 : ℝ)*x 1 + (1309741173/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267546653/500000000 : ℝ)^2121 ≤ (8770877633651/20000000000000 : ℝ)^1609 := by
    have hnat : (267546653 : ℕ)^2121*20000000000000^1609 ≤ 8770877633651^1609*500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267546653 500000000 8770877633651 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547179937/2500000000 : ℝ)^2121 ≤ (13496837559079/100000000000000 : ℝ)^1609 := by
    have hnat : (547179937 : ℕ)^2121*100000000000000^1609 ≤ 13496837559079^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547179937 2500000000 13496837559079 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309741173/2500000000 : ℝ)^2121 ≤ (426487742519/1000000000000 : ℝ)^1609 := by
    have hnat : (1309741173 : ℕ)^2121*1000000000000^1609 ≤ 426487742519^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309741173 2500000000 426487742519 1000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267546653/500000000 : ℝ), (-547179937/2500000000 : ℝ), (1309741173/2500000000 : ℝ)] ![(8770877633651/20000000000000 : ℝ), (13496837559079/100000000000000 : ℝ), (426487742519/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267546653/500000000 : ℝ)|^2121 ≤ (8770877633651/20000000000000 : ℝ)^1609
        have hw : |(267546653/500000000 : ℝ)|=(267546653/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-547179937/2500000000 : ℝ)|^2121 ≤ (13496837559079/100000000000000 : ℝ)^1609
        have hw : |(-547179937/2500000000 : ℝ)|=(547179937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1309741173/2500000000 : ℝ)|^2121 ≤ (426487742519/1000000000000 : ℝ)^1609
        have hw : |(1309741173/2500000000 : ℝ)|=(1309741173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s4_2 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337733221/2500000000 : ℝ)*x 0 + (5238964843/10000000000 : ℝ)*x 1 + (-2188719783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337733221/2500000000 : ℝ)^2121 ≤ (43854386266823/100000000000000 : ℝ)^1609 := by
    have hnat : (1337733221 : ℕ)^2121*100000000000000^1609 ≤ 43854386266823^1609*2500000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337733221 2500000000 43854386266823 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238964843/10000000000 : ℝ)^2121 ≤ (21324387936151/50000000000000 : ℝ)^1609 := by
    have hnat : (5238964843 : ℕ)^2121*50000000000000^1609 ≤ 21324387936151^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238964843 10000000000 21324387936151 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2188719783/10000000000 : ℝ)^2121 ≤ (13496837843587/100000000000000 : ℝ)^1609 := by
    have hnat : (2188719783 : ℕ)^2121*100000000000000^1609 ≤ 13496837843587^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188719783 10000000000 13496837843587 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337733221/2500000000 : ℝ), (5238964843/10000000000 : ℝ), (-2188719783/10000000000 : ℝ)] ![(43854386266823/100000000000000 : ℝ), (21324387936151/50000000000000 : ℝ), (13496837843587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337733221/2500000000 : ℝ)|^2121 ≤ (43854386266823/100000000000000 : ℝ)^1609
        have hw : |(1337733221/2500000000 : ℝ)|=(1337733221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238964843/10000000000 : ℝ)|^2121 ≤ (21324387936151/50000000000000 : ℝ)^1609
        have hw : |(5238964843/10000000000 : ℝ)|=(5238964843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2188719783/10000000000 : ℝ)|^2121 ≤ (13496837843587/100000000000000 : ℝ)^1609
        have hw : |(-2188719783/10000000000 : ℝ)|=(2188719783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s4_3 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4342280213/10000000000 : ℝ)*x 0 + (2080517147/5000000000 : ℝ)*x 1 + (4531096499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342280213/10000000000 : ℝ)^2121 ≤ (33299369957787/100000000000000 : ℝ)^1609 := by
    have hnat : (4342280213 : ℕ)^2121*100000000000000^1609 ≤ 33299369957787^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342280213 10000000000 33299369957787 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080517147/5000000000 : ℝ)^2121 ≤ (31479462854341/100000000000000 : ℝ)^1609 := by
    have hnat : (2080517147 : ℕ)^2121*100000000000000^1609 ≤ 31479462854341^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080517147 5000000000 31479462854341 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4531096499/10000000000 : ℝ)^2121 ≤ (7044233434871/20000000000000 : ℝ)^1609 := by
    have hnat : (4531096499 : ℕ)^2121*20000000000000^1609 ≤ 7044233434871^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531096499 10000000000 7044233434871 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342280213/10000000000 : ℝ), (2080517147/5000000000 : ℝ), (4531096499/10000000000 : ℝ)] ![(33299369957787/100000000000000 : ℝ), (31479462854341/100000000000000 : ℝ), (7044233434871/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342280213/10000000000 : ℝ)|^2121 ≤ (33299369957787/100000000000000 : ℝ)^1609
        have hw : |(4342280213/10000000000 : ℝ)|=(4342280213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2080517147/5000000000 : ℝ)|^2121 ≤ (31479462854341/100000000000000 : ℝ)^1609
        have hw : |(2080517147/5000000000 : ℝ)|=(2080517147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4531096499/10000000000 : ℝ)|^2121 ≤ (7044233434871/20000000000000 : ℝ)^1609
        have hw : |(4531096499/10000000000 : ℝ)|=(4531096499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s4_4 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2096511317/10000000000 : ℝ)*x 0 + (5239636547/10000000000 : ℝ)*x 1 + (5419037751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096511317/10000000000 : ℝ)^2121 ≤ (797022918127/6250000000000 : ℝ)^1609 := by
    have hnat : (2096511317 : ℕ)^2121*6250000000000^1609 ≤ 797022918127^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096511317 10000000000 797022918127 6250000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239636547/10000000000 : ℝ)^2121 ≤ (42655984166511/100000000000000 : ℝ)^1609 := by
    have hnat : (5239636547 : ℕ)^2121*100000000000000^1609 ≤ 42655984166511^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239636547 10000000000 42655984166511 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419037751/10000000000 : ℝ)^2121 ≤ (4459164912311/10000000000000 : ℝ)^1609 := by
    have hnat : (5419037751 : ℕ)^2121*10000000000000^1609 ≤ 4459164912311^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419037751 10000000000 4459164912311 10000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2096511317/10000000000 : ℝ), (5239636547/10000000000 : ℝ), (5419037751/10000000000 : ℝ)] ![(797022918127/6250000000000 : ℝ), (42655984166511/100000000000000 : ℝ), (4459164912311/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2096511317/10000000000 : ℝ)|^2121 ≤ (797022918127/6250000000000 : ℝ)^1609
        have hw : |(-2096511317/10000000000 : ℝ)|=(2096511317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239636547/10000000000 : ℝ)|^2121 ≤ (42655984166511/100000000000000 : ℝ)^1609
        have hw : |(5239636547/10000000000 : ℝ)|=(5239636547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419037751/10000000000 : ℝ)|^2121 ≤ (4459164912311/10000000000000 : ℝ)^1609
        have hw : |(5419037751/10000000000 : ℝ)|=(5419037751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s4_5 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5304715347/10000000000 : ℝ)*x 0 + (-2008646643/10000000000 : ℝ)*x 1 + (5419037853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304715347/10000000000 : ℝ)^2121 ≤ (5419469800189/12500000000000 : ℝ)^1609 := by
    have hnat : (5304715347 : ℕ)^2121*12500000000000^1609 ≤ 5419469800189^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304715347 10000000000 5419469800189 12500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008646643/10000000000 : ℝ)^2121 ≤ (12052591358651/100000000000000 : ℝ)^1609 := by
    have hnat : (2008646643 : ℕ)^2121*100000000000000^1609 ≤ 12052591358651^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008646643 10000000000 12052591358651 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419037853/10000000000 : ℝ)^2121 ≤ (557395627869/1250000000000 : ℝ)^1609 := by
    have hnat : (5419037853 : ℕ)^2121*1250000000000^1609 ≤ 557395627869^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419037853 10000000000 557395627869 1250000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304715347/10000000000 : ℝ), (-2008646643/10000000000 : ℝ), (5419037853/10000000000 : ℝ)] ![(5419469800189/12500000000000 : ℝ), (12052591358651/100000000000000 : ℝ), (557395627869/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304715347/10000000000 : ℝ)|^2121 ≤ (5419469800189/12500000000000 : ℝ)^1609
        have hw : |(5304715347/10000000000 : ℝ)|=(5304715347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2008646643/10000000000 : ℝ)|^2121 ≤ (12052591358651/100000000000000 : ℝ)^1609
        have hw : |(-2008646643/10000000000 : ℝ)|=(2008646643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419037853/10000000000 : ℝ)|^2121 ≤ (557395627869/1250000000000 : ℝ)^1609
        have hw : |(5419037853/10000000000 : ℝ)|=(5419037853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s4_6 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652357681/5000000000 : ℝ)*x 0 + (2709518873/5000000000 : ℝ)*x 1 + (-2008646769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652357681/5000000000 : ℝ)^2121 ≤ (43355758563119/100000000000000 : ℝ)^1609 := by
    have hnat : (2652357681 : ℕ)^2121*100000000000000^1609 ≤ 43355758563119^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652357681 5000000000 43355758563119 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709518873/5000000000 : ℝ)^2121 ≤ (22295824534437/50000000000000 : ℝ)^1609 := by
    have hnat : (2709518873 : ℕ)^2121*50000000000000^1609 ≤ 22295824534437^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709518873 5000000000 22295824534437 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2008646769/10000000000 : ℝ)^2121 ≤ (3013148088819/25000000000000 : ℝ)^1609 := by
    have hnat : (2008646769 : ℕ)^2121*25000000000000^1609 ≤ 3013148088819^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008646769 10000000000 3013148088819 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652357681/5000000000 : ℝ), (2709518873/5000000000 : ℝ), (-2008646769/10000000000 : ℝ)] ![(43355758563119/100000000000000 : ℝ), (22295824534437/50000000000000 : ℝ), (3013148088819/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652357681/5000000000 : ℝ)|^2121 ≤ (43355758563119/100000000000000 : ℝ)^1609
        have hw : |(2652357681/5000000000 : ℝ)|=(2652357681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709518873/5000000000 : ℝ)|^2121 ≤ (22295824534437/50000000000000 : ℝ)^1609
        have hw : |(2709518873/5000000000 : ℝ)|=(2709518873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2008646769/10000000000 : ℝ)|^2121 ≤ (3013148088819/25000000000000 : ℝ)^1609
        have hw : |(-2008646769/10000000000 : ℝ)|=(2008646769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s4_7 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2171155127/5000000000 : ℝ)*x 0 + (2264860349/5000000000 : ℝ)*x 1 + (130075541/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171155127/5000000000 : ℝ)^2121 ≤ (33299673638813/100000000000000 : ℝ)^1609 := by
    have hnat : (2171155127 : ℕ)^2121*100000000000000^1609 ≤ 33299673638813^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171155127 5000000000 33299673638813 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264860349/5000000000 : ℝ)^2121 ≤ (8801767600433/25000000000000 : ℝ)^1609 := by
    have hnat : (2264860349 : ℕ)^2121*25000000000000^1609 ≤ 8801767600433^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264860349 5000000000 8801767600433 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130075541/312500000 : ℝ)^2121 ≤ (15746627970093/50000000000000 : ℝ)^1609 := by
    have hnat : (130075541 : ℕ)^2121*50000000000000^1609 ≤ 15746627970093^1609*312500000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130075541 312500000 15746627970093 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171155127/5000000000 : ℝ), (2264860349/5000000000 : ℝ), (130075541/312500000 : ℝ)] ![(33299673638813/100000000000000 : ℝ), (8801767600433/25000000000000 : ℝ), (15746627970093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171155127/5000000000 : ℝ)|^2121 ≤ (33299673638813/100000000000000 : ℝ)^1609
        have hw : |(2171155127/5000000000 : ℝ)|=(2171155127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2264860349/5000000000 : ℝ)|^2121 ≤ (8801767600433/25000000000000 : ℝ)^1609
        have hw : |(2264860349/5000000000 : ℝ)|=(2264860349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130075541/312500000 : ℝ)|^2121 ≤ (15746627970093/50000000000000 : ℝ)^1609
        have hw : |(130075541/312500000 : ℝ)|=(130075541/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1282_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (377/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10613/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2731/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3687/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (377/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10613/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (377/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10613/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (377/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10613/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (377/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10613/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (377/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10613/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (377/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10613/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10613/100000 : ℝ) ^ (4241/1024 : ℝ) ≤ (1846884831787901/20000000000000000000 : ℝ) := by
    have hpowers : (10613/100000 : ℝ)^4241 ≤ (1846884831787901/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10613 : ℕ)^4241*20000000000000000000^1024 ≤ 1846884831787901^1024*100000^4241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10613 100000 1846884831787901 20000000000000000000 4241 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10613/100000 : ℝ)) (X := (1846884831787901/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (377/2500 : ℝ) ^ (4241/1024 : ℝ) ≤ (39560858937990671/100000000000000000000 : ℝ) := by
    have hpowers : (377/2500 : ℝ)^4241 ≤ (39560858937990671/100000000000000000000 : ℝ)^1024 := by
      have hnat : (377 : ℕ)^4241*100000000000000000000^1024 ≤ 39560858937990671^1024*2500^4241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        377 2500 39560858937990671 100000000000000000000 4241 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (377/2500 : ℝ)) (X := (39560858937990671/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001846884831787901/10000000000000000000 : ℝ) ≤ (10000445903703741/10000000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (10001846884831787901/10000000000000000000 : ℝ)^1024 ≤ (10000445903703741/10000000000000000 : ℝ)^4241 := by
      have hnat : (10001846884831787901 : ℕ)^1024*10000000000000000^4241 ≤ 10000445903703741^4241*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001846884831787901 10000000000000000000 10000445903703741 10000000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000445903703741/10000000000000000 : ℝ)) (X := (10001846884831787901/10000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (781631213149194767/781250000000000000 : ℝ) ≤ (625073622266821/625000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (781631213149194767/781250000000000000 : ℝ)^1024 ≤ (625073622266821/625000000000000 : ℝ)^4241 := by
      have hnat : (781631213149194767 : ℕ)^1024*625000000000000^4241 ≤ 625073622266821^4241*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781631213149194767 781250000000000000 625073622266821 625000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625073622266821/625000000000000 : ℝ)) (X := (781631213149194767/781250000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039560858937990671/50000000000000000000 : ℝ) ≤ (10001910008834531/10000000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (50039560858937990671/50000000000000000000 : ℝ)^1024 ≤ (10001910008834531/10000000000000000 : ℝ)^4241 := by
      have hnat : (50039560858937990671 : ℕ)^1024*10000000000000000^4241 ≤ 10001910008834531^4241*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039560858937990671 50000000000000000000 10001910008834531 10000000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001910008834531/10000000000000000 : ℝ)) (X := (50039560858937990671/50000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1846884831787901/20000000000000000000 : ℝ) ≤ ((44656453304091536777/44670000000000000000 : ℝ)+2*(146410513079/89340000000000 : ℝ)*(10613/100000 : ℝ))^(4241/1024 : ℝ) := by
    rw [show (44656453304091536777/44670000000000000000 : ℝ)+2*(146410513079/89340000000000 : ℝ)*(10613/100000 : ℝ)=(10000445903703741/10000000000000000 : ℝ) by norm_num, show 1+2*(1846884831787901/20000000000000000000 : ℝ)=(10001846884831787901/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39560858937990671/100000000000000000000 : ℝ)+(1846884831787901/20000000000000000000 : ℝ) ≤ ((44656453304091536777/44670000000000000000 : ℝ)+(146410513079/89340000000000 : ℝ)*((377/2500 : ℝ)+(10613/100000 : ℝ)))^(4241/1024 : ℝ) := by
    rw [show (44656453304091536777/44670000000000000000 : ℝ)+(146410513079/89340000000000 : ℝ)*((377/2500 : ℝ)+(10613/100000 : ℝ))=(625073622266821/625000000000000 : ℝ) by norm_num, show 1+(39560858937990671/100000000000000000000 : ℝ)+(1846884831787901/20000000000000000000 : ℝ)=(781631213149194767/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39560858937990671/100000000000000000000 : ℝ) ≤ ((44656453304091536777/44670000000000000000 : ℝ)+2*(146410513079/89340000000000 : ℝ)*(377/2500 : ℝ))^(4241/1024 : ℝ) := by
    rw [show (44656453304091536777/44670000000000000000 : ℝ)+2*(146410513079/89340000000000 : ℝ)*(377/2500 : ℝ)=(10001910008834531/10000000000000000 : ℝ) by norm_num, show 1+2*(39560858937990671/100000000000000000000 : ℝ)=(50039560858937990671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44656453304091536777/44670000000000000000 : ℝ)*(X 1 0+X 2 0)+(146410513079/89340000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (10613/100000 : ℝ)) (hi := (377/2500 : ℝ)) (c := (44656453304091536777/44670000000000000000 : ℝ)) (alpha := (146410513079/89340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44656453304091536777/44670000000000000000 : ℝ)*(X 0 1+X 2 1)+(146410513079/89340000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (10613/100000 : ℝ)) (hi := (377/2500 : ℝ)) (c := (44656453304091536777/44670000000000000000 : ℝ)) (alpha := (146410513079/89340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44656453304091536777/44670000000000000000 : ℝ)*(X 0 2+X 1 2)+(146410513079/89340000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (10613/100000 : ℝ)) (hi := (377/2500 : ℝ)) (c := (44656453304091536777/44670000000000000000 : ℝ)) (alpha := (146410513079/89340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2096496579/10000000000 : ℝ)*X 0 0+(2709856679/5000000000 : ℝ)*X 0 1+(5238964649/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267546653/500000000 : ℝ)*X 1 0+(-547179937/2500000000 : ℝ)*X 1 1+(1309741173/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337733221/2500000000 : ℝ)*X 2 0+(5238964843/10000000000 : ℝ)*X 2 1+(-2188719783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4342280213/10000000000 : ℝ)*X 0 0+(2080517147/5000000000 : ℝ)*X 0 1+(4531096499/10000000000 : ℝ)*X 0 2+(4342280213/10000000000 : ℝ)*X 1 0+(2080517147/5000000000 : ℝ)*X 1 1+(4531096499/10000000000 : ℝ)*X 1 2+(4342280213/10000000000 : ℝ)*X 2 0+(2080517147/5000000000 : ℝ)*X 2 1+(4531096499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2096511317/10000000000 : ℝ)*X 0 0+(5239636547/10000000000 : ℝ)*X 0 1+(5419037751/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304715347/10000000000 : ℝ)*X 1 0+(-2008646643/10000000000 : ℝ)*X 1 1+(5419037853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652357681/5000000000 : ℝ)*X 2 0+(2709518873/5000000000 : ℝ)*X 2 1+(-2008646769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2171155127/5000000000 : ℝ)*X 0 0+(2264860349/5000000000 : ℝ)*X 0 1+(130075541/312500000 : ℝ)*X 0 2+(2171155127/5000000000 : ℝ)*X 1 0+(2264860349/5000000000 : ℝ)*X 1 1+(130075541/312500000 : ℝ)*X 1 2+(2171155127/5000000000 : ℝ)*X 2 0+(2264860349/5000000000 : ℝ)*X 2 1+(130075541/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2950982987524336434899423033/744500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (190336609/100000000000000 : ℝ)*(base19) + (58453309/100000000000000 : ℝ)*(base23) + (7441381/25000000000000 : ℝ)*(lower2) + (35707301/100000000000000 : ℝ)*(upper3) + (56568617/100000000000000 : ℝ)*(lower4) + (4117403448815471/100000000000000 : ℝ)*(major0) + (4117403448815471/100000000000000 : ℝ)*(major1) + (4117403448815471/100000000000000 : ℝ)*(major2) + (5532550435407573/100000000000000 : ℝ)*(sp0) + (5532554615663549/100000000000000 : ℝ)*(sp1) + (5532554747546849/100000000000000 : ℝ)*(sp2) + (1351125170535701/50000000000000 : ℝ)*(sp3) + (874118517/20000000000000 : ℝ)*(sp4) + (1618435669/100000000000000 : ℝ)*(sp7) + (270225195950707/10000000000000 : ℝ)*(f.failure) + (2766277403000079/50000000000000 : ℝ)*(f.sum) + (6763371220571/4467000000000000000000000000 : ℝ)*base66 + (9757600951335141011/1489000000000000000000000000000000 : ℝ)*base68 + (2776078498013858989/1489000000000000000000000000000000 : ℝ)*base69 + (5311753248507858989/1489000000000000000000000000000000 : ℝ)*base71 + (13493041436357/4467000000000000000000000000 : ℝ)*base74 + (5526486789669858989/1489000000000000000000000000000000 : ℝ)*base75 + (1334625437156141011/1489000000000000000000000000000000 : ℝ)*base78 + (1512989103022858989/1489000000000000000000000000000000 : ℝ)*base79 + (2730740961289/1116750000000000000000000000 : ℝ)*base81 + (7827327/1000000000000000000000 : ℝ)*base90 + (7827327/1000000000000000000000 : ℝ)*base92 + (7827327/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1223790391314086399337648209/372250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12316123/4000000000000 : ℝ)*(base19) + (374373931/100000000000000 : ℝ)*(base23) + (16654183/50000000000000 : ℝ)*(upper3) + (45735937/100000000000000 : ℝ)*(lower4) + (99075577/100000000000000 : ℝ)*(upper5) + (2074160894649017/50000000000000 : ℝ)*(major0) + (2074160894649017/50000000000000 : ℝ)*(major1) + (2074160894649017/50000000000000 : ℝ)*(major2) + (4570272601/50000000000000 : ℝ)*(sp1) + (2532515543/50000000000000 : ℝ)*(sp2) + (5574099802074223/100000000000000 : ℝ)*(sp4) + (1114818070725189/20000000000000 : ℝ)*(sp5) + (5574094362669207/100000000000000 : ℝ)*(sp6) + (1361271833468423/50000000000000 : ℝ)*(sp7) + (1361271833468423/50000000000000 : ℝ)*(f.failure) + (5574099802074223/100000000000000 : ℝ)*(f.sum) + (1835887789111/893400000000000000000000000 : ℝ)*base65 + (923405543649200597/744500000000000000000000000000000 : ℝ)*base68 + (3357700124001200597/744500000000000000000000000000000 : ℝ)*base70 + (3608674419784200597/744500000000000000000000000000000 : ℝ)*base72 + (2507571296173/4467000000000000000000000000 : ℝ)*base74 + (12928303341676799403/744500000000000000000000000000000 : ℝ)*base75 + (1668465224542299403/744500000000000000000000000000000 : ℝ)*base77 + (7671232618734700597/744500000000000000000000000000000 : ℝ)*base80 + (12904623925591/4467000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (10117603/5000000000000000000000 : ℝ)*base90 + (10117603/5000000000000000000000 : ℝ)*base92 + (10117603/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1282_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (377/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10613/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2731/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1282_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1282_s5_0 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1048441683/5000000000 : ℝ)*x 0 + (5416457427/10000000000 : ℝ)*x 1 + (655245789/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048441683/5000000000 : ℝ)^2121 ≤ (6377674973311/50000000000000 : ℝ)^1609 := by
    have hnat : (1048441683 : ℕ)^2121*50000000000000^1609 ≤ 6377674973311^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048441683 5000000000 6377674973311 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416457427/10000000000 : ℝ)^2121 ≤ (44563662060639/100000000000000 : ℝ)^1609 := by
    have hnat : (5416457427 : ℕ)^2121*100000000000000^1609 ≤ 44563662060639^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416457427 10000000000 44563662060639 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655245789/1250000000 : ℝ)^2121 ≤ (21340493990403/50000000000000 : ℝ)^1609 := by
    have hnat : (655245789 : ℕ)^2121*50000000000000^1609 ≤ 21340493990403^1609*1250000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655245789 1250000000 21340493990403 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1048441683/5000000000 : ℝ), (5416457427/10000000000 : ℝ), (655245789/1250000000 : ℝ)] ![(6377674973311/50000000000000 : ℝ), (44563662060639/100000000000000 : ℝ), (21340493990403/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1048441683/5000000000 : ℝ)|^2121 ≤ (6377674973311/50000000000000 : ℝ)^1609
        have hw : |(-1048441683/5000000000 : ℝ)|=(1048441683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416457427/10000000000 : ℝ)|^2121 ≤ (44563662060639/100000000000000 : ℝ)^1609
        have hw : |(5416457427/10000000000 : ℝ)|=(5416457427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655245789/1250000000 : ℝ)|^2121 ≤ (21340493990403/50000000000000 : ℝ)^1609
        have hw : |(655245789/1250000000 : ℝ)|=(655245789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s5_1 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5350108557/10000000000 : ℝ)*x 0 + (-1092925991/5000000000 : ℝ)*x 1 + (5241966339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350108557/10000000000 : ℝ)^2121 ≤ (10961370198217/25000000000000 : ℝ)^1609 := by
    have hnat : (5350108557 : ℕ)^2121*25000000000000^1609 ≤ 10961370198217^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350108557 10000000000 10961370198217 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092925991/5000000000 : ℝ)^2121 ≤ (13473530921229/100000000000000 : ℝ)^1609 := by
    have hnat : (1092925991 : ℕ)^2121*100000000000000^1609 ≤ 13473530921229^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092925991 5000000000 13473530921229 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241966339/10000000000 : ℝ)^2121 ≤ (213404941353/500000000000 : ℝ)^1609 := by
    have hnat : (5241966339 : ℕ)^2121*500000000000^1609 ≤ 213404941353^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241966339 10000000000 213404941353 500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350108557/10000000000 : ℝ), (-1092925991/5000000000 : ℝ), (5241966339/10000000000 : ℝ)] ![(10961370198217/25000000000000 : ℝ), (13473530921229/100000000000000 : ℝ), (213404941353/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350108557/10000000000 : ℝ)|^2121 ≤ (10961370198217/25000000000000 : ℝ)^1609
        have hw : |(5350108557/10000000000 : ℝ)|=(5350108557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1092925991/5000000000 : ℝ)|^2121 ≤ (13473530921229/100000000000000 : ℝ)^1609
        have hw : |(-1092925991/5000000000 : ℝ)|=(1092925991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241966339/10000000000 : ℝ)|^2121 ≤ (213404941353/500000000000 : ℝ)^1609
        have hw : |(5241966339/10000000000 : ℝ)|=(5241966339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s5_2 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2675054309/5000000000 : ℝ)*x 0 + (1048393273/2000000000 : ℝ)*x 1 + (-2185851867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675054309/5000000000 : ℝ)^2121 ≤ (21922740725927/50000000000000 : ℝ)^1609 := by
    have hnat : (2675054309 : ℕ)^2121*50000000000000^1609 ≤ 21922740725927^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675054309 5000000000 21922740725927 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048393273/2000000000 : ℝ)^2121 ≤ (2134049427483/5000000000000 : ℝ)^1609 := by
    have hnat : (1048393273 : ℕ)^2121*5000000000000^1609 ≤ 2134049427483^1609*2000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048393273 2000000000 2134049427483 5000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2185851867/10000000000 : ℝ)^2121 ≤ (13473529986807/100000000000000 : ℝ)^1609 := by
    have hnat : (2185851867 : ℕ)^2121*100000000000000^1609 ≤ 13473529986807^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185851867 10000000000 13473529986807 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675054309/5000000000 : ℝ), (1048393273/2000000000 : ℝ), (-2185851867/10000000000 : ℝ)] ![(21922740725927/50000000000000 : ℝ), (2134049427483/5000000000000 : ℝ), (13473529986807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675054309/5000000000 : ℝ)|^2121 ≤ (21922740725927/50000000000000 : ℝ)^1609
        have hw : |(2675054309/5000000000 : ℝ)|=(2675054309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048393273/2000000000 : ℝ)|^2121 ≤ (2134049427483/5000000000000 : ℝ)^1609
        have hw : |(1048393273/2000000000 : ℝ)|=(1048393273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2185851867/10000000000 : ℝ)|^2121 ≤ (13473529986807/100000000000000 : ℝ)^1609
        have hw : |(-2185851867/10000000000 : ℝ)|=(2185851867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s5_3 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2171254629/5000000000 : ℝ)*x 0 + (4167410469/10000000000 : ℝ)*x 1 + (4524661937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171254629/5000000000 : ℝ)^2121 ≤ (33301685364327/100000000000000 : ℝ)^1609 := by
    have hnat : (2171254629 : ℕ)^2121*100000000000000^1609 ≤ 33301685364327^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171254629 5000000000 33301685364327 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4167410469/10000000000 : ℝ)^2121 ≤ (31543065723033/100000000000000 : ℝ)^1609 := by
    have hnat : (4167410469 : ℕ)^2121*100000000000000^1609 ≤ 31543065723033^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4167410469 10000000000 31543065723033 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4524661937/10000000000 : ℝ)^2121 ≤ (35155248892693/100000000000000 : ℝ)^1609 := by
    have hnat : (4524661937 : ℕ)^2121*100000000000000^1609 ≤ 35155248892693^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524661937 10000000000 35155248892693 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171254629/5000000000 : ℝ), (4167410469/10000000000 : ℝ), (4524661937/10000000000 : ℝ)] ![(33301685364327/100000000000000 : ℝ), (31543065723033/100000000000000 : ℝ), (35155248892693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171254629/5000000000 : ℝ)|^2121 ≤ (33301685364327/100000000000000 : ℝ)^1609
        have hw : |(2171254629/5000000000 : ℝ)|=(2171254629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4167410469/10000000000 : ℝ)|^2121 ≤ (31543065723033/100000000000000 : ℝ)^1609
        have hw : |(4167410469/10000000000 : ℝ)|=(4167410469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4524661937/10000000000 : ℝ)|^2121 ≤ (35155248892693/100000000000000 : ℝ)^1609
        have hw : |(4524661937/10000000000 : ℝ)|=(4524661937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s5_4 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1048448127/5000000000 : ℝ)*x 0 + (5242592611/10000000000 : ℝ)*x 1 + (5415828067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048448127/5000000000 : ℝ)^2121 ≤ (2551090658287/20000000000000 : ℝ)^1609 := by
    have hnat : (1048448127 : ℕ)^2121*20000000000000^1609 ≤ 2551090658287^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048448127 5000000000 2551090658287 20000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242592611/10000000000 : ℝ)^2121 ≤ (2134385511677/5000000000000 : ℝ)^1609 := by
    have hnat : (5242592611 : ℕ)^2121*5000000000000^1609 ≤ 2134385511677^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242592611 10000000000 2134385511677 5000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415828067/10000000000 : ℝ)^2121 ≤ (11139209113443/25000000000000 : ℝ)^1609 := by
    have hnat : (5415828067 : ℕ)^2121*25000000000000^1609 ≤ 11139209113443^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415828067 10000000000 11139209113443 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1048448127/5000000000 : ℝ), (5242592611/10000000000 : ℝ), (5415828067/10000000000 : ℝ)] ![(2551090658287/20000000000000 : ℝ), (2134385511677/5000000000000 : ℝ), (11139209113443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1048448127/5000000000 : ℝ)|^2121 ≤ (2551090658287/20000000000000 : ℝ)^1609
        have hw : |(-1048448127/5000000000 : ℝ)|=(1048448127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242592611/10000000000 : ℝ)|^2121 ≤ (2134385511677/5000000000000 : ℝ)^1609
        have hw : |(5242592611/10000000000 : ℝ)|=(5242592611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415828067/10000000000 : ℝ)|^2121 ≤ (11139209113443/25000000000000 : ℝ)^1609
        have hw : |(5415828067/10000000000 : ℝ)|=(5415828067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s5_5 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305491409/10000000000 : ℝ)*x 0 + (-40239801/200000000 : ℝ)*x 1 + (2707914033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305491409/10000000000 : ℝ)^2121 ≤ (5420514967619/12500000000000 : ℝ)^1609 := by
    have hnat : (5305491409 : ℕ)^2121*12500000000000^1609 ≤ 5420514967619^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305491409 10000000000 5420514967619 12500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40239801/200000000 : ℝ)^2121 ≤ (6039521898681/50000000000000 : ℝ)^1609 := by
    have hnat : (40239801 : ℕ)^2121*50000000000000^1609 ≤ 6039521898681^1609*200000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40239801 200000000 6039521898681 50000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707914033/5000000000 : ℝ)^2121 ≤ (44556836442927/100000000000000 : ℝ)^1609 := by
    have hnat : (2707914033 : ℕ)^2121*100000000000000^1609 ≤ 44556836442927^1609*5000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707914033 5000000000 44556836442927 100000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305491409/10000000000 : ℝ), (-40239801/200000000 : ℝ), (2707914033/5000000000 : ℝ)] ![(5420514967619/12500000000000 : ℝ), (6039521898681/50000000000000 : ℝ), (44556836442927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305491409/10000000000 : ℝ)|^2121 ≤ (5420514967619/12500000000000 : ℝ)^1609
        have hw : |(5305491409/10000000000 : ℝ)|=(5305491409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40239801/200000000 : ℝ)|^2121 ≤ (6039521898681/50000000000000 : ℝ)^1609
        have hw : |(-40239801/200000000 : ℝ)|=(40239801/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707914033/5000000000 : ℝ)|^2121 ≤ (44556836442927/100000000000000 : ℝ)^1609
        have hw : |(2707914033/5000000000 : ℝ)|=(2707914033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s5_6 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305491409/10000000000 : ℝ)*x 0 + (5415828067/10000000000 : ℝ)*x 1 + (-2011990049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305491409/10000000000 : ℝ)^2121 ≤ (5420514967619/12500000000000 : ℝ)^1609 := by
    have hnat : (5305491409 : ℕ)^2121*12500000000000^1609 ≤ 5420514967619^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305491409 10000000000 5420514967619 12500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415828067/10000000000 : ℝ)^2121 ≤ (11139209113443/25000000000000 : ℝ)^1609 := by
    have hnat : (5415828067 : ℕ)^2121*25000000000000^1609 ≤ 11139209113443^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415828067 10000000000 11139209113443 25000000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011990049/10000000000 : ℝ)^2121 ≤ (1509880473681/12500000000000 : ℝ)^1609 := by
    have hnat : (2011990049 : ℕ)^2121*12500000000000^1609 ≤ 1509880473681^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011990049 10000000000 1509880473681 12500000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305491409/10000000000 : ℝ), (5415828067/10000000000 : ℝ), (-2011990049/10000000000 : ℝ)] ![(5420514967619/12500000000000 : ℝ), (11139209113443/25000000000000 : ℝ), (1509880473681/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305491409/10000000000 : ℝ)|^2121 ≤ (5420514967619/12500000000000 : ℝ)^1609
        have hw : |(5305491409/10000000000 : ℝ)|=(5305491409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415828067/10000000000 : ℝ)|^2121 ≤ (11139209113443/25000000000000 : ℝ)^1609
        have hw : |(5415828067/10000000000 : ℝ)|=(5415828067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2011990049/10000000000 : ℝ)|^2121 ≤ (1509880473681/12500000000000 : ℝ)^1609
        have hw : |(-2011990049/10000000000 : ℝ)|=(2011990049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1282_s5_7 (p : ℝ) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4342535631/10000000000 : ℝ)*x 0 + (4523379773/10000000000 : ℝ)*x 1 + (416869979/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342535631/10000000000 : ℝ)^2121 ≤ (41627439963/125000000000 : ℝ)^1609 := by
    have hnat : (4342535631 : ℕ)^2121*125000000000^1609 ≤ 41627439963^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342535631 10000000000 41627439963 125000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4523379773/10000000000 : ℝ)^2121 ≤ (2196382340211/6250000000000 : ℝ)^1609 := by
    have hnat : (4523379773 : ℕ)^2121*6250000000000^1609 ≤ 2196382340211^1609*10000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523379773 10000000000 2196382340211 6250000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416869979/1000000000 : ℝ)^2121 ≤ (986122830363/3125000000000 : ℝ)^1609 := by
    have hnat : (416869979 : ℕ)^2121*3125000000000^1609 ≤ 986122830363^1609*1000000000^2121 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416869979 1000000000 986122830363 3125000000000 2121 1609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2121/512 : ℝ)) 2121 1609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342535631/10000000000 : ℝ), (4523379773/10000000000 : ℝ), (416869979/1000000000 : ℝ)] ![(41627439963/125000000000 : ℝ), (2196382340211/6250000000000 : ℝ), (986122830363/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342535631/10000000000 : ℝ)|^2121 ≤ (41627439963/125000000000 : ℝ)^1609
        have hw : |(4342535631/10000000000 : ℝ)|=(4342535631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4523379773/10000000000 : ℝ)|^2121 ≤ (2196382340211/6250000000000 : ℝ)^1609
        have hw : |(4523379773/10000000000 : ℝ)|=(4523379773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(416869979/1000000000 : ℝ)|^2121 ≤ (986122830363/3125000000000 : ℝ)^1609
        have hw : |(416869979/1000000000 : ℝ)|=(416869979/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1282_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2731/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2747/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (367/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2731/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2731/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2731/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2731/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2731/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2731/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2731/25000 : ℝ) ^ (4241/1024 : ℝ) ≤ (1040782810548297/10000000000000000000 : ℝ) := by
    have hpowers : (2731/25000 : ℝ)^4241 ≤ (1040782810548297/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2731 : ℕ)^4241*10000000000000000000^1024 ≤ 1040782810548297^1024*25000^4241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2731 25000 1040782810548297 10000000000000000000 4241 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2731/25000 : ℝ)) (X := (1040782810548297/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3687/25000 : ℝ) ^ (4241/1024 : ℝ) ≤ (36076452697611417/100000000000000000000 : ℝ) := by
    have hpowers : (3687/25000 : ℝ)^4241 ≤ (36076452697611417/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3687 : ℕ)^4241*100000000000000000000^1024 ≤ 36076452697611417^1024*25000^4241 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3687 25000 36076452697611417 100000000000000000000 4241 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3687/25000 : ℝ)) (X := (36076452697611417/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001040782810548297/5000000000000000000 : ℝ) ≤ (5000251279761419/5000000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (5001040782810548297/5000000000000000000 : ℝ)^1024 ≤ (5000251279761419/5000000000000000 : ℝ)^4241 := by
      have hnat : (5001040782810548297 : ℕ)^1024*5000000000000000^4241 ≤ 5000251279761419^4241*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001040782810548297 5000000000000000000 5000251279761419 5000000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000251279761419/5000000000000000 : ℝ)) (X := (5001040782810548297/5000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046484280803094387/100000000000000000000 : ℝ) ≤ (2000224435339957/2000000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (100046484280803094387/100000000000000000000 : ℝ)^1024 ≤ (2000224435339957/2000000000000000 : ℝ)^4241 := by
      have hnat : (100046484280803094387 : ℕ)^1024*2000000000000000^4241 ≤ 2000224435339957^4241*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046484280803094387 100000000000000000000 2000224435339957 2000000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000224435339957/2000000000000000 : ℝ)) (X := (100046484280803094387/100000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036076452697611417/50000000000000000000 : ℝ) ≤ (2500435448469183/2500000000000000 : ℝ) ^ (4241/1024 : ℝ) := by
    have hpowers : (50036076452697611417/50000000000000000000 : ℝ)^1024 ≤ (2500435448469183/2500000000000000 : ℝ)^4241 := by
      have hnat : (50036076452697611417 : ℕ)^1024*2500000000000000^4241 ≤ 2500435448469183^4241*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036076452697611417 50000000000000000000 2500435448469183 2500000000000000 1024 4241 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500435448469183/2500000000000000 : ℝ)) (X := (50036076452697611417/50000000000000000000 : ℝ)) (by norm_num) 4241 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1040782810548297/10000000000000000000 : ℝ) ≤ ((4778548048941674307/4780000000000000000 : ℝ)+2*(619617176947/382400000000000 : ℝ)*(2731/25000 : ℝ))^(4241/1024 : ℝ) := by
    rw [show (4778548048941674307/4780000000000000000 : ℝ)+2*(619617176947/382400000000000 : ℝ)*(2731/25000 : ℝ)=(5000251279761419/5000000000000000 : ℝ) by norm_num, show 1+2*(1040782810548297/10000000000000000000 : ℝ)=(5001040782810548297/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36076452697611417/100000000000000000000 : ℝ)+(1040782810548297/10000000000000000000 : ℝ) ≤ ((4778548048941674307/4780000000000000000 : ℝ)+(619617176947/382400000000000 : ℝ)*((3687/25000 : ℝ)+(2731/25000 : ℝ)))^(4241/1024 : ℝ) := by
    rw [show (4778548048941674307/4780000000000000000 : ℝ)+(619617176947/382400000000000 : ℝ)*((3687/25000 : ℝ)+(2731/25000 : ℝ))=(2000224435339957/2000000000000000 : ℝ) by norm_num, show 1+(36076452697611417/100000000000000000000 : ℝ)+(1040782810548297/10000000000000000000 : ℝ)=(100046484280803094387/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36076452697611417/100000000000000000000 : ℝ) ≤ ((4778548048941674307/4780000000000000000 : ℝ)+2*(619617176947/382400000000000 : ℝ)*(3687/25000 : ℝ))^(4241/1024 : ℝ) := by
    rw [show (4778548048941674307/4780000000000000000 : ℝ)+2*(619617176947/382400000000000 : ℝ)*(3687/25000 : ℝ)=(2500435448469183/2500000000000000 : ℝ) by norm_num, show 1+2*(36076452697611417/100000000000000000000 : ℝ)=(50036076452697611417/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4778548048941674307/4780000000000000000 : ℝ)*(X 1 0+X 2 0)+(619617176947/382400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (2731/25000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (4778548048941674307/4780000000000000000 : ℝ)) (alpha := (619617176947/382400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4778548048941674307/4780000000000000000 : ℝ)*(X 0 1+X 2 1)+(619617176947/382400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (2731/25000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (4778548048941674307/4780000000000000000 : ℝ)) (alpha := (619617176947/382400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4778548048941674307/4780000000000000000 : ℝ)*(X 0 2+X 1 2)+(619617176947/382400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4241/1024 : ℝ)) (lo := (2731/25000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (4778548048941674307/4780000000000000000 : ℝ)) (alpha := (619617176947/382400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1048441683/5000000000 : ℝ)*X 0 0+(5416457427/10000000000 : ℝ)*X 0 1+(655245789/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350108557/10000000000 : ℝ)*X 1 0+(-1092925991/5000000000 : ℝ)*X 1 1+(5241966339/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675054309/5000000000 : ℝ)*X 2 0+(1048393273/2000000000 : ℝ)*X 2 1+(-2185851867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2171254629/5000000000 : ℝ)*X 0 0+(4167410469/10000000000 : ℝ)*X 0 1+(4524661937/10000000000 : ℝ)*X 0 2+(2171254629/5000000000 : ℝ)*X 1 0+(4167410469/10000000000 : ℝ)*X 1 1+(4524661937/10000000000 : ℝ)*X 1 2+(2171254629/5000000000 : ℝ)*X 2 0+(4167410469/10000000000 : ℝ)*X 2 1+(4524661937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1048448127/5000000000 : ℝ)*X 0 0+(5242592611/10000000000 : ℝ)*X 0 1+(5415828067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305491409/10000000000 : ℝ)*X 1 0+(-40239801/200000000 : ℝ)*X 1 1+(2707914033/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305491409/10000000000 : ℝ)*X 2 0+(5415828067/10000000000 : ℝ)*X 2 1+(-2011990049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4342535631/10000000000 : ℝ)*X 0 0+(4523379773/10000000000 : ℝ)*X 0 1+(416869979/1000000000 : ℝ)*X 0 2+(4342535631/10000000000 : ℝ)*X 1 0+(4523379773/10000000000 : ℝ)*X 1 1+(416869979/1000000000 : ℝ)*X 1 2+(4342535631/10000000000 : ℝ)*X 2 0+(4523379773/10000000000 : ℝ)*X 2 1+(416869979/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1282_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78669572412387300820876749/29875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (774530471/100000000000000 : ℝ)*(base19) + (199383329/25000000000000 : ℝ)*(base23) + (17697/78125000000 : ℝ)*(lower2) + (141603907/100000000000000 : ℝ)*(upper3) + (25802833/10000000000000 : ℝ)*(upper5) + (1066267319114981/25000000000000 : ℝ)*(major0) + (1066267319114981/25000000000000 : ℝ)*(major1) + (1066267319114981/25000000000000 : ℝ)*(major2) + (573095947846363/10000000000000 : ℝ)*(sp0) + (5730972645695449/100000000000000 : ℝ)*(sp1) + (5730972622692603/100000000000000 : ℝ)*(sp2) + (699789376718767/25000000000000 : ℝ)*(sp3) + (1394176229/10000000000000 : ℝ)*(sp4) + (3769021241/50000000000000 : ℝ)*(sp7) + (55983300898351/2000000000000 : ℝ)*(f.failure) + (5730973420225919/100000000000000 : ℝ)*(f.sum) + (1553833711127/4780000000000000000000000000 : ℝ)*base65 + (246356080146919333/119500000000000000000000000000000 : ℝ)*base68 + (2070955797297080667/119500000000000000000000000000000 : ℝ)*base69 + (853116802783580667/119500000000000000000000000000000 : ℝ)*base71 + (5679062073793/4780000000000000000000000000 : ℝ)*base74 + (1437359003387580667/119500000000000000000000000000000 : ℝ)*base75 + (44783483244080667/119500000000000000000000000000000 : ℝ)*base77 + (2200408941900580667/119500000000000000000000000000000 : ℝ)*base79 + (9153506720907/4780000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (59989/200000000000000000000 : ℝ)*base89 + (59989/200000000000000000000 : ℝ)*base91 + (59989/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (339122068518869680680081147/119500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (254646931/50000000000000 : ℝ)*(base19) + (554296543/100000000000000 : ℝ)*(base23) + (57951657/100000000000000 : ℝ)*(upper3) + (1012117/5000000000000 : ℝ)*(lower4) + (364459/625000000000 : ℝ)*(upper5) + (4295966472674543/100000000000000 : ℝ)*(major0) + (4295966472674543/100000000000000 : ℝ)*(major1) + (4295966472674543/100000000000000 : ℝ)*(major2) + (1006202807/10000000000000 : ℝ)*(sp1) + (2719112989/25000000000000 : ℝ)*(sp2) + (230899599015619/4000000000000 : ℝ)*(sp4) + (2886239702034271/50000000000000 : ℝ)*(sp5) + (721559818080247/12500000000000 : ℝ)*(sp6) + (2819442875363883/100000000000000 : ℝ)*(sp7) + (2819442875363883/100000000000000 : ℝ)*(f.failure) + (230899599015619/4000000000000 : ℝ)*(f.sum) + (38712529280461/19120000000000000000000000000 : ℝ)*base65 + (3466391986966829201/478000000000000000000000000000000 : ℝ)*base67 + (941259211091170799/478000000000000000000000000000000 : ℝ)*base70 + (3170391893720829201/478000000000000000000000000000000 : ℝ)*base71 + (80727540092941/19120000000000000000000000000 : ℝ)*base73 + (5953903371302829201/478000000000000000000000000000000 : ℝ)*base75 + (2024152518848829201/478000000000000000000000000000000 : ℝ)*base77 + (1600843975820829201/478000000000000000000000000000000 : ℝ)*base79 + (75148531066941/19120000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (62816663/10000000000000000000000 : ℝ)*base90 + (62816663/10000000000000000000000 : ℝ)*base92 + (62816663/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1282_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2731/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2747/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (367/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1282_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1282_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (943/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2747/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (367/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1282_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1282_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1282_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4241/1024 : ℝ) ≤ p) (hpb : p ≤ (2121/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152369339/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4091/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (943/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2747/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (367/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1282_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

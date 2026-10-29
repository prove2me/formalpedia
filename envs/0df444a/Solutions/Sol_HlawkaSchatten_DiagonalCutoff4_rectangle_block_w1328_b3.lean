-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1328_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:55:36.85799+00:00
-- url     : https://prove2.me/submissions/a7c97a0c-091e-443c-8628-0ef7fdeee62c

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
theorem support_rectangle_w1328_box_0 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-943877843/5000000000 : ℝ)*x 0 + (2695261843/5000000000 : ℝ)*x 1 + (539052337/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (943877843/5000000000 : ℝ)^67 ≤ (2237801289843/20000000000000 : ℝ)^51 := by
    have hnat : (943877843 : ℕ)^67*20000000000000^51 ≤ 2237801289843^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943877843 5000000000 2237801289843 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695261843/5000000000 : ℝ)^67 ≤ (11101374619303/25000000000000 : ℝ)^51 := by
    have hnat : (2695261843 : ℕ)^67*25000000000000^51 ≤ 11101374619303^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695261843 5000000000 11101374619303 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539052337/1000000000 : ℝ)^67 ≤ (44405495057437/100000000000000 : ℝ)^51 := by
    have hnat : (539052337 : ℕ)^67*100000000000000^51 ≤ 44405495057437^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539052337 1000000000 44405495057437 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-943877843/5000000000 : ℝ), (2695261843/5000000000 : ℝ), (539052337/1000000000 : ℝ)] ![(2237801289843/20000000000000 : ℝ), (11101374619303/25000000000000 : ℝ), (44405495057437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-943877843/5000000000 : ℝ)|^67 ≤ (2237801289843/20000000000000 : ℝ)^51
        have hw : |(-943877843/5000000000 : ℝ)|=(943877843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695261843/5000000000 : ℝ)|^67 ≤ (11101374619303/25000000000000 : ℝ)^51
        have hw : |(2695261843/5000000000 : ℝ)|=(2695261843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539052337/1000000000 : ℝ)|^67 ≤ (44405495057437/100000000000000 : ℝ)^51
        have hw : |(539052337/1000000000 : ℝ)|=(539052337/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_box_1 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2642482337/5000000000 : ℝ)*x 0 + (-2032304499/10000000000 : ℝ)*x 1 + (2695261789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642482337/5000000000 : ℝ)^67 ≤ (2704166009753/6250000000000 : ℝ)^51 := by
    have hnat : (2642482337 : ℕ)^67*6250000000000^51 ≤ 2704166009753^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642482337 5000000000 2704166009753 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2032304499/10000000000 : ℝ)^67 ≤ (2465569304437/20000000000000 : ℝ)^51 := by
    have hnat : (2032304499 : ℕ)^67*20000000000000^51 ≤ 2465569304437^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032304499 10000000000 2465569304437 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695261789/5000000000 : ℝ)^67 ≤ (11101374327107/25000000000000 : ℝ)^51 := by
    have hnat : (2695261789 : ℕ)^67*25000000000000^51 ≤ 11101374327107^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695261789 5000000000 11101374327107 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642482337/5000000000 : ℝ), (-2032304499/10000000000 : ℝ), (2695261789/5000000000 : ℝ)] ![(2704166009753/6250000000000 : ℝ), (2465569304437/20000000000000 : ℝ), (11101374327107/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642482337/5000000000 : ℝ)|^67 ≤ (2704166009753/6250000000000 : ℝ)^51
        have hw : |(2642482337/5000000000 : ℝ)|=(2642482337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2032304499/10000000000 : ℝ)|^67 ≤ (2465569304437/20000000000000 : ℝ)^51
        have hw : |(-2032304499/10000000000 : ℝ)|=(2032304499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695261789/5000000000 : ℝ)|^67 ≤ (11101374327107/25000000000000 : ℝ)^51
        have hw : |(2695261789/5000000000 : ℝ)|=(2695261789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_box_2 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (211398571/400000000 : ℝ)*x 0 + (5390524007/10000000000 : ℝ)*x 1 + (-406460891/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211398571/400000000 : ℝ)^67 ≤ (173066607459/400000000000 : ℝ)^51 := by
    have hnat : (211398571 : ℕ)^67*400000000000^51 ≤ 173066607459^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211398571 400000000 173066607459 400000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390524007/10000000000 : ℝ)^67 ≤ (44405501951097/100000000000000 : ℝ)^51 := by
    have hnat : (5390524007 : ℕ)^67*100000000000000^51 ≤ 44405501951097^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390524007 10000000000 44405501951097 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (406460891/2000000000 : ℝ)^67 ≤ (246556923431/2000000000000 : ℝ)^51 := by
    have hnat : (406460891 : ℕ)^67*2000000000000^51 ≤ 246556923431^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406460891 2000000000 246556923431 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211398571/400000000 : ℝ), (5390524007/10000000000 : ℝ), (-406460891/2000000000 : ℝ)] ![(173066607459/400000000000 : ℝ), (44405501951097/100000000000000 : ℝ), (246556923431/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211398571/400000000 : ℝ)|^67 ≤ (173066607459/400000000000 : ℝ)^51
        have hw : |(211398571/400000000 : ℝ)|=(211398571/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390524007/10000000000 : ℝ)|^67 ≤ (44405501951097/100000000000000 : ℝ)^51
        have hw : |(5390524007/10000000000 : ℝ)|=(5390524007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-406460891/2000000000 : ℝ)|^67 ≤ (246556923431/2000000000000 : ℝ)^51
        have hw : |(-406460891/2000000000 : ℝ)|=(406460891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_box_3 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4478817527/10000000000 : ℝ)*x 0 + (212997807/500000000 : ℝ)*x 1 + (4259956447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4478817527/10000000000 : ℝ)^67 ≤ (34811635379537/100000000000000 : ℝ)^51 := by
    have hnat : (4478817527 : ℕ)^67*100000000000000^51 ≤ 34811635379537^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478817527 10000000000 34811635379537 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212997807/500000000 : ℝ)^67 ≤ (2037136297413/6250000000000 : ℝ)^51 := by
    have hnat : (212997807 : ℕ)^67*6250000000000^51 ≤ 2037136297413^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212997807 500000000 2037136297413 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4259956447/10000000000 : ℝ)^67 ≤ (50928412257/156250000000 : ℝ)^51 := by
    have hnat : (4259956447 : ℕ)^67*156250000000^51 ≤ 50928412257^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4259956447 10000000000 50928412257 156250000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4478817527/10000000000 : ℝ), (212997807/500000000 : ℝ), (4259956447/10000000000 : ℝ)] ![(34811635379537/100000000000000 : ℝ), (2037136297413/6250000000000 : ℝ), (50928412257/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4478817527/10000000000 : ℝ)|^67 ≤ (34811635379537/100000000000000 : ℝ)^51
        have hw : |(4478817527/10000000000 : ℝ)|=(4478817527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(212997807/500000000 : ℝ)|^67 ≤ (2037136297413/6250000000000 : ℝ)^51
        have hw : |(212997807/500000000 : ℝ)|=(212997807/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4259956447/10000000000 : ℝ)|^67 ≤ (50928412257/156250000000 : ℝ)^51
        have hw : |(4259956447/10000000000 : ℝ)|=(4259956447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_box_4 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-278407323/1250000000 : ℝ)*x 0 + (2632303467/5000000000 : ℝ)*x 1 + (5264607507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (278407323/1250000000 : ℝ)^67 ≤ (3476079294901/25000000000000 : ℝ)^51 := by
    have hnat : (278407323 : ℕ)^67*25000000000000^51 ≤ 3476079294901^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278407323 1250000000 3476079294901 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632303467/5000000000 : ℝ)^67 ≤ (21523919163307/50000000000000 : ℝ)^51 := by
    have hnat : (2632303467 : ℕ)^67*50000000000000^51 ≤ 21523919163307^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632303467 5000000000 21523919163307 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264607507/10000000000 : ℝ)^67 ≤ (860956889637/2000000000000 : ℝ)^51 := by
    have hnat : (5264607507 : ℕ)^67*2000000000000^51 ≤ 860956889637^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264607507 10000000000 860956889637 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-278407323/1250000000 : ℝ), (2632303467/5000000000 : ℝ), (5264607507/10000000000 : ℝ)] ![(3476079294901/25000000000000 : ℝ), (21523919163307/50000000000000 : ℝ), (860956889637/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-278407323/1250000000 : ℝ)|^67 ≤ (3476079294901/25000000000000 : ℝ)^51
        have hw : |(-278407323/1250000000 : ℝ)|=(278407323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632303467/5000000000 : ℝ)|^67 ≤ (21523919163307/50000000000000 : ℝ)^51
        have hw : |(2632303467/5000000000 : ℝ)|=(2632303467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264607507/10000000000 : ℝ)|^67 ≤ (860956889637/2000000000000 : ℝ)^51
        have hw : |(5264607507/10000000000 : ℝ)|=(5264607507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_box_5 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5373458121/10000000000 : ℝ)*x 0 + (-1041365543/5000000000 : ℝ)*x 1 + (164518983/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373458121/10000000000 : ℝ)^67 ≤ (22110452743117/50000000000000 : ℝ)^51 := by
    have hnat : (5373458121 : ℕ)^67*50000000000000^51 ≤ 22110452743117^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373458121 10000000000 22110452743117 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041365543/5000000000 : ℝ)^67 ≤ (3182812641059/25000000000000 : ℝ)^51 := by
    have hnat : (1041365543 : ℕ)^67*25000000000000^51 ≤ 3182812641059^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041365543 5000000000 3182812641059 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164518983/312500000 : ℝ)^67 ≤ (21523921967001/50000000000000 : ℝ)^51 := by
    have hnat : (164518983 : ℕ)^67*50000000000000^51 ≤ 21523921967001^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164518983 312500000 21523921967001 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373458121/10000000000 : ℝ), (-1041365543/5000000000 : ℝ), (164518983/312500000 : ℝ)] ![(22110452743117/50000000000000 : ℝ), (3182812641059/25000000000000 : ℝ), (21523921967001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373458121/10000000000 : ℝ)|^67 ≤ (22110452743117/50000000000000 : ℝ)^51
        have hw : |(5373458121/10000000000 : ℝ)|=(5373458121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1041365543/5000000000 : ℝ)|^67 ≤ (3182812641059/25000000000000 : ℝ)^51
        have hw : |(-1041365543/5000000000 : ℝ)|=(1041365543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164518983/312500000 : ℝ)|^67 ≤ (21523921967001/50000000000000 : ℝ)^51
        have hw : |(164518983/312500000 : ℝ)|=(164518983/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_box_6 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2686729199/5000000000 : ℝ)*x 0 + (105292147/200000000 : ℝ)*x 1 + (-416546171/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686729199/5000000000 : ℝ)^67 ≤ (44220908480967/100000000000000 : ℝ)^51 := by
    have hnat : (2686729199 : ℕ)^67*100000000000000^51 ≤ 44220908480967^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686729199 5000000000 44220908480967 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105292147/200000000 : ℝ)^67 ≤ (43047842795337/100000000000000 : ℝ)^51 := by
    have hnat : (105292147 : ℕ)^67*100000000000000^51 ≤ 43047842795337^51*200000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105292147 200000000 43047842795337 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416546171/2000000000 : ℝ)^67 ≤ (12731248709191/100000000000000 : ℝ)^51 := by
    have hnat : (416546171 : ℕ)^67*100000000000000^51 ≤ 12731248709191^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416546171 2000000000 12731248709191 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686729199/5000000000 : ℝ), (105292147/200000000 : ℝ), (-416546171/2000000000 : ℝ)] ![(44220908480967/100000000000000 : ℝ), (43047842795337/100000000000000 : ℝ), (12731248709191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686729199/5000000000 : ℝ)|^67 ≤ (44220908480967/100000000000000 : ℝ)^51
        have hw : |(2686729199/5000000000 : ℝ)|=(2686729199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105292147/200000000 : ℝ)|^67 ≤ (43047842795337/100000000000000 : ℝ)^51
        have hw : |(105292147/200000000 : ℝ)|=(105292147/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-416546171/2000000000 : ℝ)|^67 ≤ (12731248709191/100000000000000 : ℝ)^51
        have hw : |(-416546171/2000000000 : ℝ)|=(416546171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_box_7 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4180870089/10000000000 : ℝ)*x 0 + (1102219031/2500000000 : ℝ)*x 1 + (4408875761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180870089/10000000000 : ℝ)^67 ≤ (31801556333189/100000000000000 : ℝ)^51 := by
    have hnat : (4180870089 : ℕ)^67*100000000000000^51 ≤ 31801556333189^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180870089 10000000000 31801556333189 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102219031/2500000000 : ℝ)^67 ≤ (34099223674583/100000000000000 : ℝ)^51 := by
    have hnat : (1102219031 : ℕ)^67*100000000000000^51 ≤ 34099223674583^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102219031 2500000000 34099223674583 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4408875761/10000000000 : ℝ)^67 ≤ (34099219986269/100000000000000 : ℝ)^51 := by
    have hnat : (4408875761 : ℕ)^67*100000000000000^51 ≤ 34099219986269^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4408875761 10000000000 34099219986269 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180870089/10000000000 : ℝ), (1102219031/2500000000 : ℝ), (4408875761/10000000000 : ℝ)] ![(31801556333189/100000000000000 : ℝ), (34099223674583/100000000000000 : ℝ), (34099219986269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180870089/10000000000 : ℝ)|^67 ≤ (31801556333189/100000000000000 : ℝ)^51
        have hw : |(4180870089/10000000000 : ℝ)|=(4180870089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1102219031/2500000000 : ℝ)|^67 ≤ (34099223674583/100000000000000 : ℝ)^51
        have hw : |(1102219031/2500000000 : ℝ)|=(1102219031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4408875761/10000000000 : ℝ)|^67 ≤ (34099219986269/100000000000000 : ℝ)^51
        have hw : |(4408875761/10000000000 : ℝ)|=(4408875761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_box_8 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-431200263/2000000000 : ℝ)*x 0 + (1035597883/2000000000 : ℝ)*x 1 + (5404548577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431200263/2000000000 : ℝ)^67 ≤ (6661434137691/50000000000000 : ℝ)^51 := by
    have hnat : (431200263 : ℕ)^67*50000000000000^51 ≤ 6661434137691^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431200263 2000000000 6661434137691 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035597883/2000000000 : ℝ)^67 ≤ (21059896471793/50000000000000 : ℝ)^51 := by
    have hnat : (1035597883 : ℕ)^67*50000000000000^51 ≤ 21059896471793^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035597883 2000000000 21059896471793 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404548577/10000000000 : ℝ)^67 ≤ (8911467752787/20000000000000 : ℝ)^51 := by
    have hnat : (5404548577 : ℕ)^67*20000000000000^51 ≤ 8911467752787^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404548577 10000000000 8911467752787 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-431200263/2000000000 : ℝ), (1035597883/2000000000 : ℝ), (5404548577/10000000000 : ℝ)] ![(6661434137691/50000000000000 : ℝ), (21059896471793/50000000000000 : ℝ), (8911467752787/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-431200263/2000000000 : ℝ)|^67 ≤ (6661434137691/50000000000000 : ℝ)^51
        have hw : |(-431200263/2000000000 : ℝ)|=(431200263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035597883/2000000000 : ℝ)|^67 ≤ (21059896471793/50000000000000 : ℝ)^51
        have hw : |(1035597883/2000000000 : ℝ)|=(1035597883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404548577/10000000000 : ℝ)|^67 ≤ (8911467752787/20000000000000 : ℝ)^51
        have hw : |(5404548577/10000000000 : ℝ)|=(5404548577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_box_9 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5275101969/10000000000 : ℝ)*x 0 + (-253319227/1250000000 : ℝ)*x 1 + (1080909881/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275101969/10000000000 : ℝ)^67 ≤ (4316061249631/10000000000000 : ℝ)^51 := by
    have hnat : (5275101969 : ℕ)^67*10000000000000^51 ≤ 4316061249631^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275101969 10000000000 4316061249631 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253319227/1250000000 : ℝ)^67 ≤ (2456407952751/20000000000000 : ℝ)^51 := by
    have hnat : (253319227 : ℕ)^67*20000000000000^51 ≤ 2456407952751^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253319227 1250000000 2456407952751 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080909881/2000000000 : ℝ)^67 ≤ (44557347731919/100000000000000 : ℝ)^51 := by
    have hnat : (1080909881 : ℕ)^67*100000000000000^51 ≤ 44557347731919^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080909881 2000000000 44557347731919 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275101969/10000000000 : ℝ), (-253319227/1250000000 : ℝ), (1080909881/2000000000 : ℝ)] ![(4316061249631/10000000000000 : ℝ), (2456407952751/20000000000000 : ℝ), (44557347731919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275101969/10000000000 : ℝ)|^67 ≤ (4316061249631/10000000000000 : ℝ)^51
        have hw : |(5275101969/10000000000 : ℝ)|=(5275101969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-253319227/1250000000 : ℝ)|^67 ≤ (2456407952751/20000000000000 : ℝ)^51
        have hw : |(-253319227/1250000000 : ℝ)|=(253319227/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080909881/2000000000 : ℝ)|^67 ≤ (44557347731919/100000000000000 : ℝ)^51
        have hw : |(1080909881/2000000000 : ℝ)|=(1080909881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_box_10 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1318775689/2500000000 : ℝ)*x 0 + (5404548629/10000000000 : ℝ)*x 1 + (-2026553809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318775689/2500000000 : ℝ)^67 ≤ (21580310477821/50000000000000 : ℝ)^51 := by
    have hnat : (1318775689 : ℕ)^67*50000000000000^51 ≤ 21580310477821^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318775689 2500000000 21580310477821 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404548629/10000000000 : ℝ)^67 ≤ (22278669663571/50000000000000 : ℝ)^51 := by
    have hnat : (5404548629 : ℕ)^67*50000000000000^51 ≤ 22278669663571^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404548629 10000000000 22278669663571 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2026553809/10000000000 : ℝ)^67 ≤ (6141019854011/50000000000000 : ℝ)^51 := by
    have hnat : (2026553809 : ℕ)^67*50000000000000^51 ≤ 6141019854011^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026553809 10000000000 6141019854011 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318775689/2500000000 : ℝ), (5404548629/10000000000 : ℝ), (-2026553809/10000000000 : ℝ)] ![(21580310477821/50000000000000 : ℝ), (22278669663571/50000000000000 : ℝ), (6141019854011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318775689/2500000000 : ℝ)|^67 ≤ (21580310477821/50000000000000 : ℝ)^51
        have hw : |(1318775689/2500000000 : ℝ)|=(1318775689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404548629/10000000000 : ℝ)|^67 ≤ (22278669663571/50000000000000 : ℝ)^51
        have hw : |(5404548629/10000000000 : ℝ)|=(5404548629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2026553809/10000000000 : ℝ)|^67 ≤ (6141019854011/50000000000000 : ℝ)^51
        have hw : |(-2026553809/10000000000 : ℝ)|=(2026553809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_box_11 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (451144511/1000000000 : ℝ)*x 0 + (4243354849/10000000000 : ℝ)*x 1 + (848671029/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (451144511/1000000000 : ℝ)^67 ≤ (17572586858057/50000000000000 : ℝ)^51 := by
    have hnat : (451144511 : ℕ)^67*50000000000000^51 ≤ 17572586858057^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451144511 1000000000 17572586858057 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4243354849/10000000000 : ℝ)^67 ≤ (32427411642493/100000000000000 : ℝ)^51 := by
    have hnat : (4243354849 : ℕ)^67*100000000000000^51 ≤ 32427411642493^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243354849 10000000000 32427411642493 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848671029/2000000000 : ℝ)^67 ≤ (16213707307077/50000000000000 : ℝ)^51 := by
    have hnat : (848671029 : ℕ)^67*50000000000000^51 ≤ 16213707307077^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848671029 2000000000 16213707307077 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(451144511/1000000000 : ℝ), (4243354849/10000000000 : ℝ), (848671029/2000000000 : ℝ)] ![(17572586858057/50000000000000 : ℝ), (32427411642493/100000000000000 : ℝ), (16213707307077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(451144511/1000000000 : ℝ)|^67 ≤ (17572586858057/50000000000000 : ℝ)^51
        have hw : |(451144511/1000000000 : ℝ)|=(451144511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4243354849/10000000000 : ℝ)|^67 ≤ (32427411642493/100000000000000 : ℝ)^51
        have hw : |(4243354849/10000000000 : ℝ)|=(4243354849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848671029/2000000000 : ℝ)|^67 ≤ (16213707307077/50000000000000 : ℝ)^51
        have hw : |(848671029/2000000000 : ℝ)|=(848671029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_box_12 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-979688943/5000000000 : ℝ)*x 0 + (5474904203/10000000000 : ℝ)*x 1 + (5253549891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (979688943/5000000000 : ℝ)^67 ≤ (11749993819593/100000000000000 : ℝ)^51 := by
    have hnat : (979688943 : ℕ)^67*100000000000000^51 ≤ 11749993819593^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979688943 5000000000 11749993819593 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474904203/10000000000 : ℝ)^67 ≤ (45320904775857/100000000000000 : ℝ)^51 := by
    have hnat : (5474904203 : ℕ)^67*100000000000000^51 ≤ 45320904775857^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474904203 10000000000 45320904775857 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253549891/10000000000 : ℝ)^67 ≤ (21464550693659/50000000000000 : ℝ)^51 := by
    have hnat : (5253549891 : ℕ)^67*50000000000000^51 ≤ 21464550693659^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253549891 10000000000 21464550693659 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-979688943/5000000000 : ℝ), (5474904203/10000000000 : ℝ), (5253549891/10000000000 : ℝ)] ![(11749993819593/100000000000000 : ℝ), (45320904775857/100000000000000 : ℝ), (21464550693659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-979688943/5000000000 : ℝ)|^67 ≤ (11749993819593/100000000000000 : ℝ)^51
        have hw : |(-979688943/5000000000 : ℝ)|=(979688943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5474904203/10000000000 : ℝ)|^67 ≤ (45320904775857/100000000000000 : ℝ)^51
        have hw : |(5474904203/10000000000 : ℝ)|=(5474904203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253549891/10000000000 : ℝ)|^67 ≤ (21464550693659/50000000000000 : ℝ)^51
        have hw : |(5253549891/10000000000 : ℝ)|=(5253549891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_box_13 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2690613401/5000000000 : ℝ)*x 0 + (-1043527311/5000000000 : ℝ)*x 1 + (5253550117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690613401/5000000000 : ℝ)^67 ≤ (44304914159389/100000000000000 : ℝ)^51 := by
    have hnat : (2690613401 : ℕ)^67*100000000000000^51 ≤ 44304914159389^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690613401 5000000000 44304914159389 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043527311/5000000000 : ℝ)^67 ≤ (6382991006603/50000000000000 : ℝ)^51 := by
    have hnat : (1043527311 : ℕ)^67*50000000000000^51 ≤ 6382991006603^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043527311 5000000000 6382991006603 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253550117/10000000000 : ℝ)^67 ≤ (10732275953359/25000000000000 : ℝ)^51 := by
    have hnat : (5253550117 : ℕ)^67*25000000000000^51 ≤ 10732275953359^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253550117 10000000000 10732275953359 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690613401/5000000000 : ℝ), (-1043527311/5000000000 : ℝ), (5253550117/10000000000 : ℝ)] ![(44304914159389/100000000000000 : ℝ), (6382991006603/50000000000000 : ℝ), (10732275953359/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690613401/5000000000 : ℝ)|^67 ≤ (44304914159389/100000000000000 : ℝ)^51
        have hw : |(2690613401/5000000000 : ℝ)|=(2690613401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1043527311/5000000000 : ℝ)|^67 ≤ (6382991006603/50000000000000 : ℝ)^51
        have hw : |(-1043527311/5000000000 : ℝ)|=(1043527311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253550117/10000000000 : ℝ)|^67 ≤ (10732275953359/25000000000000 : ℝ)^51
        have hw : |(5253550117/10000000000 : ℝ)|=(5253550117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_box_14 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1076245349/2000000000 : ℝ)*x 0 + (1313387499/2500000000 : ℝ)*x 1 + (-2087054861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076245349/2000000000 : ℝ)^67 ≤ (8860982708573/20000000000000 : ℝ)^51 := by
    have hnat : (1076245349 : ℕ)^67*20000000000000^51 ≤ 8860982708573^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076245349 2000000000 8860982708573 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313387499/2500000000 : ℝ)^67 ≤ (42929102514497/100000000000000 : ℝ)^51 := by
    have hnat : (1313387499 : ℕ)^67*100000000000000^51 ≤ 42929102514497^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313387499 2500000000 42929102514497 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2087054861/10000000000 : ℝ)^67 ≤ (797873995859/6250000000000 : ℝ)^51 := by
    have hnat : (2087054861 : ℕ)^67*6250000000000^51 ≤ 797873995859^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087054861 10000000000 797873995859 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076245349/2000000000 : ℝ), (1313387499/2500000000 : ℝ), (-2087054861/10000000000 : ℝ)] ![(8860982708573/20000000000000 : ℝ), (42929102514497/100000000000000 : ℝ), (797873995859/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076245349/2000000000 : ℝ)|^67 ≤ (8860982708573/20000000000000 : ℝ)^51
        have hw : |(1076245349/2000000000 : ℝ)|=(1076245349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313387499/2500000000 : ℝ)|^67 ≤ (42929102514497/100000000000000 : ℝ)^51
        have hw : |(1313387499/2500000000 : ℝ)|=(1313387499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2087054861/10000000000 : ℝ)|^67 ≤ (797873995859/6250000000000 : ℝ)^51
        have hw : |(-2087054861/10000000000 : ℝ)|=(2087054861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_box_15 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4154257701/10000000000 : ℝ)*x 0 + (884388631/2000000000 : ℝ)*x 1 + (4421943143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4154257701/10000000000 : ℝ)^67 ≤ (15767945253629/50000000000000 : ℝ)^51 := by
    have hnat : (4154257701 : ℕ)^67*50000000000000^51 ≤ 15767945253629^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154257701 10000000000 15767945253629 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (884388631/2000000000 : ℝ)^67 ≤ (34232054804603/100000000000000 : ℝ)^51 := by
    have hnat : (884388631 : ℕ)^67*100000000000000^51 ≤ 34232054804603^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884388631 2000000000 34232054804603 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4421943143/10000000000 : ℝ)^67 ≤ (17116027341281/50000000000000 : ℝ)^51 := by
    have hnat : (4421943143 : ℕ)^67*50000000000000^51 ≤ 17116027341281^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4421943143 10000000000 17116027341281 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4154257701/10000000000 : ℝ), (884388631/2000000000 : ℝ), (4421943143/10000000000 : ℝ)] ![(15767945253629/50000000000000 : ℝ), (34232054804603/100000000000000 : ℝ), (17116027341281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4154257701/10000000000 : ℝ)|^67 ≤ (15767945253629/50000000000000 : ℝ)^51
        have hw : |(4154257701/10000000000 : ℝ)|=(4154257701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(884388631/2000000000 : ℝ)|^67 ≤ (34232054804603/100000000000000 : ℝ)^51
        have hw : |(884388631/2000000000 : ℝ)|=(884388631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4421943143/10000000000 : ℝ)|^67 ≤ (17116027341281/50000000000000 : ℝ)^51
        have hw : |(4421943143/10000000000 : ℝ)|=(4421943143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1328_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(1257/2000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29457/50000 : ℝ) ∧ (2496/3125 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84297/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14697/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11117/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14697/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11117/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14697/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11117/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14697/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11117/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14697/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11117/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14697/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11117/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11117/100000 : ℝ) ^ (4287/1024 : ℝ) ≤ (2534806196443621/25000000000000000000 : ℝ) := by
    have hpowers : (11117/100000 : ℝ)^4287 ≤ (2534806196443621/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11117 : ℕ)^4287*25000000000000000000^1024 ≤ 2534806196443621^1024*100000^4287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11117 100000 2534806196443621 25000000000000000000 4287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11117/100000 : ℝ)) (X := (2534806196443621/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14697/100000 : ℝ) ^ (4287/1024 : ℝ) ≤ (32627470831599221/100000000000000000000 : ℝ) := by
    have hpowers : (14697/100000 : ℝ)^4287 ≤ (32627470831599221/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14697 : ℕ)^4287*100000000000000000000^1024 ≤ 32627470831599221^1024*100000^4287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14697 100000 32627470831599221 100000000000000000000 4287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14697/100000 : ℝ)) (X := (32627470831599221/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502534806196443621/12500000000000000000 : ℝ) ≤ (1000048433706633/1000000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (12502534806196443621/12500000000000000000 : ℝ)^1024 ≤ (1000048433706633/1000000000000000 : ℝ)^4287 := by
      have hnat : (12502534806196443621 : ℕ)^1024*1000000000000000^4287 ≤ 1000048433706633^4287*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502534806196443621 12500000000000000000 1000048433706633 1000000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000048433706633/1000000000000000 : ℝ)) (X := (12502534806196443621/12500000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008553339123474741/20000000000000000000 : ℝ) ≤ (2000204273246907/2000000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (20008553339123474741/20000000000000000000 : ℝ)^1024 ≤ (2000204273246907/2000000000000000 : ℝ)^4287 := by
      have hnat : (20008553339123474741 : ℕ)^1024*2000000000000000^4287 ≤ 2000204273246907^4287*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008553339123474741 20000000000000000000 2000204273246907 2000000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000204273246907/2000000000000000 : ℝ)) (X := (20008553339123474741/20000000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032627470831599221/50000000000000000000 : ℝ) ≤ (500077919770137/500000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (50032627470831599221/50000000000000000000 : ℝ)^1024 ≤ (500077919770137/500000000000000 : ℝ)^4287 := by
      have hnat : (50032627470831599221 : ℕ)^1024*500000000000000^4287 ≤ 500077919770137^4287*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032627470831599221 50000000000000000000 500077919770137 500000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500077919770137/500000000000000 : ℝ)) (X := (50032627470831599221/50000000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2534806196443621/25000000000000000000 : ℝ) ≤ ((3578979362017159143/3580000000000000000 : ℝ)+2*(107405833641/71600000000000 : ℝ)*(11117/100000 : ℝ))^(4287/1024 : ℝ) := by
    rw [show (3578979362017159143/3580000000000000000 : ℝ)+2*(107405833641/71600000000000 : ℝ)*(11117/100000 : ℝ)=(1000048433706633/1000000000000000 : ℝ) by norm_num, show 1+2*(2534806196443621/25000000000000000000 : ℝ)=(12502534806196443621/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32627470831599221/100000000000000000000 : ℝ)+(2534806196443621/25000000000000000000 : ℝ) ≤ ((3578979362017159143/3580000000000000000 : ℝ)+(107405833641/71600000000000 : ℝ)*((14697/100000 : ℝ)+(11117/100000 : ℝ)))^(4287/1024 : ℝ) := by
    rw [show (3578979362017159143/3580000000000000000 : ℝ)+(107405833641/71600000000000 : ℝ)*((14697/100000 : ℝ)+(11117/100000 : ℝ))=(2000204273246907/2000000000000000 : ℝ) by norm_num, show 1+(32627470831599221/100000000000000000000 : ℝ)+(2534806196443621/25000000000000000000 : ℝ)=(20008553339123474741/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32627470831599221/100000000000000000000 : ℝ) ≤ ((3578979362017159143/3580000000000000000 : ℝ)+2*(107405833641/71600000000000 : ℝ)*(14697/100000 : ℝ))^(4287/1024 : ℝ) := by
    rw [show (3578979362017159143/3580000000000000000 : ℝ)+2*(107405833641/71600000000000 : ℝ)*(14697/100000 : ℝ)=(500077919770137/500000000000000 : ℝ) by norm_num, show 1+2*(32627470831599221/100000000000000000000 : ℝ)=(50032627470831599221/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3578979362017159143/3580000000000000000 : ℝ)*(X 1 0+X 2 0)+(107405833641/71600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (11117/100000 : ℝ)) (hi := (14697/100000 : ℝ)) (c := (3578979362017159143/3580000000000000000 : ℝ)) (alpha := (107405833641/71600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3578979362017159143/3580000000000000000 : ℝ)*(X 0 1+X 2 1)+(107405833641/71600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (11117/100000 : ℝ)) (hi := (14697/100000 : ℝ)) (c := (3578979362017159143/3580000000000000000 : ℝ)) (alpha := (107405833641/71600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3578979362017159143/3580000000000000000 : ℝ)*(X 0 2+X 1 2)+(107405833641/71600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (11117/100000 : ℝ)) (hi := (14697/100000 : ℝ)) (c := (3578979362017159143/3580000000000000000 : ℝ)) (alpha := (107405833641/71600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-943877843/5000000000 : ℝ)*X 0 0+(2695261843/5000000000 : ℝ)*X 0 1+(539052337/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642482337/5000000000 : ℝ)*X 1 0+(-2032304499/10000000000 : ℝ)*X 1 1+(2695261789/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((211398571/400000000 : ℝ)*X 2 0+(5390524007/10000000000 : ℝ)*X 2 1+(-406460891/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4478817527/10000000000 : ℝ)*X 0 0+(212997807/500000000 : ℝ)*X 0 1+(4259956447/10000000000 : ℝ)*X 0 2+(4478817527/10000000000 : ℝ)*X 1 0+(212997807/500000000 : ℝ)*X 1 1+(4259956447/10000000000 : ℝ)*X 1 2+(4478817527/10000000000 : ℝ)*X 2 0+(212997807/500000000 : ℝ)*X 2 1+(4259956447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-278407323/1250000000 : ℝ)*X 0 0+(2632303467/5000000000 : ℝ)*X 0 1+(5264607507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5373458121/10000000000 : ℝ)*X 1 0+(-1041365543/5000000000 : ℝ)*X 1 1+(164518983/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2686729199/5000000000 : ℝ)*X 2 0+(105292147/200000000 : ℝ)*X 2 1+(-416546171/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4180870089/10000000000 : ℝ)*X 0 0+(1102219031/2500000000 : ℝ)*X 0 1+(4408875761/10000000000 : ℝ)*X 0 2+(4180870089/10000000000 : ℝ)*X 1 0+(1102219031/2500000000 : ℝ)*X 1 1+(4408875761/10000000000 : ℝ)*X 1 2+(4180870089/10000000000 : ℝ)*X 2 0+(1102219031/2500000000 : ℝ)*X 2 1+(4408875761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-431200263/2000000000 : ℝ)*X 0 0+(1035597883/2000000000 : ℝ)*X 0 1+(5404548577/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275101969/10000000000 : ℝ)*X 1 0+(-253319227/1250000000 : ℝ)*X 1 1+(1080909881/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1318775689/2500000000 : ℝ)*X 2 0+(5404548629/10000000000 : ℝ)*X 2 1+(-2026553809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((451144511/1000000000 : ℝ)*X 0 0+(4243354849/10000000000 : ℝ)*X 0 1+(848671029/2000000000 : ℝ)*X 0 2+(451144511/1000000000 : ℝ)*X 1 0+(4243354849/10000000000 : ℝ)*X 1 1+(848671029/2000000000 : ℝ)*X 1 2+(451144511/1000000000 : ℝ)*X 2 0+(4243354849/10000000000 : ℝ)*X 2 1+(848671029/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-979688943/5000000000 : ℝ)*X 0 0+(5474904203/10000000000 : ℝ)*X 0 1+(5253549891/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2690613401/5000000000 : ℝ)*X 1 0+(-1043527311/5000000000 : ℝ)*X 1 1+(5253550117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1076245349/2000000000 : ℝ)*X 2 0+(1313387499/2500000000 : ℝ)*X 2 1+(-2087054861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4154257701/10000000000 : ℝ)*X 0 0+(884388631/2000000000 : ℝ)*X 0 1+(4421943143/10000000000 : ℝ)*X 0 2+(4154257701/10000000000 : ℝ)*X 1 0+(884388631/2000000000 : ℝ)*X 1 1+(4421943143/10000000000 : ℝ)*X 1 2+(4154257701/10000000000 : ℝ)*X 2 0+(884388631/2000000000 : ℝ)*X 2 1+(4421943143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-1257/2000 : ℝ) ≤ (-112497088625740522870421047723971/179000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (282373/5000000000000 : ℝ)*(upper1) + (136032999/100000000000000 : ℝ)*(lower2) + (13477847/100000000000000 : ℝ)*(upper5) + (2904936406436599/100000000000000 : ℝ)*(major0) + (2904936406436599/100000000000000 : ℝ)*(major1) + (2904936406436599/100000000000000 : ℝ)*(major2) + (322753399/50000000000000 : ℝ)*(sp1) + (1149158361/100000000000000 : ℝ)*(sp3) + (1973331172741187/50000000000000 : ℝ)*(sp4) + (986666861238417/25000000000000 : ℝ)*(sp5) + (1973320530141299/50000000000000 : ℝ)*(sp6) + (1884152751769399/100000000000000 : ℝ)*(sp7) + (574497809/10000000000000 : ℝ)*(sp12) + (27030177867/100000000000000 : ℝ)*(sp14) + (23551923761597/1250000000000 : ℝ)*(f.failure) + (789333618092093/20000000000000 : ℝ)*(f.sum) + (8228332531799/3580000000000000000000000000 : ℝ)*base65 + (5143357943554624657/358000000000000000000000000000000 : ℝ)*base67 + (2075476509658624657/358000000000000000000000000000000 : ℝ)*base69 + (993328353733375343/358000000000000000000000000000000 : ℝ)*base72 + (24488245876679/3580000000000000000000000000 : ℝ)*base73 + (2325117502093375343/358000000000000000000000000000000 : ℝ)*base76 + (3143855958704624657/358000000000000000000000000000000 : ℝ)*base77 + (580311335486624657/358000000000000000000000000000000 : ℝ)*base79 + (7345149432861/3580000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (86027/31250000000000000000 : ℝ)*base90 + (86027/31250000000000000000 : ℝ)*base92 + (86027/31250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29457/50000 : ℝ) ≤ (52730327513853724492832815440261/89500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14314689/50000000000000 : ℝ)*(lower1) + (33911327/50000000000000 : ℝ)*(upper2) + (1123437/100000000000000 : ℝ)*(upper3) + (593879/20000000000000 : ℝ)*(lower5) + (1486580479978203/50000000000000 : ℝ)*(major0) + (1486580479978203/50000000000000 : ℝ)*(major1) + (1486580479978203/50000000000000 : ℝ)*(major2) + (9995690278623/250000000000 : ℝ)*(sp0) + (1999137224654173/50000000000000 : ℝ)*(sp1) + (999566021522661/25000000000000 : ℝ)*(sp2) + (96420231581931/5000000000000 : ℝ)*(sp3) + (159331239/4000000000000 : ℝ)*(sp5) + (14346498677/100000000000000 : ℝ)*(sp6) + (1160570061/50000000000000 : ℝ)*(sp8) + (96420231581931/5000000000000 : ℝ)*(f.failure) + (1999139216294661/50000000000000 : ℝ)*(f.sum) + (7200844940223/1790000000000000000000000000 : ℝ)*base65 + (1853336959791689971/179000000000000000000000000000000 : ℝ)*base68 + (1492509995607689971/179000000000000000000000000000000 : ℝ)*base70 + (1275099528522689971/179000000000000000000000000000000 : ℝ)*base72 + (7278695287283/1790000000000000000000000000 : ℝ)*base73 + (542489189333689971/179000000000000000000000000000000 : ℝ)*base76 + (1291453929215689971/179000000000000000000000000000000 : ℝ)*base78 + (443892146203689971/179000000000000000000000000000000 : ℝ)*base80 + (13199306466973/1790000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (219321/125000000000000000000 : ℝ)*base90 + (219321/125000000000000000000 : ℝ)*base92 + (219321/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (2496/3125 : ℝ) ≤ (399372836585525924298178216287/500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (365737263/100000000000000 : ℝ)*(lower3) + (88254317/100000000000000 : ℝ)*(upper4) + (37124013/25000000000000 : ℝ)*(lower5) + (1642938985771821/50000000000000 : ℝ)*(major0) + (1642938985771821/50000000000000 : ℝ)*(major1) + (1642938985771821/50000000000000 : ℝ)*(major2) + (30317592919/100000000000000 : ℝ)*(sp0) + (275822943273/50000000000000 : ℝ)*(sp1) + (288954162047/100000000000000 : ℝ)*(sp2) + (180578367221/100000000000000 : ℝ)*(sp3) + (1103466644166011/25000000000000 : ℝ)*(sp8) + (2206672624185209/50000000000000 : ℝ)*(sp9) + (1103401985023729/25000000000000 : ℝ)*(sp10) + (2131053614690723/100000000000000 : ℝ)*(sp11) + (266404274132243/12500000000000 : ℝ)*(f.failure) + (1103474223564241/25000000000000 : ℝ)*(f.sum) + (38223518109/1790000000000000000000000000 : ℝ)*base66 + (3311224780635959403/179000000000000000000000000000000 : ℝ)*base67 + (1924261255994959403/179000000000000000000000000000000 : ℝ)*base69 + (249215055457959403/179000000000000000000000000000000 : ℝ)*base71 + (11333153297511/1790000000000000000000000000 : ℝ)*base73 + (76229373654959403/179000000000000000000000000000000 : ℝ)*base75 + (930483618332959403/179000000000000000000000000000000 : ℝ)*base77 + (1324153155614959403/179000000000000000000000000000000 : ℝ)*base79 + (5220979974791/1790000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (194913/312500000000000000000 : ℝ)*base90 + (194913/312500000000000000000 : ℝ)*base92 + (194913/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-84297/100000 : ℝ) ≤ (-1508876302827193316004718827/1790000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3118391/5000000000000 : ℝ)*(lower0) + (24724511/100000000000000 : ℝ)*(lower1) + (15834849/50000000000000 : ℝ)*(upper3) + (99851879/100000000000000 : ℝ)*(lower4) + (1661080316853681/50000000000000 : ℝ)*(major0) + (1661080316853681/50000000000000 : ℝ)*(major1) + (1661080316853681/50000000000000 : ℝ)*(major2) + (3815548437/4000000000000 : ℝ)*(sp6) + (874341407/2000000000000 : ℝ)*(sp7) + (302682941/10000000000000 : ℝ)*(sp8) + (2258824608148349/50000000000000 : ℝ)*(sp12) + (1129413060781527/25000000000000 : ℝ)*(sp13) + (2258778427207591/50000000000000 : ℝ)*(sp14) + (1077361781195973/50000000000000 : ℝ)*(sp15) + (269345909932787/12500000000000 : ℝ)*(f.failure) + (1129413060781527/25000000000000 : ℝ)*(f.sum) + (1358692982699/1790000000000000000000000000 : ℝ)*base66 + (1309959983697594617/179000000000000000000000000000000 : ℝ)*base68 + (6411643164984405383/179000000000000000000000000000000 : ℝ)*base69 + (393687903500405383/179000000000000000000000000000000 : ℝ)*base71 + (11019214036139/1790000000000000000000000000 : ℝ)*base74 + (3127328616507594617/179000000000000000000000000000000 : ℝ)*base76 + (319851455304405383/179000000000000000000000000000000 : ℝ)*base77 + (1451874974559594617/179000000000000000000000000000000 : ℝ)*base80 + (2751900011231/1790000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (5109183/312500000000000000000 : ℝ)*base89 + (5109183/312500000000000000000 : ℝ)*base91 + (5109183/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1328_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1257/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(29457/50000 : ℝ) else (2496/3125 : ℝ) ≤ X j i ∧ X j i ≤ (84297/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1328_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1328_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1257/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(29457/50000 : ℝ) else (2496/3125 : ℝ) ≤ X j i ∧ X j i ≤ (84297/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1328_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14697/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11117/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1257/2000 : ℝ) ≤ X j i ∧ X j i ≤ -(29457/50000 : ℝ) else (2496/3125 : ℝ) ≤ X j i ∧ X j i ≤ (84297/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1328_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

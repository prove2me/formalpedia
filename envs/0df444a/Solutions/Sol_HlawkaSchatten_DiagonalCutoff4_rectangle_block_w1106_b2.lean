-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1106_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:03:17.877523+00:00
-- url     : https://prove2.me/submissions/e9c09d0e-a210-4eb4-8857-974ac1f2f7a3

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
theorem support_rectangle_w1106_s6_0 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1092092633/5000000000 : ℝ)*x 0 + (337131527/625000000 : ℝ)*x 1 + (1316184299/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092092633/5000000000 : ℝ)^8299 ≤ (13268519969541/100000000000000 : ℝ)^6251 := by
    have hnat : (1092092633 : ℕ)^8299*100000000000000^6251 ≤ 13268519969541^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092092633 5000000000 13268519969541 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337131527/625000000 : ℝ)^8299 ≤ (22032244387847/50000000000000 : ℝ)^6251 := by
    have hnat : (337131527 : ℕ)^8299*50000000000000^6251 ≤ 22032244387847^6251*625000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337131527 625000000 22032244387847 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316184299/2500000000 : ℝ)^8299 ≤ (42666991240673/100000000000000 : ℝ)^6251 := by
    have hnat : (1316184299 : ℕ)^8299*100000000000000^6251 ≤ 42666991240673^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316184299 2500000000 42666991240673 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1092092633/5000000000 : ℝ), (337131527/625000000 : ℝ), (1316184299/2500000000 : ℝ)] ![(13268519969541/100000000000000 : ℝ), (22032244387847/50000000000000 : ℝ), (42666991240673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1092092633/5000000000 : ℝ)|^8299 ≤ (13268519969541/100000000000000 : ℝ)^6251
        have hw : |(-1092092633/5000000000 : ℝ)|=(1092092633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337131527/625000000 : ℝ)|^8299 ≤ (22032244387847/50000000000000 : ℝ)^6251
        have hw : |(337131527/625000000 : ℝ)|=(337131527/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316184299/2500000000 : ℝ)|^8299 ≤ (42666991240673/100000000000000 : ℝ)^6251
        have hw : |(1316184299/2500000000 : ℝ)|=(1316184299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s6_1 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344985181/10000000000 : ℝ)*x 0 + (-281227247/1250000000 : ℝ)*x 1 + (1052947433/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344985181/10000000000 : ℝ)^8299 ≤ (43532567042413/100000000000000 : ℝ)^6251 := by
    have hnat : (5344985181 : ℕ)^8299*100000000000000^6251 ≤ 43532567042413^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344985181 10000000000 43532567042413 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281227247/1250000000 : ℝ)^8299 ≤ (13800442039891/100000000000000 : ℝ)^6251 := by
    have hnat : (281227247 : ℕ)^8299*100000000000000^6251 ≤ 13800442039891^6251*1250000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281227247 1250000000 13800442039891 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052947433/2000000000 : ℝ)^8299 ≤ (42666990907129/100000000000000 : ℝ)^6251 := by
    have hnat : (1052947433 : ℕ)^8299*100000000000000^6251 ≤ 42666990907129^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052947433 2000000000 42666990907129 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344985181/10000000000 : ℝ), (-281227247/1250000000 : ℝ), (1052947433/2000000000 : ℝ)] ![(43532567042413/100000000000000 : ℝ), (13800442039891/100000000000000 : ℝ), (42666990907129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344985181/10000000000 : ℝ)|^8299 ≤ (43532567042413/100000000000000 : ℝ)^6251
        have hw : |(5344985181/10000000000 : ℝ)|=(5344985181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-281227247/1250000000 : ℝ)|^8299 ≤ (13800442039891/100000000000000 : ℝ)^6251
        have hw : |(-281227247/1250000000 : ℝ)|=(281227247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052947433/2000000000 : ℝ)|^8299 ≤ (42666990907129/100000000000000 : ℝ)^6251
        have hw : |(1052947433/2000000000 : ℝ)|=(1052947433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s6_2 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336246303/2500000000 : ℝ)*x 0 + (5264737163/10000000000 : ℝ)*x 1 + (-2249817937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336246303/2500000000 : ℝ)^8299 ≤ (8706513475523/20000000000000 : ℝ)^6251 := by
    have hnat : (1336246303 : ℕ)^8299*20000000000000^6251 ≤ 8706513475523^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336246303 2500000000 8706513475523 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264737163/10000000000 : ℝ)^8299 ≤ (4266699088561/10000000000000 : ℝ)^6251 := by
    have hnat : (5264737163 : ℕ)^8299*10000000000000^6251 ≤ 4266699088561^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264737163 10000000000 4266699088561 10000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249817937/10000000000 : ℝ)^8299 ≤ (13800441722287/100000000000000 : ℝ)^6251 := by
    have hnat : (2249817937 : ℕ)^8299*100000000000000^6251 ≤ 13800441722287^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249817937 10000000000 13800441722287 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336246303/2500000000 : ℝ), (5264737163/10000000000 : ℝ), (-2249817937/10000000000 : ℝ)] ![(8706513475523/20000000000000 : ℝ), (4266699088561/10000000000000 : ℝ), (13800441722287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336246303/2500000000 : ℝ)|^8299 ≤ (8706513475523/20000000000000 : ℝ)^6251
        have hw : |(1336246303/2500000000 : ℝ)|=(1336246303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264737163/10000000000 : ℝ)|^8299 ≤ (4266699088561/10000000000000 : ℝ)^6251
        have hw : |(5264737163/10000000000 : ℝ)|=(5264737163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2249817937/10000000000 : ℝ)|^8299 ≤ (13800441722287/100000000000000 : ℝ)^6251
        have hw : |(-2249817937/10000000000 : ℝ)|=(2249817937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s6_3 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436974841/1000000000 : ℝ)*x 0 + (4243844757/10000000000 : ℝ)*x 1 + (2249700781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436974841/1000000000 : ℝ)^8299 ≤ (33316551646601/100000000000000 : ℝ)^6251 := by
    have hnat : (436974841 : ℕ)^8299*100000000000000^6251 ≤ 33316551646601^6251*1000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436974841 1000000000 33316551646601 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4243844757/10000000000 : ℝ)^8299 ≤ (32048169652223/100000000000000 : ℝ)^6251 := by
    have hnat : (4243844757 : ℕ)^8299*100000000000000^6251 ≤ 32048169652223^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243844757 10000000000 32048169652223 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2249700781/5000000000 : ℝ)^8299 ≤ (34635278694593/100000000000000 : ℝ)^6251 := by
    have hnat : (2249700781 : ℕ)^8299*100000000000000^6251 ≤ 34635278694593^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249700781 5000000000 34635278694593 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436974841/1000000000 : ℝ), (4243844757/10000000000 : ℝ), (2249700781/5000000000 : ℝ)] ![(33316551646601/100000000000000 : ℝ), (32048169652223/100000000000000 : ℝ), (34635278694593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436974841/1000000000 : ℝ)|^8299 ≤ (33316551646601/100000000000000 : ℝ)^6251
        have hw : |(436974841/1000000000 : ℝ)|=(436974841/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4243844757/10000000000 : ℝ)|^8299 ≤ (32048169652223/100000000000000 : ℝ)^6251
        have hw : |(4243844757/10000000000 : ℝ)|=(4243844757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2249700781/5000000000 : ℝ)|^8299 ≤ (34635278694593/100000000000000 : ℝ)^6251
        have hw : |(2249700781/5000000000 : ℝ)|=(2249700781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s6_4 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2184190317/10000000000 : ℝ)*x 0 + (5265063869/10000000000 : ℝ)*x 1 + (674222073/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184190317/10000000000 : ℝ)^8299 ≤ (13268560706331/100000000000000 : ℝ)^6251 := by
    have hnat : (2184190317 : ℕ)^8299*100000000000000^6251 ≤ 13268560706331^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184190317 10000000000 13268560706331 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265063869/10000000000 : ℝ)^8299 ≤ (1706820244419/4000000000000 : ℝ)^6251 := by
    have hnat : (5265063869 : ℕ)^8299*4000000000000^6251 ≤ 1706820244419^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265063869 10000000000 1706820244419 4000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674222073/1250000000 : ℝ)^8299 ≤ (22030466583883/50000000000000 : ℝ)^6251 := by
    have hnat : (674222073 : ℕ)^8299*50000000000000^6251 ≤ 22030466583883^6251*1250000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674222073 1250000000 22030466583883 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2184190317/10000000000 : ℝ), (5265063869/10000000000 : ℝ), (674222073/1250000000 : ℝ)] ![(13268560706331/100000000000000 : ℝ), (1706820244419/4000000000000 : ℝ), (22030466583883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2184190317/10000000000 : ℝ)|^8299 ≤ (13268560706331/100000000000000 : ℝ)^6251
        have hw : |(-2184190317/10000000000 : ℝ)|=(2184190317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265063869/10000000000 : ℝ)|^8299 ≤ (1706820244419/4000000000000 : ℝ)^6251
        have hw : |(5265063869/10000000000 : ℝ)|=(5265063869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674222073/1250000000 : ℝ)|^8299 ≤ (22030466583883/50000000000000 : ℝ)^6251
        have hw : |(674222073/1250000000 : ℝ)|=(674222073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s6_5 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656149137/5000000000 : ℝ)*x 0 + (-530194639/2500000000 : ℝ)*x 1 + (1078755317/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656149137/5000000000 : ℝ)^8299 ≤ (2158973992051/5000000000000 : ℝ)^6251 := by
    have hnat : (2656149137 : ℕ)^8299*5000000000000^6251 ≤ 2158973992051^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656149137 5000000000 2158973992051 5000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530194639/2500000000 : ℝ)^8299 ≤ (12759586969371/100000000000000 : ℝ)^6251 := by
    have hnat : (530194639 : ℕ)^8299*100000000000000^6251 ≤ 12759586969371^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530194639 2500000000 12759586969371 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078755317/2000000000 : ℝ)^8299 ≤ (44060933178611/100000000000000 : ℝ)^6251 := by
    have hnat : (1078755317 : ℕ)^8299*100000000000000^6251 ≤ 44060933178611^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078755317 2000000000 44060933178611 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656149137/5000000000 : ℝ), (-530194639/2500000000 : ℝ), (1078755317/2000000000 : ℝ)] ![(2158973992051/5000000000000 : ℝ), (12759586969371/100000000000000 : ℝ), (44060933178611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656149137/5000000000 : ℝ)|^8299 ≤ (2158973992051/5000000000000 : ℝ)^6251
        have hw : |(2656149137/5000000000 : ℝ)|=(2656149137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-530194639/2500000000 : ℝ)|^8299 ≤ (12759586969371/100000000000000 : ℝ)^6251
        have hw : |(-530194639/2500000000 : ℝ)|=(530194639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078755317/2000000000 : ℝ)|^8299 ≤ (44060933178611/100000000000000 : ℝ)^6251
        have hw : |(1078755317/2000000000 : ℝ)|=(1078755317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s6_6 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312298273/10000000000 : ℝ)*x 0 + (1078755317/2000000000 : ℝ)*x 1 + (-530194639/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312298273/10000000000 : ℝ)^8299 ≤ (10794869957557/25000000000000 : ℝ)^6251 := by
    have hnat : (5312298273 : ℕ)^8299*25000000000000^6251 ≤ 10794869957557^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312298273 10000000000 10794869957557 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078755317/2000000000 : ℝ)^8299 ≤ (44060933178611/100000000000000 : ℝ)^6251 := by
    have hnat : (1078755317 : ℕ)^8299*100000000000000^6251 ≤ 44060933178611^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078755317 2000000000 44060933178611 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530194639/2500000000 : ℝ)^8299 ≤ (12759586969371/100000000000000 : ℝ)^6251 := by
    have hnat : (530194639 : ℕ)^8299*100000000000000^6251 ≤ 12759586969371^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530194639 2500000000 12759586969371 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312298273/10000000000 : ℝ), (1078755317/2000000000 : ℝ), (-530194639/2500000000 : ℝ)] ![(10794869957557/25000000000000 : ℝ), (44060933178611/100000000000000 : ℝ), (12759586969371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312298273/10000000000 : ℝ)|^8299 ≤ (10794869957557/25000000000000 : ℝ)^6251
        have hw : |(5312298273/10000000000 : ℝ)|=(5312298273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078755317/2000000000 : ℝ)|^8299 ≤ (44060933178611/100000000000000 : ℝ)^6251
        have hw : |(1078755317/2000000000 : ℝ)|=(1078755317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-530194639/2500000000 : ℝ)|^8299 ≤ (12759586969371/100000000000000 : ℝ)^6251
        have hw : |(-530194639/2500000000 : ℝ)|=(530194639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s6_7 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184879183/5000000000 : ℝ)*x 0 + (2249378107/5000000000 : ℝ)*x 1 + (4244492503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184879183/5000000000 : ℝ)^8299 ≤ (16658326212207/50000000000000 : ℝ)^6251 := by
    have hnat : (2184879183 : ℕ)^8299*50000000000000^6251 ≤ 16658326212207^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184879183 5000000000 16658326212207 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249378107/5000000000 : ℝ)^8299 ≤ (8657170888867/25000000000000 : ℝ)^6251 := by
    have hnat : (2249378107 : ℕ)^8299*25000000000000^6251 ≤ 8657170888867^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249378107 5000000000 8657170888867 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4244492503/10000000000 : ℝ)^8299 ≤ (32054664000961/100000000000000 : ℝ)^6251 := by
    have hnat : (4244492503 : ℕ)^8299*100000000000000^6251 ≤ 32054664000961^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244492503 10000000000 32054664000961 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184879183/5000000000 : ℝ), (2249378107/5000000000 : ℝ), (4244492503/10000000000 : ℝ)] ![(16658326212207/50000000000000 : ℝ), (8657170888867/25000000000000 : ℝ), (32054664000961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184879183/5000000000 : ℝ)|^8299 ≤ (16658326212207/50000000000000 : ℝ)^6251
        have hw : |(2184879183/5000000000 : ℝ)|=(2184879183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249378107/5000000000 : ℝ)|^8299 ≤ (8657170888867/25000000000000 : ℝ)^6251
        have hw : |(2249378107/5000000000 : ℝ)|=(2249378107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4244492503/10000000000 : ℝ)|^8299 ≤ (32054664000961/100000000000000 : ℝ)^6251
        have hw : |(4244492503/10000000000 : ℝ)|=(4244492503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1106_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11297/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14037/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7037/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11261/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7037/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11261/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7037/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11261/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7037/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11261/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7037/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11261/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7037/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11261/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11261/100000 : ℝ) ^ (4149/1024 : ℝ) ≤ (7181076218601271/50000000000000000000 : ℝ) := by
    have hpowers : (11261/100000 : ℝ)^4149 ≤ (7181076218601271/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11261 : ℕ)^4149*50000000000000000000^1024 ≤ 7181076218601271^1024*100000^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11261 100000 7181076218601271 50000000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11261/100000 : ℝ)) (X := (7181076218601271/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7037/50000 : ℝ) ^ (4149/1024 : ℝ) ≤ (7089639256966793/20000000000000000000 : ℝ) := by
    have hpowers : (7037/50000 : ℝ)^4149 ≤ (7089639256966793/20000000000000000000 : ℝ)^1024 := by
      have hnat : (7037 : ℕ)^4149*20000000000000000000^1024 ≤ 7089639256966793^1024*50000^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7037 50000 7089639256966793 20000000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7037/50000 : ℝ)) (X := (7089639256966793/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007181076218601271/25000000000000000000 : ℝ) ≤ (5000354428861237/5000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (25007181076218601271/25000000000000000000 : ℝ)^1024 ≤ (5000354428861237/5000000000000000 : ℝ)^4149 := by
      have hnat : (25007181076218601271 : ℕ)^1024*5000000000000000^4149 ≤ 5000354428861237^4149*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007181076218601271 25000000000000000000 5000354428861237 5000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000354428861237/5000000000000000 : ℝ)) (X := (25007181076218601271/25000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049810348722036507/100000000000000000000 : ℝ) ≤ (1250153640130139/1250000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (100049810348722036507/100000000000000000000 : ℝ)^1024 ≤ (1250153640130139/1250000000000000 : ℝ)^4149 := by
      have hnat : (100049810348722036507 : ℕ)^1024*1250000000000000^4149 ≤ 1250153640130139^4149*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049810348722036507 100000000000000000000 1250153640130139 1250000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250153640130139/1250000000000000 : ℝ)) (X := (100049810348722036507/100000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007089639256966793/10000000000000000000 : ℝ) ≤ (40006997537439/40000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (10007089639256966793/10000000000000000000 : ℝ)^1024 ≤ (40006997537439/40000000000000 : ℝ)^4149 := by
      have hnat : (10007089639256966793 : ℕ)^1024*40000000000000^4149 ≤ 40006997537439^4149*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007089639256966793 10000000000000000000 40006997537439 40000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40006997537439/40000000000000 : ℝ)) (X := (10007089639256966793/10000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7181076218601271/50000000000000000000 : ℝ) ≤ ((14060138323155477163/14065000000000000000 : ℝ)+2*(260131659319/140650000000000 : ℝ)*(11261/100000 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (14060138323155477163/14065000000000000000 : ℝ)+2*(260131659319/140650000000000 : ℝ)*(11261/100000 : ℝ)=(5000354428861237/5000000000000000 : ℝ) by norm_num, show 1+2*(7181076218601271/50000000000000000000 : ℝ)=(25007181076218601271/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7089639256966793/20000000000000000000 : ℝ)+(7181076218601271/50000000000000000000 : ℝ) ≤ ((14060138323155477163/14065000000000000000 : ℝ)+(260131659319/140650000000000 : ℝ)*((7037/50000 : ℝ)+(11261/100000 : ℝ)))^(4149/1024 : ℝ) := by
    rw [show (14060138323155477163/14065000000000000000 : ℝ)+(260131659319/140650000000000 : ℝ)*((7037/50000 : ℝ)+(11261/100000 : ℝ))=(1250153640130139/1250000000000000 : ℝ) by norm_num, show 1+(7089639256966793/20000000000000000000 : ℝ)+(7181076218601271/50000000000000000000 : ℝ)=(100049810348722036507/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7089639256966793/20000000000000000000 : ℝ) ≤ ((14060138323155477163/14065000000000000000 : ℝ)+2*(260131659319/140650000000000 : ℝ)*(7037/50000 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (14060138323155477163/14065000000000000000 : ℝ)+2*(260131659319/140650000000000 : ℝ)*(7037/50000 : ℝ)=(40006997537439/40000000000000 : ℝ) by norm_num, show 1+2*(7089639256966793/20000000000000000000 : ℝ)=(10007089639256966793/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14060138323155477163/14065000000000000000 : ℝ)*(X 1 0+X 2 0)+(260131659319/140650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (11261/100000 : ℝ)) (hi := (7037/50000 : ℝ)) (c := (14060138323155477163/14065000000000000000 : ℝ)) (alpha := (260131659319/140650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14060138323155477163/14065000000000000000 : ℝ)*(X 0 1+X 2 1)+(260131659319/140650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (11261/100000 : ℝ)) (hi := (7037/50000 : ℝ)) (c := (14060138323155477163/14065000000000000000 : ℝ)) (alpha := (260131659319/140650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14060138323155477163/14065000000000000000 : ℝ)*(X 0 2+X 1 2)+(260131659319/140650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (11261/100000 : ℝ)) (hi := (7037/50000 : ℝ)) (c := (14060138323155477163/14065000000000000000 : ℝ)) (alpha := (260131659319/140650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1092092633/5000000000 : ℝ)*X 0 0+(337131527/625000000 : ℝ)*X 0 1+(1316184299/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344985181/10000000000 : ℝ)*X 1 0+(-281227247/1250000000 : ℝ)*X 1 1+(1052947433/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336246303/2500000000 : ℝ)*X 2 0+(5264737163/10000000000 : ℝ)*X 2 1+(-2249817937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((436974841/1000000000 : ℝ)*X 0 0+(4243844757/10000000000 : ℝ)*X 0 1+(2249700781/5000000000 : ℝ)*X 0 2+(436974841/1000000000 : ℝ)*X 1 0+(4243844757/10000000000 : ℝ)*X 1 1+(2249700781/5000000000 : ℝ)*X 1 2+(436974841/1000000000 : ℝ)*X 2 0+(4243844757/10000000000 : ℝ)*X 2 1+(2249700781/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2184190317/10000000000 : ℝ)*X 0 0+(5265063869/10000000000 : ℝ)*X 0 1+(674222073/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656149137/5000000000 : ℝ)*X 1 0+(-530194639/2500000000 : ℝ)*X 1 1+(1078755317/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312298273/10000000000 : ℝ)*X 2 0+(1078755317/2000000000 : ℝ)*X 2 1+(-530194639/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2184879183/5000000000 : ℝ)*X 0 0+(2249378107/5000000000 : ℝ)*X 0 1+(4244492503/10000000000 : ℝ)*X 0 2+(2184879183/5000000000 : ℝ)*X 1 0+(2249378107/5000000000 : ℝ)*X 1 1+(4244492503/10000000000 : ℝ)*X 1 2+(2184879183/5000000000 : ℝ)*X 2 0+(2249378107/5000000000 : ℝ)*X 2 1+(4244492503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6203697674358427326459/1406500000000000000000000000 : ℝ) := by norm_num
    linear_combination (251931531/25000000000000 : ℝ)*(base19) + (61040197/6250000000000 : ℝ)*(base23) + (20288377/50000000000000 : ℝ)*(lower2) + (3127339/3125000000000 : ℝ)*(upper3) + (453641/400000000000 : ℝ)*(upper5) + (582151893908279/10000000000000 : ℝ)*(major0) + (582151893908279/10000000000000 : ℝ)*(major1) + (582151893908279/10000000000000 : ℝ)*(major2) + (1932489356365749/25000000000000 : ℝ)*(sp0) + (3864991892558911/50000000000000 : ℝ)*(sp1) + (3864991908100397/50000000000000 : ℝ)*(sp2) + (195651920689533/5000000000000 : ℝ)*(sp3) + (27367380951/100000000000000 : ℝ)*(sp4) + (7262253243/50000000000000 : ℝ)*(sp7) + (1956526469148573/50000000000000 : ℝ)*(f.failure) + (3864992396421973/50000000000000 : ℝ)*(f.sum) + (2570662066131/562600000000000000000000000 : ℝ)*base65 + (165909093946482477/140650000000000000000000000000000 : ℝ)*base67 + (3042318061904467523/140650000000000000000000000000000 : ℝ)*base70 + (452314738086467523/140650000000000000000000000000000 : ℝ)*base72 + (5332176738207/703250000000000000000000000 : ℝ)*base73 + (2595917921276032477/140650000000000000000000000000000 : ℝ)*base75 + (1935407124818632477/140650000000000000000000000000000 : ℝ)*base77 + (1380868145718667523/140650000000000000000000000000000 : ℝ)*base80 + (1076707919049/703250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (49695757/5000000000000000000000 : ℝ)*base90 + (49695757/5000000000000000000000 : ℝ)*base92 + (49695757/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4374050171246208246385119339/703250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14384603/1250000000000 : ℝ)*(base19) + (249721321/20000000000000 : ℝ)*(base23) + (31463443/25000000000000 : ℝ)*(upper3) + (22583303/50000000000000 : ℝ)*(lower4) + (63417787/50000000000000 : ℝ)*(upper5) + (5851081748030651/100000000000000 : ℝ)*(major0) + (5851081748030651/100000000000000 : ℝ)*(major1) + (5851081748030651/100000000000000 : ℝ)*(major2) + (31385193331/100000000000000 : ℝ)*(sp1) + (16852826941/50000000000000 : ℝ)*(sp2) + (3884619552091719/50000000000000 : ℝ)*(sp4) + (7769206568221867/100000000000000 : ℝ)*(sp5) + (971150518740369/12500000000000 : ℝ)*(sp6) + (1966462092276167/50000000000000 : ℝ)*(sp7) + (1966462092276167/50000000000000 : ℝ)*(f.failure) + (3884619552091719/50000000000000 : ℝ)*(f.sum) + (33474633291133/3516250000000000000000000000 : ℝ)*base66 + (12039413182215576887/1406500000000000000000000000000000 : ℝ)*base68 + (11657214664139576887/1406500000000000000000000000000000 : ℝ)*base70 + (689965113786923113/1406500000000000000000000000000000 : ℝ)*base71 + (84514658083791/7032500000000000000000000000 : ℝ)*base74 + (6050036613043423113/1406500000000000000000000000000000 : ℝ)*base75 + (8796693712784576887/1406500000000000000000000000000000 : ℝ)*base78 + (22827681783231576887/1406500000000000000000000000000000 : ℝ)*base80 + (13453720236151/7032500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (81205097/5000000000000000000000 : ℝ)*base89 + (81205097/5000000000000000000000 : ℝ)*base91 + (81205097/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1106_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14037/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1106_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1106_s7_0 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2184216357/10000000000 : ℝ)*x 0 + (5393721943/10000000000 : ℝ)*x 1 + (210603977/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184216357/10000000000 : ℝ)^8299 ≤ (13268770721871/100000000000000 : ℝ)^6251 := by
    have hnat : (2184216357 : ℕ)^8299*100000000000000^6251 ≤ 13268770721871^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184216357 10000000000 13268770721871 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393721943/10000000000 : ℝ)^8299 ≤ (2753771286059/6250000000000 : ℝ)^6251 := by
    have hnat : (5393721943 : ℕ)^8299*6250000000000^6251 ≤ 2753771286059^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393721943 10000000000 2753771286059 6250000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210603977/400000000 : ℝ)^8299 ≤ (8534177736603/20000000000000 : ℝ)^6251 := by
    have hnat : (210603977 : ℕ)^8299*20000000000000^6251 ≤ 8534177736603^6251*400000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210603977 400000000 8534177736603 20000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2184216357/10000000000 : ℝ), (5393721943/10000000000 : ℝ), (210603977/400000000 : ℝ)] ![(13268770721871/100000000000000 : ℝ), (2753771286059/6250000000000 : ℝ), (8534177736603/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2184216357/10000000000 : ℝ)|^8299 ≤ (13268770721871/100000000000000 : ℝ)^6251
        have hw : |(-2184216357/10000000000 : ℝ)|=(2184216357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393721943/10000000000 : ℝ)|^8299 ≤ (2753771286059/6250000000000 : ℝ)^6251
        have hw : |(5393721943/10000000000 : ℝ)|=(5393721943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210603977/400000000 : ℝ)|^8299 ≤ (8534177736603/20000000000000 : ℝ)^6251
        have hw : |(210603977/400000000 : ℝ)|=(210603977/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s7_1 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267244497/500000000 : ℝ)*x 0 + (-562366449/2500000000 : ℝ)*x 1 + (1316274857/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267244497/500000000 : ℝ)^8299 ≤ (43531537209621/100000000000000 : ℝ)^6251 := by
    have hnat : (267244497 : ℕ)^8299*100000000000000^6251 ≤ 43531537209621^6251*500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267244497 500000000 43531537209621 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562366449/2500000000 : ℝ)^8299 ≤ (689878703221/5000000000000 : ℝ)^6251 := by
    have hnat : (562366449 : ℕ)^8299*5000000000000^6251 ≤ 689878703221^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562366449 2500000000 689878703221 5000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316274857/2500000000 : ℝ)^8299 ≤ (21335444357647/50000000000000 : ℝ)^6251 := by
    have hnat : (1316274857 : ℕ)^8299*50000000000000^6251 ≤ 21335444357647^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316274857 2500000000 21335444357647 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267244497/500000000 : ℝ), (-562366449/2500000000 : ℝ), (1316274857/2500000000 : ℝ)] ![(43531537209621/100000000000000 : ℝ), (689878703221/5000000000000 : ℝ), (21335444357647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267244497/500000000 : ℝ)|^8299 ≤ (43531537209621/100000000000000 : ℝ)^6251
        have hw : |(267244497/500000000 : ℝ)|=(267244497/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-562366449/2500000000 : ℝ)|^8299 ≤ (689878703221/5000000000000 : ℝ)^6251
        have hw : |(-562366449/2500000000 : ℝ)|=(562366449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316274857/2500000000 : ℝ)|^8299 ≤ (21335444357647/50000000000000 : ℝ)^6251
        have hw : |(1316274857/2500000000 : ℝ)|=(1316274857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s7_2 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344889941/10000000000 : ℝ)*x 0 + (526509943/1000000000 : ℝ)*x 1 + (-35147903/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344889941/10000000000 : ℝ)^8299 ≤ (21765768610217/50000000000000 : ℝ)^6251 := by
    have hnat : (5344889941 : ℕ)^8299*50000000000000^6251 ≤ 21765768610217^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344889941 10000000000 21765768610217 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526509943/1000000000 : ℝ)^8299 ≤ (21335444368407/50000000000000 : ℝ)^6251 := by
    have hnat : (526509943 : ℕ)^8299*50000000000000^6251 ≤ 21335444368407^6251*1000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526509943 1000000000 21335444368407 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35147903/156250000 : ℝ)^8299 ≤ (13797574031847/100000000000000 : ℝ)^6251 := by
    have hnat : (35147903 : ℕ)^8299*100000000000000^6251 ≤ 13797574031847^6251*156250000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35147903 156250000 13797574031847 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344889941/10000000000 : ℝ), (526509943/1000000000 : ℝ), (-35147903/156250000 : ℝ)] ![(21765768610217/50000000000000 : ℝ), (21335444368407/50000000000000 : ℝ), (13797574031847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344889941/10000000000 : ℝ)|^8299 ≤ (21765768610217/50000000000000 : ℝ)^6251
        have hw : |(5344889941/10000000000 : ℝ)|=(5344889941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526509943/1000000000 : ℝ)|^8299 ≤ (21335444368407/50000000000000 : ℝ)^6251
        have hw : |(526509943/1000000000 : ℝ)|=(526509943/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-35147903/156250000 : ℝ)|^8299 ≤ (13797574031847/100000000000000 : ℝ)^6251
        have hw : |(-35147903/156250000 : ℝ)|=(35147903/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s7_3 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4369767379/10000000000 : ℝ)*x 0 + (4244577947/10000000000 : ℝ)*x 1 + (140583233/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369767379/10000000000 : ℝ)^8299 ≤ (2082296478559/6250000000000 : ℝ)^6251 := by
    have hnat : (4369767379 : ℕ)^8299*6250000000000^6251 ≤ 2082296478559^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369767379 10000000000 2082296478559 6250000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4244577947/10000000000 : ℝ)^8299 ≤ (32055520692993/100000000000000 : ℝ)^6251 := by
    have hnat : (4244577947 : ℕ)^8299*100000000000000^6251 ≤ 32055520692993^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244577947 10000000000 32055520692993 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140583233/312500000 : ℝ)^8299 ≤ (3462773563981/10000000000000 : ℝ)^6251 := by
    have hnat : (140583233 : ℕ)^8299*10000000000000^6251 ≤ 3462773563981^6251*312500000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140583233 312500000 3462773563981 10000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369767379/10000000000 : ℝ), (4244577947/10000000000 : ℝ), (140583233/312500000 : ℝ)] ![(2082296478559/6250000000000 : ℝ), (32055520692993/100000000000000 : ℝ), (3462773563981/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369767379/10000000000 : ℝ)|^8299 ≤ (2082296478559/6250000000000 : ℝ)^6251
        have hw : |(4369767379/10000000000 : ℝ)|=(4369767379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4244577947/10000000000 : ℝ)|^8299 ≤ (32055520692993/100000000000000 : ℝ)^6251
        have hw : |(4244577947/10000000000 : ℝ)|=(4244577947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140583233/312500000 : ℝ)|^8299 ≤ (3462773563981/10000000000000 : ℝ)^6251
        have hw : |(140583233/312500000 : ℝ)|=(140583233/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s7_4 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2184221343/10000000000 : ℝ)*x 0 + (658177797/1250000000 : ℝ)*x 1 + (2696698911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184221343/10000000000 : ℝ)^8299 ≤ (6634405467309/50000000000000 : ℝ)^6251 := by
    have hnat : (2184221343 : ℕ)^8299*50000000000000^6251 ≤ 6634405467309^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184221343 10000000000 6634405467309 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658177797/1250000000 : ℝ)^8299 ≤ (42674363583519/100000000000000 : ℝ)^6251 := by
    have hnat : (658177797 : ℕ)^8299*100000000000000^6251 ≤ 42674363583519^6251*1250000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658177797 1250000000 42674363583519 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696698911/5000000000 : ℝ)^8299 ≤ (44056825470697/100000000000000 : ℝ)^6251 := by
    have hnat : (2696698911 : ℕ)^8299*100000000000000^6251 ≤ 44056825470697^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696698911 5000000000 44056825470697 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2184221343/10000000000 : ℝ), (658177797/1250000000 : ℝ), (2696698911/5000000000 : ℝ)] ![(6634405467309/50000000000000 : ℝ), (42674363583519/100000000000000 : ℝ), (44056825470697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2184221343/10000000000 : ℝ)|^8299 ≤ (6634405467309/50000000000000 : ℝ)^6251
        have hw : |(-2184221343/10000000000 : ℝ)|=(2184221343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658177797/1250000000 : ℝ)|^8299 ≤ (42674363583519/100000000000000 : ℝ)^6251
        have hw : |(658177797/1250000000 : ℝ)|=(658177797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696698911/5000000000 : ℝ)|^8299 ≤ (44056825470697/100000000000000 : ℝ)^6251
        have hw : |(2696698911/5000000000 : ℝ)|=(2696698911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s7_5 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328097773/2500000000 : ℝ)*x 0 + (-1060583683/5000000000 : ℝ)*x 1 + (5393397851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328097773/2500000000 : ℝ)^8299 ≤ (21590240732449/50000000000000 : ℝ)^6251 := by
    have hnat : (1328097773 : ℕ)^8299*50000000000000^6251 ≤ 21590240732449^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328097773 2500000000 21590240732449 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060583683/5000000000 : ℝ)^8299 ≤ (398834147823/3125000000000 : ℝ)^6251 := by
    have hnat : (1060583683 : ℕ)^8299*3125000000000^6251 ≤ 398834147823^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060583683 5000000000 398834147823 3125000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393397851/10000000000 : ℝ)^8299 ≤ (110142064463/250000000000 : ℝ)^6251 := by
    have hnat : (5393397851 : ℕ)^8299*250000000000^6251 ≤ 110142064463^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393397851 10000000000 110142064463 250000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328097773/2500000000 : ℝ), (-1060583683/5000000000 : ℝ), (5393397851/10000000000 : ℝ)] ![(21590240732449/50000000000000 : ℝ), (398834147823/3125000000000 : ℝ), (110142064463/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328097773/2500000000 : ℝ)|^8299 ≤ (21590240732449/50000000000000 : ℝ)^6251
        have hw : |(1328097773/2500000000 : ℝ)|=(1328097773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1060583683/5000000000 : ℝ)|^8299 ≤ (398834147823/3125000000000 : ℝ)^6251
        have hw : |(-1060583683/5000000000 : ℝ)|=(1060583683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393397851/10000000000 : ℝ)|^8299 ≤ (110142064463/250000000000 : ℝ)^6251
        have hw : |(5393397851/10000000000 : ℝ)|=(5393397851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s7_6 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (332024441/625000000 : ℝ)*x 0 + (1078679571/2000000000 : ℝ)*x 1 + (-2121167409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332024441/625000000 : ℝ)^8299 ≤ (10795120269103/25000000000000 : ℝ)^6251 := by
    have hnat : (332024441 : ℕ)^8299*25000000000000^6251 ≤ 10795120269103^6251*625000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332024441 625000000 10795120269103 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078679571/2000000000 : ℝ)^8299 ≤ (44056825828579/100000000000000 : ℝ)^6251 := by
    have hnat : (1078679571 : ℕ)^8299*100000000000000^6251 ≤ 44056825828579^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078679571 2000000000 44056825828579 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121167409/10000000000 : ℝ)^8299 ≤ (398834158557/3125000000000 : ℝ)^6251 := by
    have hnat : (2121167409 : ℕ)^8299*3125000000000^6251 ≤ 398834158557^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121167409 10000000000 398834158557 3125000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332024441/625000000 : ℝ), (1078679571/2000000000 : ℝ), (-2121167409/10000000000 : ℝ)] ![(10795120269103/25000000000000 : ℝ), (44056825828579/100000000000000 : ℝ), (398834158557/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332024441/625000000 : ℝ)|^8299 ≤ (10795120269103/25000000000000 : ℝ)^6251
        have hw : |(332024441/625000000 : ℝ)|=(332024441/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078679571/2000000000 : ℝ)|^8299 ≤ (44056825828579/100000000000000 : ℝ)^6251
        have hw : |(1078679571/2000000000 : ℝ)|=(1078679571/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2121167409/10000000000 : ℝ)|^8299 ≤ (398834158557/3125000000000 : ℝ)^6251
        have hw : |(-2121167409/10000000000 : ℝ)|=(2121167409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s7_7 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4369777227/10000000000 : ℝ)*x 0 + (4498025553/10000000000 : ℝ)*x 1 + (4245218143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369777227/10000000000 : ℝ)^8299 ≤ (33316843341687/100000000000000 : ℝ)^6251 := by
    have hnat : (4369777227 : ℕ)^8299*100000000000000^6251 ≤ 33316843341687^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369777227 10000000000 33316843341687 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498025553/10000000000 : ℝ)^8299 ≤ (8655304233393/25000000000000 : ℝ)^6251 := by
    have hnat : (4498025553 : ℕ)^8299*25000000000000^6251 ≤ 8655304233393^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498025553 10000000000 8655304233393 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4245218143/10000000000 : ℝ)^8299 ≤ (32061939706273/100000000000000 : ℝ)^6251 := by
    have hnat : (4245218143 : ℕ)^8299*100000000000000^6251 ≤ 32061939706273^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4245218143 10000000000 32061939706273 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369777227/10000000000 : ℝ), (4498025553/10000000000 : ℝ), (4245218143/10000000000 : ℝ)] ![(33316843341687/100000000000000 : ℝ), (8655304233393/25000000000000 : ℝ), (32061939706273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369777227/10000000000 : ℝ)|^8299 ≤ (33316843341687/100000000000000 : ℝ)^6251
        have hw : |(4369777227/10000000000 : ℝ)|=(4369777227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498025553/10000000000 : ℝ)|^8299 ≤ (8655304233393/25000000000000 : ℝ)^6251
        have hw : |(4498025553/10000000000 : ℝ)|=(4498025553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4245218143/10000000000 : ℝ)|^8299 ≤ (32061939706273/100000000000000 : ℝ)^6251
        have hw : |(4245218143/10000000000 : ℝ)|=(4245218143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1106_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14037/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2261/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14029/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14037/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11297/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14037/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11297/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14037/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11297/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14037/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11297/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14037/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11297/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14037/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11297/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11297/100000 : ℝ) ^ (4149/1024 : ℝ) ≤ (14549094281281069/100000000000000000000 : ℝ) := by
    have hpowers : (11297/100000 : ℝ)^4149 ≤ (14549094281281069/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11297 : ℕ)^4149*100000000000000000000^1024 ≤ 14549094281281069^1024*100000^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11297 100000 14549094281281069 100000000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11297/100000 : ℝ)) (X := (14549094281281069/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14037/100000 : ℝ) ^ (4149/1024 : ℝ) ≤ (350721171193923/1000000000000000000 : ℝ) := by
    have hpowers : (14037/100000 : ℝ)^4149 ≤ (350721171193923/1000000000000000000 : ℝ)^1024 := by
      have hnat : (14037 : ℕ)^4149*1000000000000000000^1024 ≤ 350721171193923^1024*100000^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14037 100000 350721171193923 1000000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14037/100000 : ℝ)) (X := (350721171193923/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014549094281281069/50000000000000000000 : ℝ) ≤ (10000718083404513/10000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (50014549094281281069/50000000000000000000 : ℝ)^1024 ≤ (10000718083404513/10000000000000000 : ℝ)^4149 := by
      have hnat : (50014549094281281069 : ℕ)^1024*10000000000000000^4149 ≤ 10000718083404513^4149*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014549094281281069 50000000000000000000 10000718083404513 10000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000718083404513/10000000000000000 : ℝ)) (X := (50014549094281281069/50000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049621211400673369/100000000000000000000 : ℝ) ≤ (500061222737853/500000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (100049621211400673369/100000000000000000000 : ℝ)^1024 ≤ (500061222737853/500000000000000 : ℝ)^4149 := by
      have hnat : (100049621211400673369 : ℕ)^1024*500000000000000^4149 ≤ 500061222737853^4149*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049621211400673369 100000000000000000000 500061222737853 500000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500061222737853/500000000000000 : ℝ)) (X := (100049621211400673369/100000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (500350721171193923/500000000000000000 : ℝ) ≤ (10001730826109607/10000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (500350721171193923/500000000000000000 : ℝ)^1024 ≤ (10001730826109607/10000000000000000 : ℝ)^4149 := by
      have hnat : (500350721171193923 : ℕ)^1024*10000000000000000^4149 ≤ 10001730826109607^4149*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500350721171193923 500000000000000000 10001730826109607 10000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001730826109607/10000000000000000 : ℝ)) (X := (500350721171193923/500000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14549094281281069/100000000000000000000 : ℝ) ≤ ((13695263297094459351/13700000000000000000 : ℝ)+2*(506371352547/274000000000000 : ℝ)*(11297/100000 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (13695263297094459351/13700000000000000000 : ℝ)+2*(506371352547/274000000000000 : ℝ)*(11297/100000 : ℝ)=(10000718083404513/10000000000000000 : ℝ) by norm_num, show 1+2*(14549094281281069/100000000000000000000 : ℝ)=(50014549094281281069/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(350721171193923/1000000000000000000 : ℝ)+(14549094281281069/100000000000000000000 : ℝ) ≤ ((13695263297094459351/13700000000000000000 : ℝ)+(506371352547/274000000000000 : ℝ)*((14037/100000 : ℝ)+(11297/100000 : ℝ)))^(4149/1024 : ℝ) := by
    rw [show (13695263297094459351/13700000000000000000 : ℝ)+(506371352547/274000000000000 : ℝ)*((14037/100000 : ℝ)+(11297/100000 : ℝ))=(500061222737853/500000000000000 : ℝ) by norm_num, show 1+(350721171193923/1000000000000000000 : ℝ)+(14549094281281069/100000000000000000000 : ℝ)=(100049621211400673369/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(350721171193923/1000000000000000000 : ℝ) ≤ ((13695263297094459351/13700000000000000000 : ℝ)+2*(506371352547/274000000000000 : ℝ)*(14037/100000 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (13695263297094459351/13700000000000000000 : ℝ)+2*(506371352547/274000000000000 : ℝ)*(14037/100000 : ℝ)=(10001730826109607/10000000000000000 : ℝ) by norm_num, show 1+2*(350721171193923/1000000000000000000 : ℝ)=(500350721171193923/500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13695263297094459351/13700000000000000000 : ℝ)*(X 1 0+X 2 0)+(506371352547/274000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (11297/100000 : ℝ)) (hi := (14037/100000 : ℝ)) (c := (13695263297094459351/13700000000000000000 : ℝ)) (alpha := (506371352547/274000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13695263297094459351/13700000000000000000 : ℝ)*(X 0 1+X 2 1)+(506371352547/274000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (11297/100000 : ℝ)) (hi := (14037/100000 : ℝ)) (c := (13695263297094459351/13700000000000000000 : ℝ)) (alpha := (506371352547/274000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13695263297094459351/13700000000000000000 : ℝ)*(X 0 2+X 1 2)+(506371352547/274000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (11297/100000 : ℝ)) (hi := (14037/100000 : ℝ)) (c := (13695263297094459351/13700000000000000000 : ℝ)) (alpha := (506371352547/274000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2184216357/10000000000 : ℝ)*X 0 0+(5393721943/10000000000 : ℝ)*X 0 1+(210603977/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267244497/500000000 : ℝ)*X 1 0+(-562366449/2500000000 : ℝ)*X 1 1+(1316274857/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344889941/10000000000 : ℝ)*X 2 0+(526509943/1000000000 : ℝ)*X 2 1+(-35147903/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4369767379/10000000000 : ℝ)*X 0 0+(4244577947/10000000000 : ℝ)*X 0 1+(140583233/312500000 : ℝ)*X 0 2+(4369767379/10000000000 : ℝ)*X 1 0+(4244577947/10000000000 : ℝ)*X 1 1+(140583233/312500000 : ℝ)*X 1 2+(4369767379/10000000000 : ℝ)*X 2 0+(4244577947/10000000000 : ℝ)*X 2 1+(140583233/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2184221343/10000000000 : ℝ)*X 0 0+(658177797/1250000000 : ℝ)*X 0 1+(2696698911/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328097773/2500000000 : ℝ)*X 1 0+(-1060583683/5000000000 : ℝ)*X 1 1+(5393397851/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((332024441/625000000 : ℝ)*X 2 0+(1078679571/2000000000 : ℝ)*X 2 1+(-2121167409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4369777227/10000000000 : ℝ)*X 0 0+(4498025553/10000000000 : ℝ)*X 0 1+(4245218143/10000000000 : ℝ)*X 0 2+(4369777227/10000000000 : ℝ)*X 1 0+(4498025553/10000000000 : ℝ)*X 1 1+(4245218143/10000000000 : ℝ)*X 1 2+(4369777227/10000000000 : ℝ)*X 2 0+(4498025553/10000000000 : ℝ)*X 2 1+(4245218143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (70784521542590900221865463/34250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8472789/2000000000000 : ℝ)*(base19) + (401907361/100000000000000 : ℝ)*(base23) + (12393033/100000000000000 : ℝ)*(lower2) + (49576357/100000000000000 : ℝ)*(upper3) + (7794913/20000000000000 : ℝ)*(upper5) + (585520363032029/10000000000000 : ℝ)*(major0) + (585520363032029/10000000000000 : ℝ)*(major1) + (585520363032029/10000000000000 : ℝ)*(major2) + (7774700447547607/100000000000000 : ℝ)*(sp0) + (7774711976132471/100000000000000 : ℝ)*(sp1) + (97183899973307/1250000000000 : ℝ)*(sp2) + (983922167730771/25000000000000 : ℝ)*(sp3) + (5976112157/50000000000000 : ℝ)*(sp4) + (3060527759/50000000000000 : ℝ)*(sp7) + (1967847395989301/50000000000000 : ℝ)*(f.failure) + (7774712399771921/100000000000000 : ℝ)*(f.sum) + (3402809180907/1370000000000000000000000000 : ℝ)*base66 + (4645610735265703179/137000000000000000000000000000000 : ℝ)*base67 + (2382989839087703179/137000000000000000000000000000000 : ℝ)*base69 + (2557561308050703179/137000000000000000000000000000000 : ℝ)*base71 + (6785340950043/1370000000000000000000000000 : ℝ)*base73 + (529007702097296821/137000000000000000000000000000000 : ℝ)*base76 + (1753487864910703179/137000000000000000000000000000000 : ℝ)*base77 + (1665407219370703179/137000000000000000000000000000000 : ℝ)*base79 + (7512707577597/1370000000000000000000000000 : ℝ)*base82 + (26608091/5000000000000000000000 : ℝ)*base89 + (26608091/5000000000000000000000 : ℝ)*base91 + (26608091/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22276893211712315529363/3425000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60510313/5000000000000 : ℝ)*(base19) + (623217961/50000000000000 : ℝ)*(base23) + (159669863/100000000000000 : ℝ)*(upper3) + (8817087/20000000000000 : ℝ)*(lower4) + (58274499/50000000000000 : ℝ)*(upper5) + (1471196960426669/25000000000000 : ℝ)*(major0) + (1471196960426669/25000000000000 : ℝ)*(major1) + (1471196960426669/25000000000000 : ℝ)*(major2) + (6554789851/20000000000000 : ℝ)*(sp1) + (4223341633/12500000000000 : ℝ)*(sp2) + (7813995042286321/100000000000000 : ℝ)*(sp4) + (3906980529065403/50000000000000 : ℝ)*(sp5) + (1562792001823467/20000000000000 : ℝ)*(sp6) + (3955580424320277/100000000000000 : ℝ)*(sp7) + (3955580424320277/100000000000000 : ℝ)*(f.failure) + (7813995042286321/100000000000000 : ℝ)*(f.sum) + (11978283868143/3425000000000000000000000000 : ℝ)*base65 + (518582217738518181/342500000000000000000000000000000 : ℝ)*base68 + (1306661385631481819/342500000000000000000000000000000 : ℝ)*base69 + (2495851792733518181/342500000000000000000000000000000 : ℝ)*base72 + (3506708049409/1712500000000000000000000000 : ℝ)*base73 + (8370028205111481819/342500000000000000000000000000000 : ℝ)*base75 + (1416665162943518181/342500000000000000000000000000000 : ℝ)*base78 + (2540370479478981819/342500000000000000000000000000000 : ℝ)*base79 + (11782643991043/3425000000000000000000000000 : ℝ)*base81 + (33093893/10000000000000000000000 : ℝ)*base90 + (33093893/10000000000000000000000 : ℝ)*base92 + (33093893/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1106_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14037/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1106_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1106_s8_0 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2184222363/10000000000 : ℝ)*x 0 + (5393639507/10000000000 : ℝ)*x 1 + (5265178013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184222363/10000000000 : ℝ)^8299 ≤ (414650598783/3125000000000 : ℝ)^6251 := by
    have hnat : (2184222363 : ℕ)^8299*3125000000000^6251 ≤ 414650598783^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184222363 10000000000 414650598783 3125000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393639507/10000000000 : ℝ)^8299 ≤ (110148616371/250000000000 : ℝ)^6251 := by
    have hnat : (5393639507 : ℕ)^8299*250000000000^6251 ≤ 110148616371^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393639507 10000000000 110148616371 250000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265178013/10000000000 : ℝ)^8299 ≤ (170686937083/400000000000 : ℝ)^6251 := by
    have hnat : (5265178013 : ℕ)^8299*400000000000^6251 ≤ 170686937083^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265178013 10000000000 170686937083 400000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2184222363/10000000000 : ℝ), (5393639507/10000000000 : ℝ), (5265178013/10000000000 : ℝ)] ![(414650598783/3125000000000 : ℝ), (110148616371/250000000000 : ℝ), (170686937083/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2184222363/10000000000 : ℝ)|^8299 ≤ (414650598783/3125000000000 : ℝ)^6251
        have hw : |(-2184222363/10000000000 : ℝ)|=(2184222363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393639507/10000000000 : ℝ)|^8299 ≤ (110148616371/250000000000 : ℝ)^6251
        have hw : |(5393639507/10000000000 : ℝ)|=(5393639507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265178013/10000000000 : ℝ)|^8299 ≤ (170686937083/400000000000 : ℝ)^6251
        have hw : |(5265178013/10000000000 : ℝ)|=(5265178013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s8_1 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336217407/2500000000 : ℝ)*x 0 + (-44987779/200000000 : ℝ)*x 1 + (5265177999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336217407/2500000000 : ℝ)^8299 ≤ (43531317578479/100000000000000 : ℝ)^6251 := by
    have hnat : (1336217407 : ℕ)^8299*100000000000000^6251 ≤ 43531317578479^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336217407 2500000000 43531317578479 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44987779/200000000 : ℝ)^8299 ≤ (3449237072271/25000000000000 : ℝ)^6251 := by
    have hnat : (44987779 : ℕ)^8299*25000000000000^6251 ≤ 3449237072271^6251*200000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44987779 200000000 3449237072271 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265177999/10000000000 : ℝ)^8299 ≤ (42671734120113/100000000000000 : ℝ)^6251 := by
    have hnat : (5265177999 : ℕ)^8299*100000000000000^6251 ≤ 42671734120113^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265177999 10000000000 42671734120113 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336217407/2500000000 : ℝ), (-44987779/200000000 : ℝ), (5265177999/10000000000 : ℝ)] ![(43531317578479/100000000000000 : ℝ), (3449237072271/25000000000000 : ℝ), (42671734120113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336217407/2500000000 : ℝ)|^8299 ≤ (43531317578479/100000000000000 : ℝ)^6251
        have hw : |(1336217407/2500000000 : ℝ)|=(1336217407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44987779/200000000 : ℝ)|^8299 ≤ (3449237072271/25000000000000 : ℝ)^6251
        have hw : |(-44987779/200000000 : ℝ)|=(44987779/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265177999/10000000000 : ℝ)|^8299 ≤ (42671734120113/100000000000000 : ℝ)^6251
        have hw : |(5265177999/10000000000 : ℝ)|=(5265177999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s8_2 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344869747/10000000000 : ℝ)*x 0 + (1316294459/2500000000 : ℝ)*x 1 + (-140586813/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344869747/10000000000 : ℝ)^8299 ≤ (4353131886521/10000000000000 : ℝ)^6251 := by
    have hnat : (5344869747 : ℕ)^8299*10000000000000^6251 ≤ 4353131886521^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344869747 10000000000 4353131886521 10000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316294459/2500000000 : ℝ)^8299 ≤ (10667933091567/25000000000000 : ℝ)^6251 := by
    have hnat : (1316294459 : ℕ)^8299*25000000000000^6251 ≤ 10667933091567^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316294459 2500000000 10667933091567 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140586813/625000000 : ℝ)^8299 ≤ (1379694876139/10000000000000 : ℝ)^6251 := by
    have hnat : (140586813 : ℕ)^8299*10000000000000^6251 ≤ 1379694876139^6251*625000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140586813 625000000 1379694876139 10000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344869747/10000000000 : ℝ), (1316294459/2500000000 : ℝ), (-140586813/625000000 : ℝ)] ![(4353131886521/10000000000000 : ℝ), (10667933091567/25000000000000 : ℝ), (1379694876139/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344869747/10000000000 : ℝ)|^8299 ≤ (4353131886521/10000000000000 : ℝ)^6251
        have hw : |(5344869747/10000000000 : ℝ)|=(5344869747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316294459/2500000000 : ℝ)|^8299 ≤ (10667933091567/25000000000000 : ℝ)^6251
        have hw : |(1316294459/2500000000 : ℝ)|=(1316294459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-140586813/625000000 : ℝ)|^8299 ≤ (1379694876139/10000000000000 : ℝ)^6251
        have hw : |(-140586813/625000000 : ℝ)|=(140586813/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s8_3 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1092442863/2500000000 : ℝ)*x 0 + (4244736453/10000000000 : ℝ)*x 1 + (140578247/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092442863/2500000000 : ℝ)^8299 ≤ (33316784885201/100000000000000 : ℝ)^6251 := by
    have hnat : (1092442863 : ℕ)^8299*100000000000000^6251 ≤ 33316784885201^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092442863 2500000000 33316784885201 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4244736453/10000000000 : ℝ)^8299 ≤ (8014277486417/25000000000000 : ℝ)^6251 := by
    have hnat : (4244736453 : ℕ)^8299*25000000000000^6251 ≤ 8014277486417^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244736453 10000000000 8014277486417 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140578247/312500000 : ℝ)^8299 ≤ (34626105155653/100000000000000 : ℝ)^6251 := by
    have hnat : (140578247 : ℕ)^8299*100000000000000^6251 ≤ 34626105155653^6251*312500000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140578247 312500000 34626105155653 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092442863/2500000000 : ℝ), (4244736453/10000000000 : ℝ), (140578247/312500000 : ℝ)] ![(33316784885201/100000000000000 : ℝ), (8014277486417/25000000000000 : ℝ), (34626105155653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092442863/2500000000 : ℝ)|^8299 ≤ (33316784885201/100000000000000 : ℝ)^6251
        have hw : |(1092442863/2500000000 : ℝ)|=(1092442863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4244736453/10000000000 : ℝ)|^8299 ≤ (8014277486417/25000000000000 : ℝ)^6251
        have hw : |(4244736453/10000000000 : ℝ)|=(4244736453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140578247/312500000 : ℝ)|^8299 ≤ (34626105155653/100000000000000 : ℝ)^6251
        have hw : |(140578247/312500000 : ℝ)|=(140578247/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s8_4 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2184227803/10000000000 : ℝ)*x 0 + (5265500269/10000000000 : ℝ)*x 1 + (2696657867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184227803/10000000000 : ℝ)^8299 ≤ (13268863035413/100000000000000 : ℝ)^6251 := by
    have hnat : (2184227803 : ℕ)^8299*100000000000000^6251 ≤ 13268863035413^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184227803 10000000000 13268863035413 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265500269/10000000000 : ℝ)^8299 ≤ (1333600053439/3125000000000 : ℝ)^6251 := by
    have hnat : (5265500269 : ℕ)^8299*3125000000000^6251 ≤ 1333600053439^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265500269 10000000000 1333600053439 3125000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696657867/5000000000 : ℝ)^8299 ≤ (22027967616887/50000000000000 : ℝ)^6251 := by
    have hnat : (2696657867 : ℕ)^8299*50000000000000^6251 ≤ 22027967616887^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696657867 5000000000 22027967616887 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2184227803/10000000000 : ℝ), (5265500269/10000000000 : ℝ), (2696657867/5000000000 : ℝ)] ![(13268863035413/100000000000000 : ℝ), (1333600053439/3125000000000 : ℝ), (22027967616887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2184227803/10000000000 : ℝ)|^8299 ≤ (13268863035413/100000000000000 : ℝ)^6251
        have hw : |(-2184227803/10000000000 : ℝ)|=(2184227803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265500269/10000000000 : ℝ)|^8299 ≤ (1333600053439/3125000000000 : ℝ)^6251
        have hw : |(5265500269/10000000000 : ℝ)|=(5265500269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696657867/5000000000 : ℝ)|^8299 ≤ (22027967616887/50000000000000 : ℝ)^6251
        have hw : |(2696657867/5000000000 : ℝ)|=(2696657867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s8_5 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656205771/5000000000 : ℝ)*x 0 + (-212125059/1000000000 : ℝ)*x 1 + (5393316201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656205771/5000000000 : ℝ)^8299 ≤ (10795175536773/25000000000000 : ℝ)^6251 := by
    have hnat : (2656205771 : ℕ)^8299*25000000000000^6251 ≤ 10795175536773^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656205771 5000000000 10795175536773 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212125059/1000000000 : ℝ)^8299 ≤ (12763357536471/100000000000000 : ℝ)^6251 := by
    have hnat : (212125059 : ℕ)^8299*100000000000000^6251 ≤ 12763357536471^6251*1000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212125059 1000000000 12763357536471 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393316201/10000000000 : ℝ)^8299 ≤ (22027970149167/50000000000000 : ℝ)^6251 := by
    have hnat : (5393316201 : ℕ)^8299*50000000000000^6251 ≤ 22027970149167^6251*10000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393316201 10000000000 22027970149167 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656205771/5000000000 : ℝ), (-212125059/1000000000 : ℝ), (5393316201/10000000000 : ℝ)] ![(10795175536773/25000000000000 : ℝ), (12763357536471/100000000000000 : ℝ), (22027970149167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656205771/5000000000 : ℝ)|^8299 ≤ (10795175536773/25000000000000 : ℝ)^6251
        have hw : |(2656205771/5000000000 : ℝ)|=(2656205771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212125059/1000000000 : ℝ)|^8299 ≤ (12763357536471/100000000000000 : ℝ)^6251
        have hw : |(-212125059/1000000000 : ℝ)|=(212125059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393316201/10000000000 : ℝ)|^8299 ≤ (22027970149167/50000000000000 : ℝ)^6251
        have hw : |(5393316201/10000000000 : ℝ)|=(5393316201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s8_6 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656205621/5000000000 : ℝ)*x 0 + (1348329121/2500000000 : ℝ)*x 1 + (-530312653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656205621/5000000000 : ℝ)^8299 ≤ (21590349454849/50000000000000 : ℝ)^6251 := by
    have hnat : (2656205621 : ℕ)^8299*50000000000000^6251 ≤ 21590349454849^6251*5000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656205621 5000000000 21590349454849 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348329121/2500000000 : ℝ)^8299 ≤ (11013985841859/25000000000000 : ℝ)^6251 := by
    have hnat : (1348329121 : ℕ)^8299*25000000000000^6251 ≤ 11013985841859^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348329121 2500000000 11013985841859 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530312653/2500000000 : ℝ)^8299 ≤ (3190839428053/25000000000000 : ℝ)^6251 := by
    have hnat : (530312653 : ℕ)^8299*25000000000000^6251 ≤ 3190839428053^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530312653 2500000000 3190839428053 25000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656205621/5000000000 : ℝ), (1348329121/2500000000 : ℝ), (-530312653/2500000000 : ℝ)] ![(21590349454849/50000000000000 : ℝ), (11013985841859/25000000000000 : ℝ), (3190839428053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656205621/5000000000 : ℝ)|^8299 ≤ (21590349454849/50000000000000 : ℝ)^6251
        have hw : |(2656205621/5000000000 : ℝ)|=(2656205621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348329121/2500000000 : ℝ)|^8299 ≤ (11013985841859/25000000000000 : ℝ)^6251
        have hw : |(1348329121/2500000000 : ℝ)|=(1348329121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-530312653/2500000000 : ℝ)|^8299 ≤ (3190839428053/25000000000000 : ℝ)^6251
        have hw : |(-530312653/2500000000 : ℝ)|=(530312653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1106_s8_7 (p : ℝ) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1092445373/2500000000 : ℝ)*x 0 + (899573473/2000000000 : ℝ)*x 1 + (84907501/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092445373/2500000000 : ℝ)^8299 ≤ (4164610814183/12500000000000 : ℝ)^6251 := by
    have hnat : (1092445373 : ℕ)^8299*12500000000000^6251 ≤ 4164610814183^6251*2500000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092445373 2500000000 4164610814183 12500000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899573473/2000000000 : ℝ)^8299 ≤ (17309800231673/50000000000000 : ℝ)^6251 := by
    have hnat : (899573473 : ℕ)^8299*50000000000000^6251 ≤ 17309800231673^6251*2000000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899573473 2000000000 17309800231673 50000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84907501/200000000 : ℝ)^8299 ≤ (32063513004291/100000000000000 : ℝ)^6251 := by
    have hnat : (84907501 : ℕ)^8299*100000000000000^6251 ≤ 32063513004291^6251*200000000^8299 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84907501 200000000 32063513004291 100000000000000 8299 6251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8299/2048 : ℝ)) 8299 6251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092445373/2500000000 : ℝ), (899573473/2000000000 : ℝ), (84907501/200000000 : ℝ)] ![(4164610814183/12500000000000 : ℝ), (17309800231673/50000000000000 : ℝ), (32063513004291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092445373/2500000000 : ℝ)|^8299 ≤ (4164610814183/12500000000000 : ℝ)^6251
        have hw : |(1092445373/2500000000 : ℝ)|=(1092445373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899573473/2000000000 : ℝ)|^8299 ≤ (17309800231673/50000000000000 : ℝ)^6251
        have hw : |(899573473/2000000000 : ℝ)|=(899573473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84907501/200000000 : ℝ)|^8299 ≤ (32063513004291/100000000000000 : ℝ)^6251
        have hw : |(84907501/200000000 : ℝ)|=(84907501/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1106_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5653/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14027/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14029/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2261/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14029/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2261/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14029/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2261/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14029/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2261/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14029/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2261/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14029/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2261/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2261/20000 : ℝ) ^ (4149/1024 : ℝ) ≤ (14590884586925517/100000000000000000000 : ℝ) := by
    have hpowers : (2261/20000 : ℝ)^4149 ≤ (14590884586925517/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2261 : ℕ)^4149*100000000000000000000^1024 ≤ 14590884586925517^1024*20000^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2261 20000 14590884586925517 100000000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2261/20000 : ℝ)) (X := (14590884586925517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14029/100000 : ℝ) ^ (4149/1024 : ℝ) ≤ (17495599716728321/50000000000000000000 : ℝ) := by
    have hpowers : (14029/100000 : ℝ)^4149 ≤ (17495599716728321/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14029 : ℕ)^4149*50000000000000000000^1024 ≤ 17495599716728321^1024*100000^4149 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14029 100000 17495599716728321 50000000000000000000 4149 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14029/100000 : ℝ)) (X := (17495599716728321/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014590884586925517/50000000000000000000 : ℝ) ≤ (5000360072887677/5000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (50014590884586925517/50000000000000000000 : ℝ)^1024 ≤ (5000360072887677/5000000000000000 : ℝ)^4149 := by
      have hnat : (50014590884586925517 : ℕ)^1024*5000000000000000^4149 ≤ 5000360072887677^4149*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014590884586925517 50000000000000000000 5000360072887677 5000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000360072887677/5000000000000000 : ℝ)) (X := (50014590884586925517/50000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049582084020382159/100000000000000000000 : ℝ) ≤ (5000611744714331/5000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (100049582084020382159/100000000000000000000 : ℝ)^1024 ≤ (5000611744714331/5000000000000000 : ℝ)^4149 := by
      have hnat : (100049582084020382159 : ℕ)^1024*5000000000000000^4149 ≤ 5000611744714331^4149*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049582084020382159 100000000000000000000 5000611744714331 5000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000611744714331/5000000000000000 : ℝ)) (X := (100049582084020382159/100000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017495599716728321/25000000000000000000 : ℝ) ≤ (1000172683308197/1000000000000000 : ℝ) ^ (4149/1024 : ℝ) := by
    have hpowers : (25017495599716728321/25000000000000000000 : ℝ)^1024 ≤ (1000172683308197/1000000000000000 : ℝ)^4149 := by
      have hnat : (25017495599716728321 : ℕ)^1024*1000000000000000^4149 ≤ 1000172683308197^4149*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017495599716728321 25000000000000000000 1000172683308197 1000000000000000 1024 4149 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000172683308197/1000000000000000 : ℝ)) (X := (25017495599716728321/25000000000000000000 : ℝ)) (by norm_num) 4149 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14590884586925517/100000000000000000000 : ℝ) ≤ ((1701911317318173151/1702500000000000000 : ℝ)+2*(125835913327/68100000000000 : ℝ)*(2261/20000 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (1701911317318173151/1702500000000000000 : ℝ)+2*(125835913327/68100000000000 : ℝ)*(2261/20000 : ℝ)=(5000360072887677/5000000000000000 : ℝ) by norm_num, show 1+2*(14590884586925517/100000000000000000000 : ℝ)=(50014590884586925517/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17495599716728321/50000000000000000000 : ℝ)+(14590884586925517/100000000000000000000 : ℝ) ≤ ((1701911317318173151/1702500000000000000 : ℝ)+(125835913327/68100000000000 : ℝ)*((14029/100000 : ℝ)+(2261/20000 : ℝ)))^(4149/1024 : ℝ) := by
    rw [show (1701911317318173151/1702500000000000000 : ℝ)+(125835913327/68100000000000 : ℝ)*((14029/100000 : ℝ)+(2261/20000 : ℝ))=(5000611744714331/5000000000000000 : ℝ) by norm_num, show 1+(17495599716728321/50000000000000000000 : ℝ)+(14590884586925517/100000000000000000000 : ℝ)=(100049582084020382159/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17495599716728321/50000000000000000000 : ℝ) ≤ ((1701911317318173151/1702500000000000000 : ℝ)+2*(125835913327/68100000000000 : ℝ)*(14029/100000 : ℝ))^(4149/1024 : ℝ) := by
    rw [show (1701911317318173151/1702500000000000000 : ℝ)+2*(125835913327/68100000000000 : ℝ)*(14029/100000 : ℝ)=(1000172683308197/1000000000000000 : ℝ) by norm_num, show 1+2*(17495599716728321/50000000000000000000 : ℝ)=(25017495599716728321/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1701911317318173151/1702500000000000000 : ℝ)*(X 1 0+X 2 0)+(125835913327/68100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (2261/20000 : ℝ)) (hi := (14029/100000 : ℝ)) (c := (1701911317318173151/1702500000000000000 : ℝ)) (alpha := (125835913327/68100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1701911317318173151/1702500000000000000 : ℝ)*(X 0 1+X 2 1)+(125835913327/68100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (2261/20000 : ℝ)) (hi := (14029/100000 : ℝ)) (c := (1701911317318173151/1702500000000000000 : ℝ)) (alpha := (125835913327/68100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1701911317318173151/1702500000000000000 : ℝ)*(X 0 2+X 1 2)+(125835913327/68100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4149/1024 : ℝ)) (lo := (2261/20000 : ℝ)) (hi := (14029/100000 : ℝ)) (c := (1701911317318173151/1702500000000000000 : ℝ)) (alpha := (125835913327/68100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2184222363/10000000000 : ℝ)*X 0 0+(5393639507/10000000000 : ℝ)*X 0 1+(5265178013/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336217407/2500000000 : ℝ)*X 1 0+(-44987779/200000000 : ℝ)*X 1 1+(5265177999/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344869747/10000000000 : ℝ)*X 2 0+(1316294459/2500000000 : ℝ)*X 2 1+(-140586813/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1092442863/2500000000 : ℝ)*X 0 0+(4244736453/10000000000 : ℝ)*X 0 1+(140578247/312500000 : ℝ)*X 0 2+(1092442863/2500000000 : ℝ)*X 1 0+(4244736453/10000000000 : ℝ)*X 1 1+(140578247/312500000 : ℝ)*X 1 2+(1092442863/2500000000 : ℝ)*X 2 0+(4244736453/10000000000 : ℝ)*X 2 1+(140578247/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2184227803/10000000000 : ℝ)*X 0 0+(5265500269/10000000000 : ℝ)*X 0 1+(2696657867/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656205771/5000000000 : ℝ)*X 1 0+(-212125059/1000000000 : ℝ)*X 1 1+(5393316201/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656205621/5000000000 : ℝ)*X 2 0+(1348329121/2500000000 : ℝ)*X 2 1+(-530312653/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1092445373/2500000000 : ℝ)*X 0 0+(899573473/2000000000 : ℝ)*X 0 1+(84907501/200000000 : ℝ)*X 0 2+(1092445373/2500000000 : ℝ)*X 1 0+(899573473/2000000000 : ℝ)*X 1 1+(84907501/200000000 : ℝ)*X 1 2+(1092445373/2500000000 : ℝ)*X 2 0+(899573473/2000000000 : ℝ)*X 2 1+(84907501/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1106_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (224549942355305352489/28375000000000000000000000 : ℝ) := by norm_num
    linear_combination (331018299/20000000000000 : ℝ)*(base19) + (353883677/20000000000000 : ℝ)*(base23) + (31529569/100000000000000 : ℝ)*(lower2) + (43168583/20000000000000 : ℝ)*(upper3) + (11275561/10000000000000 : ℝ)*(upper5) + (586259214945261/10000000000000 : ℝ)*(major0) + (586259214945261/10000000000000 : ℝ)*(major1) + (586259214945261/10000000000000 : ℝ)*(major2) + (1946119859190593/25000000000000 : ℝ)*(sp0) + (7784521243901249/100000000000000 : ℝ)*(sp1) + (3892260564787179/50000000000000 : ℝ)*(sp2) + (39406367053747/1000000000000 : ℝ)*(sp3) + (10865557593/25000000000000 : ℝ)*(sp4) + (24430749291/100000000000000 : ℝ)*(sp7) + (492582642015499/12500000000000 : ℝ)*(f.failure) + (7784522898992743/100000000000000 : ℝ)*(f.sum) + (646273493379/113500000000000000000000000 : ℝ)*base65 + (9031969053370863/5675000000000000000000000000000 : ℝ)*base68 + (22271953794904137/5675000000000000000000000000000 : ℝ)*base69 + (1889550009345863/5675000000000000000000000000000 : ℝ)*base72 + (422297099243/227000000000000000000000000 : ℝ)*base73 + (1353189625320863/5675000000000000000000000000000 : ℝ)*base76 + (14852936834204137/5675000000000000000000000000000 : ℝ)*base77 + (42273841050829137/5675000000000000000000000000000 : ℝ)*base79 + (60231808947/28375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (10988709/1250000000000000000000 : ℝ)*base89 + (10988709/1250000000000000000000 : ℝ)*base91 + (10988709/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32770758938995775763/28375000000000000000000000 : ℝ) := by norm_num
    linear_combination (1313046837/100000000000000 : ℝ)*(base19) + (197718847/12500000000000 : ℝ)*(base23) + (535790193/100000000000000 : ℝ)*(lower1) + (297569257/100000000000000 : ℝ)*(upper2) + (17378247/4000000000000 : ℝ)*(upper3) + (6250581/6250000000000 : ℝ)*(upper5) + (294605167392021/5000000000000 : ℝ)*(major0) + (294605167392021/5000000000000 : ℝ)*(major1) + (294605167392021/5000000000000 : ℝ)*(major2) + (3076564793/12500000000000 : ℝ)*(sp2) + (1564741793179443/20000000000000 : ℝ)*(sp4) + (3911853826425189/50000000000000 : ℝ)*(sp5) + (122245043306689/1562500000000 : ℝ)*(sp6) + (1980248845643197/50000000000000 : ℝ)*(sp7) + (1980248845643197/50000000000000 : ℝ)*(f.failure) + (1564741793179443/20000000000000 : ℝ)*(f.sum) + (32633849517/9080000000000000000000000 : ℝ)*base66 + (3125308131686443/2837500000000000000000000000000 : ℝ)*base68 + (19793838051376057/2837500000000000000000000000000 : ℝ)*base69 + (29650825855848943/2837500000000000000000000000000 : ℝ)*base72 + (886254094913/113500000000000000000000000 : ℝ)*base73 + (24305198687176057/2837500000000000000000000000000 : ℝ)*base75 + (37809578487698943/2837500000000000000000000000000 : ℝ)*base78 + (16062697651426057/2837500000000000000000000000000 : ℝ)*base79 + (65591727083/28375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (35344173/5000000000000000000000 : ℝ)*base90 + (35344173/5000000000000000000000 : ℝ)*base92 + (35344173/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1106_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5653/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1106_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1106_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5653/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1106_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1106_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1106_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4149/1024 : ℝ) ≤ p) (hpb : p ≤ (8299/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148771791/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5653/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14027/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1106_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

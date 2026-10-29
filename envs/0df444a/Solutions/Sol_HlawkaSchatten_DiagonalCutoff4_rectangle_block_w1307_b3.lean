-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1307_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:38:37.790406+00:00
-- url     : https://prove2.me/submissions/b5fd9799-e15a-475b-9c12-dab61d43c11e

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
theorem support_rectangle_w1307_box_0 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-952254363/5000000000 : ℝ)*x 0 + (5391394661/10000000000 : ℝ)*x 1 + (2695697329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (952254363/5000000000 : ℝ)^4267 ≤ (5640782970617/50000000000000 : ℝ)^3243 := by
    have hnat : (952254363 : ℕ)^4267*50000000000000^3243 ≤ 5640782970617^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952254363 5000000000 5640782970617 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391394661/10000000000 : ℝ)^4267 ≤ (22179608520149/50000000000000 : ℝ)^3243 := by
    have hnat : (5391394661 : ℕ)^4267*50000000000000^3243 ≤ 22179608520149^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391394661 10000000000 22179608520149 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695697329/5000000000 : ℝ)^4267 ≤ (2217960850391/5000000000000 : ℝ)^3243 := by
    have hnat : (2695697329 : ℕ)^4267*5000000000000^3243 ≤ 2217960850391^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695697329 5000000000 2217960850391 5000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-952254363/5000000000 : ℝ), (5391394661/10000000000 : ℝ), (2695697329/5000000000 : ℝ)] ![(5640782970617/50000000000000 : ℝ), (22179608520149/50000000000000 : ℝ), (2217960850391/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-952254363/5000000000 : ℝ)|^4267 ≤ (5640782970617/50000000000000 : ℝ)^3243
        have hw : |(-952254363/5000000000 : ℝ)|=(952254363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391394661/10000000000 : ℝ)|^4267 ≤ (22179608520149/50000000000000 : ℝ)^3243
        have hw : |(5391394661/10000000000 : ℝ)|=(5391394661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695697329/5000000000 : ℝ)|^4267 ≤ (2217960850391/5000000000000 : ℝ)^3243
        have hw : |(2695697329/5000000000 : ℝ)|=(2695697329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_box_1 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42277059/80000000 : ℝ)*x 0 + (-2050594881/10000000000 : ℝ)*x 1 + (2695697251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42277059/80000000 : ℝ)^4267 ≤ (43207063887219/100000000000000 : ℝ)^3243 := by
    have hnat : (42277059 : ℕ)^4267*100000000000000^3243 ≤ 43207063887219^3243*80000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42277059 80000000 43207063887219 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2050594881/10000000000 : ℝ)^4267 ≤ (2486744155541/20000000000000 : ℝ)^3243 := by
    have hnat : (2050594881 : ℕ)^4267*20000000000000^3243 ≤ 2486744155541^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050594881 10000000000 2486744155541 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695697251/5000000000 : ℝ)^4267 ≤ (22179607659501/50000000000000 : ℝ)^3243 := by
    have hnat : (2695697251 : ℕ)^4267*50000000000000^3243 ≤ 22179607659501^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695697251 5000000000 22179607659501 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42277059/80000000 : ℝ), (-2050594881/10000000000 : ℝ), (2695697251/5000000000 : ℝ)] ![(43207063887219/100000000000000 : ℝ), (2486744155541/20000000000000 : ℝ), (22179607659501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42277059/80000000 : ℝ)|^4267 ≤ (43207063887219/100000000000000 : ℝ)^3243
        have hw : |(42277059/80000000 : ℝ)|=(42277059/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2050594881/10000000000 : ℝ)|^4267 ≤ (2486744155541/20000000000000 : ℝ)^3243
        have hw : |(-2050594881/10000000000 : ℝ)|=(2050594881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695697251/5000000000 : ℝ)|^4267 ≤ (22179607659501/50000000000000 : ℝ)^3243
        have hw : |(2695697251/5000000000 : ℝ)|=(2695697251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_box_2 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1056926413/2000000000 : ℝ)*x 0 + (5391394821/10000000000 : ℝ)*x 1 + (-1025297433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056926413/2000000000 : ℝ)^4267 ≤ (43207060552361/100000000000000 : ℝ)^3243 := by
    have hnat : (1056926413 : ℕ)^4267*100000000000000^3243 ≤ 43207060552361^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056926413 2000000000 43207060552361 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391394821/10000000000 : ℝ)^4267 ≤ (44359218772419/100000000000000 : ℝ)^3243 := by
    have hnat : (5391394821 : ℕ)^4267*100000000000000^3243 ≤ 44359218772419^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391394821 10000000000 44359218772419 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025297433/5000000000 : ℝ)^4267 ≤ (6216860329017/50000000000000 : ℝ)^3243 := by
    have hnat : (1025297433 : ℕ)^4267*50000000000000^3243 ≤ 6216860329017^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025297433 5000000000 6216860329017 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056926413/2000000000 : ℝ), (5391394821/10000000000 : ℝ), (-1025297433/5000000000 : ℝ)] ![(43207060552361/100000000000000 : ℝ), (44359218772419/100000000000000 : ℝ), (6216860329017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056926413/2000000000 : ℝ)|^4267 ≤ (43207060552361/100000000000000 : ℝ)^3243
        have hw : |(1056926413/2000000000 : ℝ)|=(1056926413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391394821/10000000000 : ℝ)|^4267 ≤ (44359218772419/100000000000000 : ℝ)^3243
        have hw : |(5391394821/10000000000 : ℝ)|=(5391394821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1025297433/5000000000 : ℝ)|^4267 ≤ (6216860329017/50000000000000 : ℝ)^3243
        have hw : |(-1025297433/5000000000 : ℝ)|=(1025297433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_box_3 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (896979643/2000000000 : ℝ)*x 0 + (1066326767/2500000000 : ℝ)*x 1 + (4265307139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (896979643/2000000000 : ℝ)^4267 ≤ (17408487226079/50000000000000 : ℝ)^3243 := by
    have hnat : (896979643 : ℕ)^4267*50000000000000^3243 ≤ 17408487226079^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896979643 2000000000 17408487226079 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1066326767/2500000000 : ℝ)^4267 ≤ (1303660496429/4000000000000 : ℝ)^3243 := by
    have hnat : (1066326767 : ℕ)^4267*4000000000000^3243 ≤ 1303660496429^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066326767 2500000000 1303660496429 4000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4265307139/10000000000 : ℝ)^4267 ≤ (509242392571/1562500000000 : ℝ)^3243 := by
    have hnat : (4265307139 : ℕ)^4267*1562500000000^3243 ≤ 509242392571^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4265307139 10000000000 509242392571 1562500000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(896979643/2000000000 : ℝ), (1066326767/2500000000 : ℝ), (4265307139/10000000000 : ℝ)] ![(17408487226079/50000000000000 : ℝ), (1303660496429/4000000000000 : ℝ), (509242392571/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(896979643/2000000000 : ℝ)|^4267 ≤ (17408487226079/50000000000000 : ℝ)^3243
        have hw : |(896979643/2000000000 : ℝ)|=(896979643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1066326767/2500000000 : ℝ)|^4267 ≤ (1303660496429/4000000000000 : ℝ)^3243
        have hw : |(1066326767/2500000000 : ℝ)|=(1066326767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4265307139/10000000000 : ℝ)|^4267 ≤ (509242392571/1562500000000 : ℝ)^3243
        have hw : |(4265307139/10000000000 : ℝ)|=(4265307139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_box_4 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2247449487/10000000000 : ℝ)*x 0 + (1316022797/2500000000 : ℝ)*x 1 + (5264092083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2247449487/10000000000 : ℝ)^4267 ≤ (1753442395321/12500000000000 : ℝ)^3243 := by
    have hnat : (2247449487 : ℕ)^4267*12500000000000^3243 ≤ 1753442395321^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247449487 10000000000 1753442395321 12500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316022797/2500000000 : ℝ)^4267 ≤ (42986225598527/100000000000000 : ℝ)^3243 := by
    have hnat : (1316022797 : ℕ)^4267*100000000000000^3243 ≤ 42986225598527^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316022797 2500000000 42986225598527 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264092083/10000000000 : ℝ)^4267 ≤ (42986235214753/100000000000000 : ℝ)^3243 := by
    have hnat : (5264092083 : ℕ)^4267*100000000000000^3243 ≤ 42986235214753^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264092083 10000000000 42986235214753 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2247449487/10000000000 : ℝ), (1316022797/2500000000 : ℝ), (5264092083/10000000000 : ℝ)] ![(1753442395321/12500000000000 : ℝ), (42986225598527/100000000000000 : ℝ), (42986235214753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2247449487/10000000000 : ℝ)|^4267 ≤ (1753442395321/12500000000000 : ℝ)^3243
        have hw : |(-2247449487/10000000000 : ℝ)|=(2247449487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316022797/2500000000 : ℝ)|^4267 ≤ (42986225598527/100000000000000 : ℝ)^3243
        have hw : |(1316022797/2500000000 : ℝ)|=(1316022797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264092083/10000000000 : ℝ)|^4267 ≤ (42986235214753/100000000000000 : ℝ)^3243
        have hw : |(5264092083/10000000000 : ℝ)|=(5264092083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_box_5 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687090313/5000000000 : ℝ)*x 0 + (-16811387/80000000 : ℝ)*x 1 + (105281837/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687090313/5000000000 : ℝ)^4267 ≤ (22086478007981/50000000000000 : ℝ)^3243 := by
    have hnat : (2687090313 : ℕ)^4267*50000000000000^3243 ≤ 22086478007981^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687090313 5000000000 22086478007981 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16811387/80000000 : ℝ)^4267 ≤ (12840811253041/100000000000000 : ℝ)^3243 := by
    have hnat : (16811387 : ℕ)^4267*100000000000000^3243 ≤ 12840811253041^3243*80000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16811387 80000000 12840811253041 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105281837/200000000 : ℝ)^4267 ≤ (42986232711311/100000000000000 : ℝ)^3243 := by
    have hnat : (105281837 : ℕ)^4267*100000000000000^3243 ≤ 42986232711311^3243*200000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105281837 200000000 42986232711311 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687090313/5000000000 : ℝ), (-16811387/80000000 : ℝ), (105281837/200000000 : ℝ)] ![(22086478007981/50000000000000 : ℝ), (12840811253041/100000000000000 : ℝ), (42986232711311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687090313/5000000000 : ℝ)|^4267 ≤ (22086478007981/50000000000000 : ℝ)^3243
        have hw : |(2687090313/5000000000 : ℝ)|=(2687090313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16811387/80000000 : ℝ)|^4267 ≤ (12840811253041/100000000000000 : ℝ)^3243
        have hw : |(-16811387/80000000 : ℝ)|=(16811387/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105281837/200000000 : ℝ)|^4267 ≤ (42986232711311/100000000000000 : ℝ)^3243
        have hw : |(105281837/200000000 : ℝ)|=(105281837/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_box_6 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687090441/5000000000 : ℝ)*x 0 + (5264091359/10000000000 : ℝ)*x 1 + (-2101423687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687090441/5000000000 : ℝ)^4267 ≤ (552161984807/1250000000000 : ℝ)^3243 := by
    have hnat : (2687090441 : ℕ)^4267*1250000000000^3243 ≤ 552161984807^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687090441 5000000000 552161984807 1250000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264091359/10000000000 : ℝ)^4267 ≤ (42986227435817/100000000000000 : ℝ)^3243 := by
    have hnat : (5264091359 : ℕ)^4267*100000000000000^3243 ≤ 42986227435817^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264091359 10000000000 42986227435817 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2101423687/10000000000 : ℝ)^4267 ≤ (12840813761513/100000000000000 : ℝ)^3243 := by
    have hnat : (2101423687 : ℕ)^4267*100000000000000^3243 ≤ 12840813761513^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101423687 10000000000 12840813761513 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687090441/5000000000 : ℝ), (5264091359/10000000000 : ℝ), (-2101423687/10000000000 : ℝ)] ![(552161984807/1250000000000 : ℝ), (42986227435817/100000000000000 : ℝ), (12840813761513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687090441/5000000000 : ℝ)|^4267 ≤ (552161984807/1250000000000 : ℝ)^3243
        have hw : |(2687090441/5000000000 : ℝ)|=(2687090441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264091359/10000000000 : ℝ)|^4267 ≤ (42986227435817/100000000000000 : ℝ)^3243
        have hw : |(5264091359/10000000000 : ℝ)|=(5264091359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2101423687/10000000000 : ℝ)|^4267 ≤ (12840813761513/100000000000000 : ℝ)^3243
        have hw : |(-2101423687/10000000000 : ℝ)|=(2101423687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_box_7 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4185944331/10000000000 : ℝ)*x 0 + (4414729193/10000000000 : ℝ)*x 1 + (441472927/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4185944331/10000000000 : ℝ)^4267 ≤ (31795969850079/100000000000000 : ℝ)^3243 := by
    have hnat : (4185944331 : ℕ)^4267*100000000000000^3243 ≤ 31795969850079^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4185944331 10000000000 31795969850079 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4414729193/10000000000 : ℝ)^4267 ≤ (532843979257/1562500000000 : ℝ)^3243 := by
    have hnat : (4414729193 : ℕ)^4267*1562500000000^3243 ≤ 532843979257^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4414729193 10000000000 532843979257 1562500000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441472927/1000000000 : ℝ)^4267 ≤ (34102015455053/100000000000000 : ℝ)^3243 := by
    have hnat : (441472927 : ℕ)^4267*100000000000000^3243 ≤ 34102015455053^3243*1000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441472927 1000000000 34102015455053 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4185944331/10000000000 : ℝ), (4414729193/10000000000 : ℝ), (441472927/1000000000 : ℝ)] ![(31795969850079/100000000000000 : ℝ), (532843979257/1562500000000 : ℝ), (34102015455053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4185944331/10000000000 : ℝ)|^4267 ≤ (31795969850079/100000000000000 : ℝ)^3243
        have hw : |(4185944331/10000000000 : ℝ)|=(4185944331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4414729193/10000000000 : ℝ)|^4267 ≤ (532843979257/1562500000000 : ℝ)^3243
        have hw : |(4414729193/10000000000 : ℝ)|=(4414729193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(441472927/1000000000 : ℝ)|^4267 ≤ (34102015455053/100000000000000 : ℝ)^3243
        have hw : |(441472927/1000000000 : ℝ)|=(441472927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_box_8 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1087764431/5000000000 : ℝ)*x 0 + (5176620619/10000000000 : ℝ)*x 1 + (67567859/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087764431/5000000000 : ℝ)^4267 ≤ (3359977058473/25000000000000 : ℝ)^3243 := by
    have hnat : (1087764431 : ℕ)^4267*25000000000000^3243 ≤ 3359977058473^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087764431 5000000000 3359977058473 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176620619/10000000000 : ℝ)^4267 ≤ (5256110368557/12500000000000 : ℝ)^3243 := by
    have hnat : (5176620619 : ℕ)^4267*12500000000000^3243 ≤ 5256110368557^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176620619 10000000000 5256110368557 12500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67567859/125000000 : ℝ)^4267 ≤ (44511208812037/100000000000000 : ℝ)^3243 := by
    have hnat : (67567859 : ℕ)^4267*100000000000000^3243 ≤ 44511208812037^3243*125000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67567859 125000000 44511208812037 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1087764431/5000000000 : ℝ), (5176620619/10000000000 : ℝ), (67567859/125000000 : ℝ)] ![(3359977058473/25000000000000 : ℝ), (5256110368557/12500000000000 : ℝ), (44511208812037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1087764431/5000000000 : ℝ)|^4267 ≤ (3359977058473/25000000000000 : ℝ)^3243
        have hw : |(-1087764431/5000000000 : ℝ)|=(1087764431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176620619/10000000000 : ℝ)|^4267 ≤ (5256110368557/12500000000000 : ℝ)^3243
        have hw : |(5176620619/10000000000 : ℝ)|=(5176620619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67567859/125000000 : ℝ)|^4267 ≤ (44511208812037/100000000000000 : ℝ)^3243
        have hw : |(67567859/125000000 : ℝ)|=(67567859/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_box_9 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5274755907/10000000000 : ℝ)*x 0 + (-1022428577/5000000000 : ℝ)*x 1 + (2702713343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274755907/10000000000 : ℝ)^4267 ≤ (10775212022521/25000000000000 : ℝ)^3243 := by
    have hnat : (5274755907 : ℕ)^4267*25000000000000^3243 ≤ 10775212022521^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274755907 10000000000 10775212022521 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1022428577/5000000000 : ℝ)^4267 ≤ (1548495640047/12500000000000 : ℝ)^3243 := by
    have hnat : (1022428577 : ℕ)^4267*12500000000000^3243 ≤ 1548495640047^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022428577 5000000000 1548495640047 12500000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702713343/5000000000 : ℝ)^4267 ≤ (44511186774357/100000000000000 : ℝ)^3243 := by
    have hnat : (2702713343 : ℕ)^4267*100000000000000^3243 ≤ 44511186774357^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702713343 5000000000 44511186774357 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274755907/10000000000 : ℝ), (-1022428577/5000000000 : ℝ), (2702713343/5000000000 : ℝ)] ![(10775212022521/25000000000000 : ℝ), (1548495640047/12500000000000 : ℝ), (44511186774357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274755907/10000000000 : ℝ)|^4267 ≤ (10775212022521/25000000000000 : ℝ)^3243
        have hw : |(5274755907/10000000000 : ℝ)|=(5274755907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1022428577/5000000000 : ℝ)|^4267 ≤ (1548495640047/12500000000000 : ℝ)^3243
        have hw : |(-1022428577/5000000000 : ℝ)|=(1022428577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702713343/5000000000 : ℝ)|^4267 ≤ (44511186774357/100000000000000 : ℝ)^3243
        have hw : |(2702713343/5000000000 : ℝ)|=(2702713343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_box_10 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263737751/500000000 : ℝ)*x 0 + (216217129/400000000 : ℝ)*x 1 + (-2044856259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263737751/500000000 : ℝ)^4267 ≤ (43100838553721/100000000000000 : ℝ)^3243 := by
    have hnat : (263737751 : ℕ)^4267*100000000000000^3243 ≤ 43100838553721^3243*500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263737751 500000000 43100838553721 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216217129/400000000 : ℝ)^4267 ≤ (11127800862221/25000000000000 : ℝ)^3243 := by
    have hnat : (216217129 : ℕ)^4267*25000000000000^3243 ≤ 11127800862221^3243*400000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216217129 400000000 11127800862221 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2044856259/10000000000 : ℝ)^4267 ≤ (6193978993167/50000000000000 : ℝ)^3243 := by
    have hnat : (2044856259 : ℕ)^4267*50000000000000^3243 ≤ 6193978993167^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044856259 10000000000 6193978993167 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263737751/500000000 : ℝ), (216217129/400000000 : ℝ), (-2044856259/10000000000 : ℝ)] ![(43100838553721/100000000000000 : ℝ), (11127800862221/25000000000000 : ℝ), (6193978993167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263737751/500000000 : ℝ)|^4267 ≤ (43100838553721/100000000000000 : ℝ)^3243
        have hw : |(263737751/500000000 : ℝ)|=(263737751/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216217129/400000000 : ℝ)|^4267 ≤ (11127800862221/25000000000000 : ℝ)^3243
        have hw : |(216217129/400000000 : ℝ)|=(216217129/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2044856259/10000000000 : ℝ)|^4267 ≤ (6193978993167/50000000000000 : ℝ)^3243
        have hw : |(-2044856259/10000000000 : ℝ)|=(2044856259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_box_11 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (564661611/1250000000 : ℝ)*x 0 + (4248822317/10000000000 : ℝ)*x 1 + (849764403/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (564661611/1250000000 : ℝ)^4267 ≤ (35148244287613/100000000000000 : ℝ)^3243 := by
    have hnat : (564661611 : ℕ)^4267*100000000000000^3243 ≤ 35148244287613^3243*1250000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564661611 1250000000 35148244287613 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4248822317/10000000000 : ℝ)^4267 ≤ (648517587309/2000000000000 : ℝ)^3243 := by
    have hnat : (4248822317 : ℕ)^4267*2000000000000^3243 ≤ 648517587309^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248822317 10000000000 648517587309 2000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849764403/2000000000 : ℝ)^4267 ≤ (6485175266583/20000000000000 : ℝ)^3243 := by
    have hnat : (849764403 : ℕ)^4267*20000000000000^3243 ≤ 6485175266583^3243*2000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849764403 2000000000 6485175266583 20000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(564661611/1250000000 : ℝ), (4248822317/10000000000 : ℝ), (849764403/2000000000 : ℝ)] ![(35148244287613/100000000000000 : ℝ), (648517587309/2000000000000 : ℝ), (6485175266583/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(564661611/1250000000 : ℝ)|^4267 ≤ (35148244287613/100000000000000 : ℝ)^3243
        have hw : |(564661611/1250000000 : ℝ)|=(564661611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4248822317/10000000000 : ℝ)|^4267 ≤ (648517587309/2000000000000 : ℝ)^3243
        have hw : |(4248822317/10000000000 : ℝ)|=(4248822317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849764403/2000000000 : ℝ)|^4267 ≤ (6485175266583/20000000000000 : ℝ)^3243
        have hw : |(849764403/2000000000 : ℝ)|=(849764403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_box_12 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1976836301/10000000000 : ℝ)*x 0 + (2738289167/5000000000 : ℝ)*x 1 + (5253053559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1976836301/10000000000 : ℝ)^4267 ≤ (5924320206499/50000000000000 : ℝ)^3243 := by
    have hnat : (1976836301 : ℕ)^4267*50000000000000^3243 ≤ 5924320206499^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976836301 10000000000 5924320206499 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738289167/5000000000 : ℝ)^4267 ≤ (45283687250723/100000000000000 : ℝ)^3243 := by
    have hnat : (2738289167 : ℕ)^4267*100000000000000^3243 ≤ 45283687250723^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738289167 5000000000 45283687250723 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253053559/10000000000 : ℝ)^4267 ≤ (10716918082193/25000000000000 : ℝ)^3243 := by
    have hnat : (5253053559 : ℕ)^4267*25000000000000^3243 ≤ 10716918082193^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253053559 10000000000 10716918082193 25000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1976836301/10000000000 : ℝ), (2738289167/5000000000 : ℝ), (5253053559/10000000000 : ℝ)] ![(5924320206499/50000000000000 : ℝ), (45283687250723/100000000000000 : ℝ), (10716918082193/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1976836301/10000000000 : ℝ)|^4267 ≤ (5924320206499/50000000000000 : ℝ)^3243
        have hw : |(-1976836301/10000000000 : ℝ)|=(1976836301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738289167/5000000000 : ℝ)|^4267 ≤ (45283687250723/100000000000000 : ℝ)^3243
        have hw : |(2738289167/5000000000 : ℝ)|=(2738289167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253053559/10000000000 : ℝ)|^4267 ≤ (10716918082193/25000000000000 : ℝ)^3243
        have hw : |(5253053559/10000000000 : ℝ)|=(5253053559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_box_13 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345485621/2500000000 : ℝ)*x 0 + (-2105725287/10000000000 : ℝ)*x 1 + (5253053523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345485621/2500000000 : ℝ)^4267 ≤ (44256918364147/100000000000000 : ℝ)^3243 := by
    have hnat : (1345485621 : ℕ)^4267*100000000000000^3243 ≤ 44256918364147^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345485621 2500000000 44256918364147 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105725287/10000000000 : ℝ)^4267 ≤ (12875409683339/100000000000000 : ℝ)^3243 := by
    have hnat : (2105725287 : ℕ)^4267*100000000000000^3243 ≤ 12875409683339^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105725287 10000000000 12875409683339 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253053523/10000000000 : ℝ)^4267 ≤ (4286767194223/10000000000000 : ℝ)^3243 := by
    have hnat : (5253053523 : ℕ)^4267*10000000000000^3243 ≤ 4286767194223^3243*10000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253053523 10000000000 4286767194223 10000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345485621/2500000000 : ℝ), (-2105725287/10000000000 : ℝ), (5253053523/10000000000 : ℝ)] ![(44256918364147/100000000000000 : ℝ), (12875409683339/100000000000000 : ℝ), (4286767194223/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345485621/2500000000 : ℝ)|^4267 ≤ (44256918364147/100000000000000 : ℝ)^3243
        have hw : |(1345485621/2500000000 : ℝ)|=(1345485621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2105725287/10000000000 : ℝ)|^4267 ≤ (12875409683339/100000000000000 : ℝ)^3243
        have hw : |(-2105725287/10000000000 : ℝ)|=(2105725287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253053523/10000000000 : ℝ)|^4267 ≤ (4286767194223/10000000000000 : ℝ)^3243
        have hw : |(5253053523/10000000000 : ℝ)|=(5253053523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_box_14 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690971133/5000000000 : ℝ)*x 0 + (656631757/1250000000 : ℝ)*x 1 + (-526431217/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690971133/5000000000 : ℝ)^4267 ≤ (44256916005439/100000000000000 : ℝ)^3243 := by
    have hnat : (2690971133 : ℕ)^4267*100000000000000^3243 ≤ 44256916005439^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690971133 5000000000 44256916005439 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656631757/1250000000 : ℝ)^4267 ≤ (21433838832597/50000000000000 : ℝ)^3243 := by
    have hnat : (656631757 : ℕ)^4267*50000000000000^3243 ≤ 21433838832597^3243*1250000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656631757 1250000000 21433838832597 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526431217/2500000000 : ℝ)^4267 ≤ (6437703156207/50000000000000 : ℝ)^3243 := by
    have hnat : (526431217 : ℕ)^4267*50000000000000^3243 ≤ 6437703156207^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526431217 2500000000 6437703156207 50000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690971133/5000000000 : ℝ), (656631757/1250000000 : ℝ), (-526431217/2500000000 : ℝ)] ![(44256916005439/100000000000000 : ℝ), (21433838832597/50000000000000 : ℝ), (6437703156207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690971133/5000000000 : ℝ)|^4267 ≤ (44256916005439/100000000000000 : ℝ)^3243
        have hw : |(2690971133/5000000000 : ℝ)|=(2690971133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(656631757/1250000000 : ℝ)|^4267 ≤ (21433838832597/50000000000000 : ℝ)^3243
        have hw : |(656631757/1250000000 : ℝ)|=(656631757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-526431217/2500000000 : ℝ)|^4267 ≤ (6437703156207/50000000000000 : ℝ)^3243
        have hw : |(-526431217/2500000000 : ℝ)|=(526431217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1307_box_15 (p : ℝ) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2079788061/5000000000 : ℝ)*x 0 + (2213837623/5000000000 : ℝ)*x 1 + (1106918567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2079788061/5000000000 : ℝ)^4267 ≤ (630653986911/2000000000000 : ℝ)^3243 := by
    have hnat : (2079788061 : ℕ)^4267*2000000000000^3243 ≤ 630653986911^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079788061 5000000000 630653986911 2000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213837623/5000000000 : ℝ)^4267 ≤ (1711682764781/5000000000000 : ℝ)^3243 := by
    have hnat : (2213837623 : ℕ)^4267*5000000000000^3243 ≤ 1711682764781^3243*5000000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213837623 5000000000 1711682764781 5000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1106918567/2500000000 : ℝ)^4267 ≤ (34233645346331/100000000000000 : ℝ)^3243 := by
    have hnat : (1106918567 : ℕ)^4267*100000000000000^3243 ≤ 34233645346331^3243*2500000000^4267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106918567 2500000000 34233645346331 100000000000000 4267 3243 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4267/1024 : ℝ)) 4267 3243 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2079788061/5000000000 : ℝ), (2213837623/5000000000 : ℝ), (1106918567/2500000000 : ℝ)] ![(630653986911/2000000000000 : ℝ), (1711682764781/5000000000000 : ℝ), (34233645346331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2079788061/5000000000 : ℝ)|^4267 ≤ (630653986911/2000000000000 : ℝ)^3243
        have hw : |(2079788061/5000000000 : ℝ)|=(2079788061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2213837623/5000000000 : ℝ)|^4267 ≤ (1711682764781/5000000000000 : ℝ)^3243
        have hw : |(2213837623/5000000000 : ℝ)|=(2213837623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1106918567/2500000000 : ℝ)|^4267 ≤ (34233645346331/100000000000000 : ℝ)^3243
        have hw : |(1106918567/2500000000 : ℝ)|=(1106918567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1307_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5533/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62843/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29437/50000 : ℝ) ∧ (79747/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42107/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14683/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5533/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14683/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5533/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14683/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5533/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14683/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5533/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14683/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5533/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14683/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5533/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5533/50000 : ℝ) ^ (2133/512 : ℝ) ≤ (10405193869683409/100000000000000000000 : ℝ) := by
    have hpowers : (5533/50000 : ℝ)^2133 ≤ (10405193869683409/100000000000000000000 : ℝ)^512 := by
      have hnat : (5533 : ℕ)^2133*100000000000000000000^512 ≤ 10405193869683409^512*50000^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5533 50000 10405193869683409 100000000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5533/50000 : ℝ)) (X := (10405193869683409/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14683/100000 : ℝ) ^ (2133/512 : ℝ) ≤ (1690080681545007/5000000000000000000 : ℝ) := by
    have hpowers : (14683/100000 : ℝ)^2133 ≤ (1690080681545007/5000000000000000000 : ℝ)^512 := by
      have hnat : (14683 : ℕ)^2133*5000000000000000000^512 ≤ 1690080681545007^512*100000^2133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14683 100000 1690080681545007 5000000000000000000 2133 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14683/100000 : ℝ)) (X := (1690080681545007/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010405193869683409/50000000000000000000 : ℝ) ≤ (5000249743930653/5000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (50010405193869683409/50000000000000000000 : ℝ)^512 ≤ (5000249743930653/5000000000000000 : ℝ)^2133 := by
      have hnat : (50010405193869683409 : ℕ)^512*5000000000000000^2133 ≤ 5000249743930653^2133*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010405193869683409 50000000000000000000 5000249743930653 5000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000249743930653/5000000000000000 : ℝ)) (X := (50010405193869683409/50000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044206807500583549/100000000000000000000 : ℝ) ≤ (10001060950981751/10000000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (100044206807500583549/100000000000000000000 : ℝ)^512 ≤ (10001060950981751/10000000000000000 : ℝ)^2133 := by
      have hnat : (100044206807500583549 : ℕ)^512*10000000000000000^2133 ≤ 10001060950981751^2133*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044206807500583549 100000000000000000000 10001060950981751 10000000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001060950981751/10000000000000000 : ℝ)) (X := (100044206807500583549/100000000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501690080681545007/2500000000000000000 : ℝ) ≤ (2500405603525549/2500000000000000 : ℝ) ^ (2133/512 : ℝ) := by
    have hpowers : (2501690080681545007/2500000000000000000 : ℝ)^512 ≤ (2500405603525549/2500000000000000 : ℝ)^2133 := by
      have hnat : (2501690080681545007 : ℕ)^512*2500000000000000^2133 ≤ 2500405603525549^2133*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501690080681545007 2500000000000000000 2500405603525549 2500000000000000 512 2133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500405603525549/2500000000000000 : ℝ)) (X := (2501690080681545007/2500000000000000000 : ℝ)) (by norm_num) 2133 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10405193869683409/100000000000000000000 : ℝ) ≤ ((18079690172906327531/18085000000000000000 : ℝ)+2*(112292624089/72340000000000 : ℝ)*(5533/50000 : ℝ))^(2133/512 : ℝ) := by
    rw [show (18079690172906327531/18085000000000000000 : ℝ)+2*(112292624089/72340000000000 : ℝ)*(5533/50000 : ℝ)=(5000249743930653/5000000000000000 : ℝ) by norm_num, show 1+2*(10405193869683409/100000000000000000000 : ℝ)=(50010405193869683409/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1690080681545007/5000000000000000000 : ℝ)+(10405193869683409/100000000000000000000 : ℝ) ≤ ((18079690172906327531/18085000000000000000 : ℝ)+(112292624089/72340000000000 : ℝ)*((14683/100000 : ℝ)+(5533/50000 : ℝ)))^(2133/512 : ℝ) := by
    rw [show (18079690172906327531/18085000000000000000 : ℝ)+(112292624089/72340000000000 : ℝ)*((14683/100000 : ℝ)+(5533/50000 : ℝ))=(10001060950981751/10000000000000000 : ℝ) by norm_num, show 1+(1690080681545007/5000000000000000000 : ℝ)+(10405193869683409/100000000000000000000 : ℝ)=(100044206807500583549/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1690080681545007/5000000000000000000 : ℝ) ≤ ((18079690172906327531/18085000000000000000 : ℝ)+2*(112292624089/72340000000000 : ℝ)*(14683/100000 : ℝ))^(2133/512 : ℝ) := by
    rw [show (18079690172906327531/18085000000000000000 : ℝ)+2*(112292624089/72340000000000 : ℝ)*(14683/100000 : ℝ)=(2500405603525549/2500000000000000 : ℝ) by norm_num, show 1+2*(1690080681545007/5000000000000000000 : ℝ)=(2501690080681545007/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18079690172906327531/18085000000000000000 : ℝ)*(X 1 0+X 2 0)+(112292624089/72340000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (5533/50000 : ℝ)) (hi := (14683/100000 : ℝ)) (c := (18079690172906327531/18085000000000000000 : ℝ)) (alpha := (112292624089/72340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18079690172906327531/18085000000000000000 : ℝ)*(X 0 1+X 2 1)+(112292624089/72340000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (5533/50000 : ℝ)) (hi := (14683/100000 : ℝ)) (c := (18079690172906327531/18085000000000000000 : ℝ)) (alpha := (112292624089/72340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18079690172906327531/18085000000000000000 : ℝ)*(X 0 2+X 1 2)+(112292624089/72340000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2133/512 : ℝ)) (lo := (5533/50000 : ℝ)) (hi := (14683/100000 : ℝ)) (c := (18079690172906327531/18085000000000000000 : ℝ)) (alpha := (112292624089/72340000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-952254363/5000000000 : ℝ)*X 0 0+(5391394661/10000000000 : ℝ)*X 0 1+(2695697329/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((42277059/80000000 : ℝ)*X 1 0+(-2050594881/10000000000 : ℝ)*X 1 1+(2695697251/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1056926413/2000000000 : ℝ)*X 2 0+(5391394821/10000000000 : ℝ)*X 2 1+(-1025297433/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((896979643/2000000000 : ℝ)*X 0 0+(1066326767/2500000000 : ℝ)*X 0 1+(4265307139/10000000000 : ℝ)*X 0 2+(896979643/2000000000 : ℝ)*X 1 0+(1066326767/2500000000 : ℝ)*X 1 1+(4265307139/10000000000 : ℝ)*X 1 2+(896979643/2000000000 : ℝ)*X 2 0+(1066326767/2500000000 : ℝ)*X 2 1+(4265307139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2247449487/10000000000 : ℝ)*X 0 0+(1316022797/2500000000 : ℝ)*X 0 1+(5264092083/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2687090313/5000000000 : ℝ)*X 1 0+(-16811387/80000000 : ℝ)*X 1 1+(105281837/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2687090441/5000000000 : ℝ)*X 2 0+(5264091359/10000000000 : ℝ)*X 2 1+(-2101423687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4185944331/10000000000 : ℝ)*X 0 0+(4414729193/10000000000 : ℝ)*X 0 1+(441472927/1000000000 : ℝ)*X 0 2+(4185944331/10000000000 : ℝ)*X 1 0+(4414729193/10000000000 : ℝ)*X 1 1+(441472927/1000000000 : ℝ)*X 1 2+(4185944331/10000000000 : ℝ)*X 2 0+(4414729193/10000000000 : ℝ)*X 2 1+(441472927/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1087764431/5000000000 : ℝ)*X 0 0+(5176620619/10000000000 : ℝ)*X 0 1+(67567859/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5274755907/10000000000 : ℝ)*X 1 0+(-1022428577/5000000000 : ℝ)*X 1 1+(2702713343/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((263737751/500000000 : ℝ)*X 2 0+(216217129/400000000 : ℝ)*X 2 1+(-2044856259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((564661611/1250000000 : ℝ)*X 0 0+(4248822317/10000000000 : ℝ)*X 0 1+(849764403/2000000000 : ℝ)*X 0 2+(564661611/1250000000 : ℝ)*X 1 0+(4248822317/10000000000 : ℝ)*X 1 1+(849764403/2000000000 : ℝ)*X 1 2+(564661611/1250000000 : ℝ)*X 2 0+(4248822317/10000000000 : ℝ)*X 2 1+(849764403/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1976836301/10000000000 : ℝ)*X 0 0+(2738289167/5000000000 : ℝ)*X 0 1+(5253053559/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1345485621/2500000000 : ℝ)*X 1 0+(-2105725287/10000000000 : ℝ)*X 1 1+(5253053523/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2690971133/5000000000 : ℝ)*X 2 0+(656631757/1250000000 : ℝ)*X 2 1+(-526431217/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2079788061/5000000000 : ℝ)*X 0 0+(2213837623/5000000000 : ℝ)*X 0 1+(1106918567/2500000000 : ℝ)*X 0 2+(2079788061/5000000000 : ℝ)*X 1 0+(2213837623/5000000000 : ℝ)*X 1 1+(1106918567/2500000000 : ℝ)*X 1 2+(2079788061/5000000000 : ℝ)*X 2 0+(2213837623/5000000000 : ℝ)*X 2 1+(1106918567/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1307_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62843/100000 : ℝ) ≤ (-142059385102118750515365197174937/226062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2649879/3125000000000 : ℝ)*(upper1) + (103181929/100000000000000 : ℝ)*(lower4) + (92678319/100000000000000 : ℝ)*(upper5) + (1440595853771291/50000000000000 : ℝ)*(major0) + (1440595853771291/50000000000000 : ℝ)*(major1) + (1440595853771291/50000000000000 : ℝ)*(major2) + (221264079/1000000000000 : ℝ)*(sp2) + (10431513849/100000000000000 : ℝ)*(sp3) + (780899741845251/20000000000000 : ℝ)*(sp4) + (3904504306754829/100000000000000 : ℝ)*(sp5) + (3904488619576909/100000000000000 : ℝ)*(sp6) + (375761831282177/20000000000000 : ℝ)*(sp7) + (6018379277/50000000000000 : ℝ)*(sp12) + (321961499/5000000000000 : ℝ)*(sp13) + (1878819587924733/100000000000000 : ℝ)*(f.failure) + (3904510745984809/100000000000000 : ℝ)*(f.sum) + (19808975586829/3617000000000000000000000000 : ℝ)*base66 + (667805013444787479/904250000000000000000000000000000 : ℝ)*base68 + (459957995815537479/904250000000000000000000000000000 : ℝ)*base70 + (1073610016076537479/904250000000000000000000000000000 : ℝ)*base72 + (5149453074441/904250000000000000000000000 : ℝ)*base73 + (1150845520143712521/904250000000000000000000000000000 : ℝ)*base75 + (1375226188023537479/904250000000000000000000000000000 : ℝ)*base78 + (3043274515278537479/904250000000000000000000000000000 : ℝ)*base80 + (506712978229/113031250000000000000000000 : ℝ)*base82 + (12515197/2500000000000000000000 : ℝ)*base90 + (12515197/2500000000000000000000 : ℝ)*base92 + (12515197/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (29437/50000 : ℝ) ≤ (2129551110409832404962603141/3617000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8226911/50000000000000 : ℝ)*(lower0) + (1248021/12500000000000 : ℝ)*(upper2) + (6243587/12500000000000 : ℝ)*(lower4) + (147435142180743/5000000000000 : ℝ)*(major0) + (147435142180743/5000000000000 : ℝ)*(major1) + (147435142180743/5000000000000 : ℝ)*(major2) + (3954935955986897/100000000000000 : ℝ)*(sp0) + (1977450720480439/50000000000000 : ℝ)*(sp1) + (1977466865413903/50000000000000 : ℝ)*(sp2) + (1922842541849027/100000000000000 : ℝ)*(sp3) + (3095711653/100000000000000 : ℝ)*(sp6) + (464229339/50000000000000 : ℝ)*(sp7) + (1769278929/5000000000000 : ℝ)*(sp9) + (435276281/50000000000000 : ℝ)*(sp12) + (384568694061541/20000000000000 : ℝ)*(f.failure) + (1977468413269729/50000000000000 : ℝ)*(f.sum) + (85713294419877/3617000000000000000000000000 : ℝ)*base65 + (103349928343189467/90425000000000000000000000000000 : ℝ)*base68 + (50534031548039467/90425000000000000000000000000000 : ℝ)*base70 + (1393529225444160533/90425000000000000000000000000000 : ℝ)*base71 + (289399023357/452125000000000000000000000 : ℝ)*base73 + (183321814714860533/90425000000000000000000000000000 : ℝ)*base75 + (5828129572906889467/90425000000000000000000000000000 : ℝ)*base78 + (195509170162410533/90425000000000000000000000000000 : ℝ)*base79 + (2598866868719/1808500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (4069/500000000000000000000 : ℝ)*base90 + (4069/500000000000000000000 : ℝ)*base92 + (4069/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79747/100000 : ℝ) ≤ (180283726769038140881422245637527/226062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44373563/20000000000000 : ℝ)*(upper1) + (47919163/12500000000000 : ℝ)*(lower3) + (23919/40000000000 : ℝ)*(lower5) + (815546347906613/25000000000000 : ℝ)*(major0) + (815546347906613/25000000000000 : ℝ)*(major1) + (815546347906613/25000000000000 : ℝ)*(major2) + (98122811597/25000000000000 : ℝ)*(sp2) + (131383384723/100000000000000 : ℝ)*(sp3) + (8609491889/100000000000000 : ℝ)*(sp4) + (1092625882697463/25000000000000 : ℝ)*(sp8) + (1092630693960999/25000000000000 : ℝ)*(sp9) + (546266285574701/12500000000000 : ℝ)*(sp10) + (425426691078351/20000000000000 : ℝ)*(sp11) + (2127112451/20000000000000 : ℝ)*(sp12) + (1063632419388239/50000000000000 : ℝ)*(f.failure) + (1092630693960999/25000000000000 : ℝ)*(f.sum) + (3296785669457/3617000000000000000000000000 : ℝ)*base65 + (1114797453983512497/452125000000000000000000000000000 : ℝ)*base68 + (436460483719137497/452125000000000000000000000000000 : ℝ)*base70 + (1339620257978012497/452125000000000000000000000000000 : ℝ)*base72 + (17736206479273/3617000000000000000000000000 : ℝ)*base73 + (2577045158672637497/452125000000000000000000000000000 : ℝ)*base76 + (1568729631970012497/452125000000000000000000000000000 : ℝ)*base78 + (3938827469231762497/452125000000000000000000000000000 : ℝ)*base80 + (376008750893/1808500000000000000000000000 : ℝ)*base82 + (4640049/1250000000000000000000 : ℝ)*base89 + (4640049/1250000000000000000000 : ℝ)*base91 + (4640049/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-42107/50000 : ℝ) ≤ (-3045947493016770507429128679/3617000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14575219/4000000000000 : ℝ)*(lower0) + (14156093/100000000000000 : ℝ)*(lower1) + (54655353/20000000000000 : ℝ)*(upper5) + (32982310116759/1000000000000 : ℝ)*(major0) + (32982310116759/1000000000000 : ℝ)*(major1) + (32982310116759/1000000000000 : ℝ)*(major2) + (646769563/10000000000000 : ℝ)*(sp0) + (125650357911/100000000000000 : ℝ)*(sp5) + (347000667/5000000000000 : ℝ)*(sp7) + (311082893/25000000000000 : ℝ)*(sp8) + (1118438713613909/25000000000000 : ℝ)*(sp12) + (2236818458062463/50000000000000 : ℝ)*(sp13) + (4473762566482837/100000000000000 : ℝ)*(sp14) + (134422698655089/6250000000000 : ℝ)*(sp15) + (537692529623691/25000000000000 : ℝ)*(f.failure) + (4473762566482837/100000000000000 : ℝ)*(f.sum) + (694709010963/452125000000000000000000000 : ℝ)*base65 + (81435569270967971/18085000000000000000000000000000 : ℝ)*base68 + (52522006217382029/18085000000000000000000000000000 : ℝ)*base69 + (7503713762212029/18085000000000000000000000000000 : ℝ)*base71 + (151164712265771/3617000000000000000000000000 : ℝ)*base73 + (48204910467857971/18085000000000000000000000000000 : ℝ)*base76 + (75121717151592029/18085000000000000000000000000000 : ℝ)*base77 + (371383909586717971/18085000000000000000000000000000 : ℝ)*base80 + (3114252651759/452125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (793419/625000000000000000000 : ℝ)*base90 + (793419/625000000000000000000 : ℝ)*base92 + (793419/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1307_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5533/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62843/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29437/50000 : ℝ) else (79747/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42107/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1307_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1307_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5533/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62843/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29437/50000 : ℝ) else (79747/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42107/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1307_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2133/512 : ℝ) ≤ p) (hpb : p ≤ (4267/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38337791/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14683/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5533/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62843/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29437/50000 : ℝ) else (79747/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42107/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1307_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

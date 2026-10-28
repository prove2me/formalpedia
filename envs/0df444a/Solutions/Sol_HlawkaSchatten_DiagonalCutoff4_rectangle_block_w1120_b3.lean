-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1120_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:09:01.548155+00:00
-- url     : https://prove2.me/submissions/497bc0df-db66-4799-8f80-218ad09b75c9

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
theorem support_rectangle_w1120_s9_0 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-87098143/400000000 : ℝ)*x 0 + (33708599/62500000 : ℝ)*x 1 + (2632714591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87098143/400000000 : ℝ)^8313 ≤ (413406627299/3125000000000 : ℝ)^6265 := by
    have hnat : (87098143 : ℕ)^8313*3125000000000^6265 ≤ 413406627299^6265*400000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87098143 400000000 413406627299 3125000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33708599/62500000 : ℝ)^8313 ≤ (22038253155149/50000000000000 : ℝ)^6265 := by
    have hnat : (33708599 : ℕ)^8313*50000000000000^6265 ≤ 22038253155149^6265*62500000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33708599 62500000 22038253155149 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632714591/5000000000 : ℝ)^8313 ≤ (10673620399407/25000000000000 : ℝ)^6265 := by
    have hnat : (2632714591 : ℕ)^8313*25000000000000^6265 ≤ 10673620399407^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632714591 5000000000 10673620399407 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87098143/400000000 : ℝ), (33708599/62500000 : ℝ), (2632714591/5000000000 : ℝ)] ![(413406627299/3125000000000 : ℝ), (22038253155149/50000000000000 : ℝ), (10673620399407/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87098143/400000000 : ℝ)|^8313 ≤ (413406627299/3125000000000 : ℝ)^6265
        have hw : |(-87098143/400000000 : ℝ)|=(87098143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33708599/62500000 : ℝ)|^8313 ≤ (22038253155149/50000000000000 : ℝ)^6265
        have hw : |(33708599/62500000 : ℝ)|=(33708599/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632714591/5000000000 : ℝ)|^8313 ≤ (10673620399407/25000000000000 : ℝ)^6265
        have hw : |(2632714591/5000000000 : ℝ)|=(2632714591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s9_1 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672410917/5000000000 : ℝ)*x 0 + (164544663/312500000 : ℝ)*x 1 + (-280294393/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672410917/5000000000 : ℝ)^8313 ≤ (43550770641249/100000000000000 : ℝ)^6265 := by
    have hnat : (2672410917 : ℕ)^8313*100000000000000^6265 ≤ 43550770641249^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672410917 5000000000 43550770641249 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164544663/312500000 : ℝ)^8313 ≤ (10673620490859/25000000000000 : ℝ)^6265 := by
    have hnat : (164544663 : ℕ)^8313*25000000000000^6265 ≤ 10673620490859^6265*312500000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164544663 312500000 10673620490859 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280294393/1250000000 : ℝ)^8313 ≤ (2750949474999/20000000000000 : ℝ)^6265 := by
    have hnat : (280294393 : ℕ)^8313*20000000000000^6265 ≤ 2750949474999^6265*1250000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280294393 1250000000 2750949474999 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672410917/5000000000 : ℝ), (164544663/312500000 : ℝ), (-280294393/1250000000 : ℝ)] ![(43550770641249/100000000000000 : ℝ), (10673620490859/25000000000000 : ℝ), (2750949474999/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672410917/5000000000 : ℝ)|^8313 ≤ (43550770641249/100000000000000 : ℝ)^6265
        have hw : |(2672410917/5000000000 : ℝ)|=(2672410917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164544663/312500000 : ℝ)|^8313 ≤ (10673620490859/25000000000000 : ℝ)^6265
        have hw : |(164544663/312500000 : ℝ)|=(164544663/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-280294393/1250000000 : ℝ)|^8313 ≤ (2750949474999/20000000000000 : ℝ)^6265
        have hw : |(-280294393/1250000000 : ℝ)|=(280294393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s9_2 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1088729101/5000000000 : ℝ)*x 0 + (658218703/1250000000 : ℝ)*x 1 + (2696527229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088729101/5000000000 : ℝ)^8313 ≤ (6614524687043/50000000000000 : ℝ)^6265 := by
    have hnat : (1088729101 : ℕ)^8313*50000000000000^6265 ≤ 6614524687043^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088729101 5000000000 6614524687043 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658218703/1250000000 : ℝ)^8313 ≤ (42697929289359/100000000000000 : ℝ)^6265 := by
    have hnat : (658218703 : ℕ)^8313*100000000000000^6265 ≤ 42697929289359^6265*1250000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658218703 1250000000 42697929289359 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696527229/5000000000 : ℝ)^8313 ≤ (11018255332149/25000000000000 : ℝ)^6265 := by
    have hnat : (2696527229 : ℕ)^8313*25000000000000^6265 ≤ 11018255332149^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696527229 5000000000 11018255332149 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1088729101/5000000000 : ℝ), (658218703/1250000000 : ℝ), (2696527229/5000000000 : ℝ)] ![(6614524687043/50000000000000 : ℝ), (42697929289359/100000000000000 : ℝ), (11018255332149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1088729101/5000000000 : ℝ)|^8313 ≤ (6614524687043/50000000000000 : ℝ)^6265
        have hw : |(-1088729101/5000000000 : ℝ)|=(1088729101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658218703/1250000000 : ℝ)|^8313 ≤ (42697929289359/100000000000000 : ℝ)^6265
        have hw : |(658218703/1250000000 : ℝ)|=(658218703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696527229/5000000000 : ℝ)|^8313 ≤ (11018255332149/25000000000000 : ℝ)^6265
        have hw : |(2696527229/5000000000 : ℝ)|=(2696527229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s9_3 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062491937/2000000000 : ℝ)*x 0 + (-528682677/2500000000 : ℝ)*x 1 + (1348263309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062491937/2000000000 : ℝ)^8313 ≤ (10800305811523/25000000000000 : ℝ)^6265 := by
    have hnat : (1062491937 : ℕ)^8313*25000000000000^6265 ≤ 10800305811523^6265*2000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062491937 2000000000 10800305811523 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528682677/2500000000 : ℝ)^8313 ≤ (2545153732859/20000000000000 : ℝ)^6265 := by
    have hnat : (528682677 : ℕ)^8313*20000000000000^6265 ≤ 2545153732859^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528682677 2500000000 2545153732859 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348263309/2500000000 : ℝ)^8313 ≤ (550912600971/1250000000000 : ℝ)^6265 := by
    have hnat : (1348263309 : ℕ)^8313*1250000000000^6265 ≤ 550912600971^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348263309 2500000000 550912600971 1250000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062491937/2000000000 : ℝ), (-528682677/2500000000 : ℝ), (1348263309/2500000000 : ℝ)] ![(10800305811523/25000000000000 : ℝ), (2545153732859/20000000000000 : ℝ), (550912600971/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062491937/2000000000 : ℝ)|^8313 ≤ (10800305811523/25000000000000 : ℝ)^6265
        have hw : |(1062491937/2000000000 : ℝ)|=(1062491937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-528682677/2500000000 : ℝ)|^8313 ≤ (2545153732859/20000000000000 : ℝ)^6265
        have hw : |(-528682677/2500000000 : ℝ)|=(528682677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348263309/2500000000 : ℝ)|^8313 ≤ (550912600971/1250000000000 : ℝ)^6265
        have hw : |(1348263309/2500000000 : ℝ)|=(1348263309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s9_4 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132811471/250000000 : ℝ)*x 0 + (5393053981/10000000000 : ℝ)*x 1 + (-1057365419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132811471/250000000 : ℝ)^8313 ≤ (43201214128213/100000000000000 : ℝ)^6265 := by
    have hnat : (132811471 : ℕ)^8313*100000000000000^6265 ≤ 43201214128213^6265*250000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132811471 250000000 43201214128213 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393053981/10000000000 : ℝ)^8313 ≤ (5509127019523/12500000000000 : ℝ)^6265 := by
    have hnat : (5393053981 : ℕ)^8313*12500000000000^6265 ≤ 5509127019523^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393053981 10000000000 5509127019523 12500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1057365419/5000000000 : ℝ)^8313 ≤ (12725769702323/100000000000000 : ℝ)^6265 := by
    have hnat : (1057365419 : ℕ)^8313*100000000000000^6265 ≤ 12725769702323^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057365419 5000000000 12725769702323 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132811471/250000000 : ℝ), (5393053981/10000000000 : ℝ), (-1057365419/5000000000 : ℝ)] ![(43201214128213/100000000000000 : ℝ), (5509127019523/12500000000000 : ℝ), (12725769702323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132811471/250000000 : ℝ)|^8313 ≤ (43201214128213/100000000000000 : ℝ)^6265
        have hw : |(132811471/250000000 : ℝ)|=(132811471/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393053981/10000000000 : ℝ)|^8313 ≤ (5509127019523/12500000000000 : ℝ)^6265
        have hw : |(5393053981/10000000000 : ℝ)|=(5393053981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1057365419/5000000000 : ℝ)|^8313 ≤ (12725769702323/100000000000000 : ℝ)^6265
        have hw : |(-1057365419/5000000000 : ℝ)|=(1057365419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_s9_5 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (136493569/312500000 : ℝ)*x 0 + (4495711489/10000000000 : ℝ)*x 1 + (848707397/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136493569/312500000 : ℝ)^8313 ≤ (8329242682209/25000000000000 : ℝ)^6265 := by
    have hnat : (136493569 : ℕ)^8313*25000000000000^6265 ≤ 8329242682209^6265*312500000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136493569 312500000 8329242682209 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4495711489/10000000000 : ℝ)^8313 ≤ (692356566461/2000000000000 : ℝ)^6265 := by
    have hnat : (4495711489 : ℕ)^8313*2000000000000^6265 ≤ 692356566461^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495711489 10000000000 692356566461 2000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848707397/2000000000 : ℝ)^8313 ≤ (2004075057953/6250000000000 : ℝ)^6265 := by
    have hnat : (848707397 : ℕ)^8313*6250000000000^6265 ≤ 2004075057953^6265*2000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848707397 2000000000 2004075057953 6250000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136493569/312500000 : ℝ), (4495711489/10000000000 : ℝ), (848707397/2000000000 : ℝ)] ![(8329242682209/25000000000000 : ℝ), (692356566461/2000000000000 : ℝ), (2004075057953/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136493569/312500000 : ℝ)|^8313 ≤ (8329242682209/25000000000000 : ℝ)^6265
        have hw : |(136493569/312500000 : ℝ)|=(136493569/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4495711489/10000000000 : ℝ)|^8313 ≤ (692356566461/2000000000000 : ℝ)^6265
        have hw : |(4495711489/10000000000 : ℝ)|=(4495711489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848707397/2000000000 : ℝ)|^8313 ≤ (2004075057953/6250000000000 : ℝ)^6265
        have hw : |(848707397/2000000000 : ℝ)|=(848707397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1120_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3509/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (453/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2807/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3509/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (453/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3509/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (453/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3509/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (453/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3509/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (453/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3509/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (453/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3509/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (453/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (453/4000 : ℝ) ^ (1039/256 : ℝ) ≤ (14478560798109227/100000000000000000000 : ℝ) := by
    have hpowers : (453/4000 : ℝ)^1039 ≤ (14478560798109227/100000000000000000000 : ℝ)^256 := by
      have hnat : (453 : ℕ)^1039*100000000000000000000^256 ≤ 14478560798109227^256*4000^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        453 4000 14478560798109227 100000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (453/4000 : ℝ)) (X := (14478560798109227/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3509/25000 : ℝ) ^ (1039/256 : ℝ) ≤ (34594513598724787/100000000000000000000 : ℝ) := by
    have hpowers : (3509/25000 : ℝ)^1039 ≤ (34594513598724787/100000000000000000000 : ℝ)^256 := by
      have hnat : (3509 : ℕ)^1039*100000000000000000000^256 ≤ 34594513598724787^256*25000^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3509 25000 34594513598724787 100000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3509/25000 : ℝ)) (X := (34594513598724787/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014478560798109227/50000000000000000000 : ℝ) ≤ (10000713398885219/10000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (50014478560798109227/50000000000000000000 : ℝ)^256 ≤ (10000713398885219/10000000000000000 : ℝ)^1039 := by
      have hnat : (50014478560798109227 : ℕ)^256*10000000000000000^1039 ≤ 10000713398885219^1039*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014478560798109227 50000000000000000000 10000713398885219 10000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000713398885219/10000000000000000 : ℝ)) (X := (50014478560798109227/50000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024536537198417007/50000000000000000000 : ℝ) ≤ (5000604445849203/5000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (50024536537198417007/50000000000000000000 : ℝ)^256 ≤ (5000604445849203/5000000000000000 : ℝ)^1039 := by
      have hnat : (50024536537198417007 : ℕ)^256*5000000000000000^1039 ≤ 5000604445849203^1039*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024536537198417007 50000000000000000000 5000604445849203 5000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000604445849203/5000000000000000 : ℝ)) (X := (50024536537198417007/50000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034594513598724787/50000000000000000000 : ℝ) ≤ (10001704384511593/10000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (50034594513598724787/50000000000000000000 : ℝ)^256 ≤ (10001704384511593/10000000000000000 : ℝ)^1039 := by
      have hnat : (50034594513598724787 : ℕ)^256*10000000000000000^1039 ≤ 10001704384511593^1039*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034594513598724787 50000000000000000000 10001704384511593 10000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001704384511593/10000000000000000 : ℝ)) (X := (50034594513598724787/50000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14478560798109227/100000000000000000000 : ℝ) ≤ ((27100711112159143159/27110000000000000000 : ℝ)+2*(495492813187/271100000000000 : ℝ)*(453/4000 : ℝ))^(1039/256 : ℝ) := by
    rw [show (27100711112159143159/27110000000000000000 : ℝ)+2*(495492813187/271100000000000 : ℝ)*(453/4000 : ℝ)=(10000713398885219/10000000000000000 : ℝ) by norm_num, show 1+2*(14478560798109227/100000000000000000000 : ℝ)=(50014478560798109227/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34594513598724787/100000000000000000000 : ℝ)+(14478560798109227/100000000000000000000 : ℝ) ≤ ((27100711112159143159/27110000000000000000 : ℝ)+(495492813187/271100000000000 : ℝ)*((3509/25000 : ℝ)+(453/4000 : ℝ)))^(1039/256 : ℝ) := by
    rw [show (27100711112159143159/27110000000000000000 : ℝ)+(495492813187/271100000000000 : ℝ)*((3509/25000 : ℝ)+(453/4000 : ℝ))=(5000604445849203/5000000000000000 : ℝ) by norm_num, show 1+(34594513598724787/100000000000000000000 : ℝ)+(14478560798109227/100000000000000000000 : ℝ)=(50024536537198417007/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34594513598724787/100000000000000000000 : ℝ) ≤ ((27100711112159143159/27110000000000000000 : ℝ)+2*(495492813187/271100000000000 : ℝ)*(3509/25000 : ℝ))^(1039/256 : ℝ) := by
    rw [show (27100711112159143159/27110000000000000000 : ℝ)+2*(495492813187/271100000000000 : ℝ)*(3509/25000 : ℝ)=(10001704384511593/10000000000000000 : ℝ) by norm_num, show 1+2*(34594513598724787/100000000000000000000 : ℝ)=(50034594513598724787/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27100711112159143159/27110000000000000000 : ℝ)*(X 1 0+X 2 0)+(495492813187/271100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (453/4000 : ℝ)) (hi := (3509/25000 : ℝ)) (c := (27100711112159143159/27110000000000000000 : ℝ)) (alpha := (495492813187/271100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27100711112159143159/27110000000000000000 : ℝ)*(X 0 1+X 2 1)+(495492813187/271100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (453/4000 : ℝ)) (hi := (3509/25000 : ℝ)) (c := (27100711112159143159/27110000000000000000 : ℝ)) (alpha := (495492813187/271100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27100711112159143159/27110000000000000000 : ℝ)*(X 0 2+X 1 2)+(495492813187/271100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (453/4000 : ℝ)) (hi := (3509/25000 : ℝ)) (c := (27100711112159143159/27110000000000000000 : ℝ)) (alpha := (495492813187/271100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-87098143/400000000 : ℝ)*X 0 0+(33708599/62500000 : ℝ)*X 0 1+(2632714591/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672410917/5000000000 : ℝ)*X 2 0+(164544663/312500000 : ℝ)*X 2 1+(-280294393/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s9_1 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-1088729101/5000000000 : ℝ)*X 0 0+(658218703/1250000000 : ℝ)*X 0 1+(2696527229/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s9_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1062491937/2000000000 : ℝ)*X 1 0+(-528682677/2500000000 : ℝ)*X 1 1+(1348263309/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s9_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((132811471/250000000 : ℝ)*X 2 0+(5393053981/10000000000 : ℝ)*X 2 1+(-1057365419/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s9_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((136493569/312500000 : ℝ)*X 0 0+(4495711489/10000000000 : ℝ)*X 0 1+(848707397/2000000000 : ℝ)*X 0 2+(136493569/312500000 : ℝ)*X 1 0+(4495711489/10000000000 : ℝ)*X 1 1+(848707397/2000000000 : ℝ)*X 1 2+(136493569/312500000 : ℝ)*X 2 0+(4495711489/10000000000 : ℝ)*X 2 1+(848707397/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5923311866591425200076854957/1355500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12206067/2000000000000 : ℝ)*(base19) + (128803111/100000000000000 : ℝ)*(upper1) + (2825701/12500000000000 : ℝ)*(upper2) + (157300461/50000000000000 : ℝ)*(lower4) + (9082733/50000000000000 : ℝ)*(upper5) + (5910369494963241/100000000000000 : ℝ)*(major0) + (5910369494963241/100000000000000 : ℝ)*(major1) + (5910369494963241/100000000000000 : ℝ)*(major2) + (10772615823/25000000000000 : ℝ)*(sp0) + (722962383/100000000000000 : ℝ)*(sp1) + (1963798237855337/25000000000000 : ℝ)*(sp2) + (7855235431581291/100000000000000 : ℝ)*(sp3) + (7855235318922257/100000000000000 : ℝ)*(sp4) + (1982751401190327/50000000000000 : ℝ)*(sp5) + (1982751401190327/50000000000000 : ℝ)*(f.failure) + (49095225261779/625000000000 : ℝ)*(f.sum) + (284573743002913/13555000000000000000000000000 : ℝ)*base66 + (12380206845450318319/2711000000000000000000000000000000 : ℝ)*base67 + (17231158247829681681/2711000000000000000000000000000000 : ℝ)*base70 + (10565786967268681681/2711000000000000000000000000000000 : ℝ)*base72 + (124206249818277/13555000000000000000000000000 : ℝ)*base73 + (20288400889942318319/2711000000000000000000000000000000 : ℝ)*base75 + (35110419086805681681/2711000000000000000000000000000000 : ℝ)*base78 + (12789526152192681681/2711000000000000000000000000000000 : ℝ)*base80 + (23989676660107/13555000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (12768261/5000000000000000000000 : ℝ)*base89 + (12768261/5000000000000000000000 : ℝ)*base91 + (12768261/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1120_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3509/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1120_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1120_box_0 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-512459183/2500000000 : ℝ)*x 0 + (2688309621/5000000000 : ℝ)*x 1 + (5376618881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (512459183/2500000000 : ℝ)^8313 ≤ (12210218397263/100000000000000 : ℝ)^6265 := by
    have hnat : (512459183 : ℕ)^8313*100000000000000^6265 ≤ 12210218397263^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512459183 2500000000 12210218397263 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688309621/5000000000 : ℝ)^8313 ≤ (8778978549079/20000000000000 : ℝ)^6265 := by
    have hnat : (2688309621 : ℕ)^8313*20000000000000^6265 ≤ 8778978549079^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688309621 5000000000 8778978549079 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376618881/10000000000 : ℝ)^8313 ≤ (10973722208687/25000000000000 : ℝ)^6265 := by
    have hnat : (5376618881 : ℕ)^8313*25000000000000^6265 ≤ 10973722208687^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376618881 10000000000 10973722208687 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-512459183/2500000000 : ℝ), (2688309621/5000000000 : ℝ), (5376618881/10000000000 : ℝ)] ![(12210218397263/100000000000000 : ℝ), (8778978549079/20000000000000 : ℝ), (10973722208687/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-512459183/2500000000 : ℝ)|^8313 ≤ (12210218397263/100000000000000 : ℝ)^6265
        have hw : |(-512459183/2500000000 : ℝ)|=(512459183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688309621/5000000000 : ℝ)|^8313 ≤ (8778978549079/20000000000000 : ℝ)^6265
        have hw : |(2688309621/5000000000 : ℝ)|=(2688309621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376618881/10000000000 : ℝ)|^8313 ≤ (10973722208687/25000000000000 : ℝ)^6265
        have hw : |(5376618881/10000000000 : ℝ)|=(5376618881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_box_1 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295774493/10000000000 : ℝ)*x 0 + (-2159420097/10000000000 : ℝ)*x 1 + (5376619117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295774493/10000000000 : ℝ)^8313 ≤ (43021276022499/100000000000000 : ℝ)^6265 := by
    have hnat : (5295774493 : ℕ)^8313*100000000000000^6265 ≤ 43021276022499^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295774493 10000000000 43021276022499 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2159420097/10000000000 : ℝ)^8313 ≤ (13083832563921/100000000000000 : ℝ)^6265 := by
    have hnat : (2159420097 : ℕ)^8313*100000000000000^6265 ≤ 13083832563921^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159420097 10000000000 13083832563921 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376619117/10000000000 : ℝ)^8313 ≤ (43894891391293/100000000000000 : ℝ)^6265 := by
    have hnat : (5376619117 : ℕ)^8313*100000000000000^6265 ≤ 43894891391293^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376619117 10000000000 43894891391293 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295774493/10000000000 : ℝ), (-2159420097/10000000000 : ℝ), (5376619117/10000000000 : ℝ)] ![(43021276022499/100000000000000 : ℝ), (13083832563921/100000000000000 : ℝ), (43894891391293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295774493/10000000000 : ℝ)|^8313 ≤ (43021276022499/100000000000000 : ℝ)^6265
        have hw : |(5295774493/10000000000 : ℝ)|=(5295774493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2159420097/10000000000 : ℝ)|^8313 ≤ (13083832563921/100000000000000 : ℝ)^6265
        have hw : |(-2159420097/10000000000 : ℝ)|=(2159420097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376619117/10000000000 : ℝ)|^8313 ≤ (43894891391293/100000000000000 : ℝ)^6265
        have hw : |(5376619117/10000000000 : ℝ)|=(5376619117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_box_2 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (661971777/1250000000 : ℝ)*x 0 + (2688309497/5000000000 : ℝ)*x 1 + (-539855159/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661971777/1250000000 : ℝ)^8313 ≤ (43021273036633/100000000000000 : ℝ)^6265 := by
    have hnat : (661971777 : ℕ)^8313*100000000000000^6265 ≤ 43021273036633^6265*1250000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661971777 1250000000 43021273036633 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688309497/5000000000 : ℝ)^8313 ≤ (43894890058857/100000000000000 : ℝ)^6265 := by
    have hnat : (2688309497 : ℕ)^8313*100000000000000^6265 ≤ 43894890058857^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688309497 5000000000 43894890058857 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539855159/2500000000 : ℝ)^8313 ≤ (13083836897267/100000000000000 : ℝ)^6265 := by
    have hnat : (539855159 : ℕ)^8313*100000000000000^6265 ≤ 13083836897267^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539855159 2500000000 13083836897267 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661971777/1250000000 : ℝ), (2688309497/5000000000 : ℝ), (-539855159/2500000000 : ℝ)] ![(43021273036633/100000000000000 : ℝ), (43894890058857/100000000000000 : ℝ), (13083836897267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661971777/1250000000 : ℝ)|^8313 ≤ (43021273036633/100000000000000 : ℝ)^6265
        have hw : |(661971777/1250000000 : ℝ)|=(661971777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688309497/5000000000 : ℝ)|^8313 ≤ (43894890058857/100000000000000 : ℝ)^6265
        have hw : |(2688309497/5000000000 : ℝ)|=(2688309497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-539855159/2500000000 : ℝ)|^8313 ≤ (13083836897267/100000000000000 : ℝ)^6265
        have hw : |(-539855159/2500000000 : ℝ)|=(539855159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_box_3 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4475562529/10000000000 : ℝ)*x 0 + (4316017629/10000000000 : ℝ)*x 1 + (4316018977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4475562529/10000000000 : ℝ)^8313 ≤ (6882422078171/20000000000000 : ℝ)^6265 := by
    have hnat : (4475562529 : ℕ)^8313*20000000000000^6265 ≤ 6882422078171^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475562529 10000000000 6882422078171 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4316017629/10000000000 : ℝ)^8313 ≤ (4099242250109/12500000000000 : ℝ)^6265 := by
    have hnat : (4316017629 : ℕ)^8313*12500000000000^6265 ≤ 4099242250109^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316017629 10000000000 4099242250109 12500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4316018977/10000000000 : ℝ)^8313 ≤ (32793951591421/100000000000000 : ℝ)^6265 := by
    have hnat : (4316018977 : ℕ)^8313*100000000000000^6265 ≤ 32793951591421^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316018977 10000000000 32793951591421 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4475562529/10000000000 : ℝ), (4316017629/10000000000 : ℝ), (4316018977/10000000000 : ℝ)] ![(6882422078171/20000000000000 : ℝ), (4099242250109/12500000000000 : ℝ), (32793951591421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4475562529/10000000000 : ℝ)|^8313 ≤ (6882422078171/20000000000000 : ℝ)^6265
        have hw : |(4475562529/10000000000 : ℝ)|=(4475562529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4316017629/10000000000 : ℝ)|^8313 ≤ (4099242250109/12500000000000 : ℝ)^6265
        have hw : |(4316017629/10000000000 : ℝ)|=(4316017629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4316018977/10000000000 : ℝ)|^8313 ≤ (32793951591421/100000000000000 : ℝ)^6265
        have hw : |(4316018977/10000000000 : ℝ)|=(4316018977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_box_4 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-230646163/1000000000 : ℝ)*x 0 + (5280854499/10000000000 : ℝ)*x 1 + (528085491/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (230646163/1000000000 : ℝ)^8313 ≤ (2855789889779/20000000000000 : ℝ)^6265 := by
    have hnat : (230646163 : ℕ)^8313*20000000000000^6265 ≤ 2855789889779^6265*1000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230646163 1000000000 2855789889779 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280854499/10000000000 : ℝ)^8313 ≤ (2678782690961/6250000000000 : ℝ)^6265 := by
    have hnat : (5280854499 : ℕ)^8313*6250000000000^6265 ≤ 2678782690961^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280854499 10000000000 2678782690961 6250000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528085491/1000000000 : ℝ)^8313 ≤ (2678782967599/6250000000000 : ℝ)^6265 := by
    have hnat : (528085491 : ℕ)^8313*6250000000000^6265 ≤ 2678782967599^6265*1000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528085491 1000000000 2678782967599 6250000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-230646163/1000000000 : ℝ), (5280854499/10000000000 : ℝ), (528085491/1000000000 : ℝ)] ![(2855789889779/20000000000000 : ℝ), (2678782690961/6250000000000 : ℝ), (2678782967599/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-230646163/1000000000 : ℝ)|^8313 ≤ (2855789889779/20000000000000 : ℝ)^6265
        have hw : |(-230646163/1000000000 : ℝ)|=(230646163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280854499/10000000000 : ℝ)|^8313 ≤ (2678782690961/6250000000000 : ℝ)^6265
        have hw : |(5280854499/10000000000 : ℝ)|=(5280854499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528085491/1000000000 : ℝ)|^8313 ≤ (2678782967599/6250000000000 : ℝ)^6265
        have hw : |(528085491/1000000000 : ℝ)|=(528085491/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_box_5 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681732429/5000000000 : ℝ)*x 0 + (-2197025631/10000000000 : ℝ)*x 1 + (330053423/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681732429/5000000000 : ℝ)^8313 ≤ (43752450723097/100000000000000 : ℝ)^6265 := by
    have hnat : (2681732429 : ℕ)^8313*100000000000000^6265 ≤ 43752450723097^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681732429 5000000000 43752450723097 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197025631/10000000000 : ℝ)^8313 ≤ (6693511652787/50000000000000 : ℝ)^6265 := by
    have hnat : (2197025631 : ℕ)^8313*50000000000000^6265 ≤ 6693511652787^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197025631 10000000000 6693511652787 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (330053423/625000000 : ℝ)^8313 ≤ (21430262976167/50000000000000 : ℝ)^6265 := by
    have hnat : (330053423 : ℕ)^8313*50000000000000^6265 ≤ 21430262976167^6265*625000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330053423 625000000 21430262976167 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681732429/5000000000 : ℝ), (-2197025631/10000000000 : ℝ), (330053423/625000000 : ℝ)] ![(43752450723097/100000000000000 : ℝ), (6693511652787/50000000000000 : ℝ), (21430262976167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681732429/5000000000 : ℝ)|^8313 ≤ (43752450723097/100000000000000 : ℝ)^6265
        have hw : |(2681732429/5000000000 : ℝ)|=(2681732429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2197025631/10000000000 : ℝ)|^8313 ≤ (6693511652787/50000000000000 : ℝ)^6265
        have hw : |(-2197025631/10000000000 : ℝ)|=(2197025631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(330053423/625000000 : ℝ)|^8313 ≤ (21430262976167/50000000000000 : ℝ)^6265
        have hw : |(330053423/625000000 : ℝ)|=(330053423/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_box_6 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (536346547/1000000000 : ℝ)*x 0 + (330053479/625000000 : ℝ)*x 1 + (-2197023619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536346547/1000000000 : ℝ)^8313 ≤ (1750098293899/4000000000000 : ℝ)^6265 := by
    have hnat : (536346547 : ℕ)^8313*4000000000000^6265 ≤ 1750098293899^6265*1000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536346547 1000000000 1750098293899 4000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (330053479/625000000 : ℝ)^8313 ≤ (42860535601683/100000000000000 : ℝ)^6265 := by
    have hnat : (330053479 : ℕ)^8313*100000000000000^6265 ≤ 42860535601683^6265*625000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330053479 625000000 42860535601683 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2197023619/10000000000 : ℝ)^8313 ≤ (13387007038347/100000000000000 : ℝ)^6265 := by
    have hnat : (2197023619 : ℕ)^8313*100000000000000^6265 ≤ 13387007038347^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197023619 10000000000 13387007038347 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536346547/1000000000 : ℝ), (330053479/625000000 : ℝ), (-2197023619/10000000000 : ℝ)] ![(1750098293899/4000000000000 : ℝ), (42860535601683/100000000000000 : ℝ), (13387007038347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536346547/1000000000 : ℝ)|^8313 ≤ (1750098293899/4000000000000 : ℝ)^6265
        have hw : |(536346547/1000000000 : ℝ)|=(536346547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(330053479/625000000 : ℝ)|^8313 ≤ (42860535601683/100000000000000 : ℝ)^6265
        have hw : |(330053479/625000000 : ℝ)|=(330053479/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2197023619/10000000000 : ℝ)|^8313 ≤ (13387007038347/100000000000000 : ℝ)^6265
        have hw : |(-2197023619/10000000000 : ℝ)|=(2197023619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_box_7 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4259653541/10000000000 : ℝ)*x 0 + (2211976373/5000000000 : ℝ)*x 1 + (4423950821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4259653541/10000000000 : ℝ)^8313 ≤ (4028361414263/12500000000000 : ℝ)^6265 := by
    have hnat : (4259653541 : ℕ)^8313*12500000000000^6265 ≤ 4028361414263^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4259653541 10000000000 4028361414263 12500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2211976373/5000000000 : ℝ)^8313 ≤ (33886564121593/100000000000000 : ℝ)^6265 := by
    have hnat : (2211976373 : ℕ)^8313*100000000000000^6265 ≤ 33886564121593^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211976373 5000000000 33886564121593 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4423950821/10000000000 : ℝ)^8313 ≤ (6777308911277/20000000000000 : ℝ)^6265 := by
    have hnat : (4423950821 : ℕ)^8313*20000000000000^6265 ≤ 6777308911277^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4423950821 10000000000 6777308911277 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4259653541/10000000000 : ℝ), (2211976373/5000000000 : ℝ), (4423950821/10000000000 : ℝ)] ![(4028361414263/12500000000000 : ℝ), (33886564121593/100000000000000 : ℝ), (6777308911277/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4259653541/10000000000 : ℝ)|^8313 ≤ (4028361414263/12500000000000 : ℝ)^6265
        have hw : |(4259653541/10000000000 : ℝ)|=(4259653541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2211976373/5000000000 : ℝ)|^8313 ≤ (33886564121593/100000000000000 : ℝ)^6265
        have hw : |(2211976373/5000000000 : ℝ)|=(2211976373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4423950821/10000000000 : ℝ)|^8313 ≤ (6777308911277/20000000000000 : ℝ)^6265
        have hw : |(4423950821/10000000000 : ℝ)|=(4423950821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_box_8 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2252823099/10000000000 : ℝ)*x 0 + (81496377/156250000 : ℝ)*x 1 + (5386225497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2252823099/10000000000 : ℝ)^8313 ≤ (13840013725779/100000000000000 : ℝ)^6265 := by
    have hnat : (2252823099 : ℕ)^8313*100000000000000^6265 ≤ 13840013725779^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252823099 10000000000 13840013725779 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81496377/156250000 : ℝ)^8313 ≤ (42161000331209/100000000000000 : ℝ)^6265 := by
    have hnat : (81496377 : ℕ)^8313*100000000000000^6265 ≤ 42161000331209^6265*156250000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81496377 156250000 42161000331209 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386225497/10000000000 : ℝ)^8313 ≤ (4399898592699/10000000000000 : ℝ)^6265 := by
    have hnat : (5386225497 : ℕ)^8313*10000000000000^6265 ≤ 4399898592699^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386225497 10000000000 4399898592699 10000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2252823099/10000000000 : ℝ), (81496377/156250000 : ℝ), (5386225497/10000000000 : ℝ)] ![(13840013725779/100000000000000 : ℝ), (42161000331209/100000000000000 : ℝ), (4399898592699/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2252823099/10000000000 : ℝ)|^8313 ≤ (13840013725779/100000000000000 : ℝ)^6265
        have hw : |(-2252823099/10000000000 : ℝ)|=(2252823099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81496377/156250000 : ℝ)|^8313 ≤ (42161000331209/100000000000000 : ℝ)^6265
        have hw : |(81496377/156250000 : ℝ)|=(81496377/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386225497/10000000000 : ℝ)|^8313 ≤ (4399898592699/10000000000000 : ℝ)^6265
        have hw : |(5386225497/10000000000 : ℝ)|=(5386225497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_box_9 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644490341/5000000000 : ℝ)*x 0 + (-538894593/2500000000 : ℝ)*x 1 + (5386225459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644490341/5000000000 : ℝ)^8313 ≤ (42948058864007/100000000000000 : ℝ)^6265 := by
    have hnat : (2644490341 : ℕ)^8313*100000000000000^6265 ≤ 42948058864007^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644490341 5000000000 42948058864007 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538894593/2500000000 : ℝ)^8313 ≤ (6526477804497/50000000000000 : ℝ)^6265 := by
    have hnat : (538894593 : ℕ)^8313*50000000000000^6265 ≤ 6526477804497^6265*2500000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538894593 2500000000 6526477804497 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386225459/10000000000 : ℝ)^8313 ≤ (43998985515103/100000000000000 : ℝ)^6265 := by
    have hnat : (5386225459 : ℕ)^8313*100000000000000^6265 ≤ 43998985515103^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386225459 10000000000 43998985515103 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644490341/5000000000 : ℝ), (-538894593/2500000000 : ℝ), (5386225459/10000000000 : ℝ)] ![(42948058864007/100000000000000 : ℝ), (6526477804497/50000000000000 : ℝ), (43998985515103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644490341/5000000000 : ℝ)|^8313 ≤ (42948058864007/100000000000000 : ℝ)^6265
        have hw : |(2644490341/5000000000 : ℝ)|=(2644490341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-538894593/2500000000 : ℝ)|^8313 ≤ (6526477804497/50000000000000 : ℝ)^6265
        have hw : |(-538894593/2500000000 : ℝ)|=(538894593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386225459/10000000000 : ℝ)|^8313 ≤ (43998985515103/100000000000000 : ℝ)^6265
        have hw : |(5386225459/10000000000 : ℝ)|=(5386225459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_box_10 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288980757/10000000000 : ℝ)*x 0 + (5386225517/10000000000 : ℝ)*x 1 + (-2155578193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288980757/10000000000 : ℝ)^8313 ≤ (10737014918029/25000000000000 : ℝ)^6265 := by
    have hnat : (5288980757 : ℕ)^8313*25000000000000^6265 ≤ 10737014918029^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288980757 10000000000 10737014918029 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386225517/10000000000 : ℝ)^8313 ≤ (43998986143773/100000000000000 : ℝ)^6265 := by
    have hnat : (5386225517 : ℕ)^8313*100000000000000^6265 ≤ 43998986143773^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386225517 10000000000 43998986143773 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2155578193/10000000000 : ℝ)^8313 ≤ (13052954170743/100000000000000 : ℝ)^6265 := by
    have hnat : (2155578193 : ℕ)^8313*100000000000000^6265 ≤ 13052954170743^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155578193 10000000000 13052954170743 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288980757/10000000000 : ℝ), (5386225517/10000000000 : ℝ), (-2155578193/10000000000 : ℝ)] ![(10737014918029/25000000000000 : ℝ), (43998986143773/100000000000000 : ℝ), (13052954170743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288980757/10000000000 : ℝ)|^8313 ≤ (10737014918029/25000000000000 : ℝ)^6265
        have hw : |(5288980757/10000000000 : ℝ)|=(5288980757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386225517/10000000000 : ℝ)|^8313 ≤ (43998986143773/100000000000000 : ℝ)^6265
        have hw : |(5386225517/10000000000 : ℝ)|=(5386225517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2155578193/10000000000 : ℝ)|^8313 ≤ (13052954170743/100000000000000 : ℝ)^6265
        have hw : |(-2155578193/10000000000 : ℝ)|=(2155578193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_box_11 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (179877917/400000000 : ℝ)*x 0 + (53814813/125000000 : ℝ)*x 1 + (34441481/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179877917/400000000 : ℝ)^8313 ≤ (34630461985079/100000000000000 : ℝ)^6265 := by
    have hnat : (179877917 : ℕ)^8313*100000000000000^6265 ≤ 34630461985079^6265*400000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179877917 400000000 34630461985079 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53814813/125000000 : ℝ)^8313 ≤ (32684768572941/100000000000000 : ℝ)^6265 := by
    have hnat : (53814813 : ℕ)^8313*100000000000000^6265 ≤ 32684768572941^6265*125000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53814813 125000000 32684768572941 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34441481/80000000 : ℝ)^8313 ≤ (32684769429209/100000000000000 : ℝ)^6265 := by
    have hnat : (34441481 : ℕ)^8313*100000000000000^6265 ≤ 32684769429209^6265*80000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34441481 80000000 32684769429209 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(179877917/400000000 : ℝ), (53814813/125000000 : ℝ), (34441481/80000000 : ℝ)] ![(34630461985079/100000000000000 : ℝ), (32684768572941/100000000000000 : ℝ), (32684769429209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(179877917/400000000 : ℝ)|^8313 ≤ (34630461985079/100000000000000 : ℝ)^6265
        have hw : |(179877917/400000000 : ℝ)|=(179877917/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53814813/125000000 : ℝ)|^8313 ≤ (32684768572941/100000000000000 : ℝ)^6265
        have hw : |(53814813/125000000 : ℝ)|=(53814813/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(34441481/80000000 : ℝ)|^8313 ≤ (32684769429209/100000000000000 : ℝ)^6265
        have hw : |(34441481/80000000 : ℝ)|=(34441481/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_box_12 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2103808931/10000000000 : ℝ)*x 0 + (42503217/78125000 : ℝ)*x 1 + (5272826113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103808931/10000000000 : ℝ)^8313 ≤ (3159658459287/25000000000000 : ℝ)^6265 := by
    have hnat : (2103808931 : ℕ)^8313*25000000000000^6265 ≤ 3159658459287^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103808931 10000000000 3159658459287 25000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42503217/78125000 : ℝ)^8313 ≤ (44587282197853/100000000000000 : ℝ)^6265 := by
    have hnat : (42503217 : ℕ)^8313*100000000000000^6265 ≤ 44587282197853^6265*78125000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42503217 78125000 44587282197853 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272826113/10000000000 : ℝ)^8313 ≤ (8554816790593/20000000000000 : ℝ)^6265 := by
    have hnat : (5272826113 : ℕ)^8313*20000000000000^6265 ≤ 8554816790593^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272826113 10000000000 8554816790593 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2103808931/10000000000 : ℝ), (42503217/78125000 : ℝ), (5272826113/10000000000 : ℝ)] ![(3159658459287/25000000000000 : ℝ), (44587282197853/100000000000000 : ℝ), (8554816790593/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2103808931/10000000000 : ℝ)|^8313 ≤ (3159658459287/25000000000000 : ℝ)^6265
        have hw : |(-2103808931/10000000000 : ℝ)|=(2103808931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42503217/78125000 : ℝ)|^8313 ≤ (44587282197853/100000000000000 : ℝ)^6265
        have hw : |(42503217/78125000 : ℝ)|=(42503217/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272826113/10000000000 : ℝ)|^8313 ≤ (8554816790593/20000000000000 : ℝ)^6265
        have hw : |(5272826113/10000000000 : ℝ)|=(5272826113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_box_13 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369138183/10000000000 : ℝ)*x 0 + (-2200119283/10000000000 : ℝ)*x 1 + (5272826507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369138183/10000000000 : ℝ)^8313 ≤ (43813870236907/100000000000000 : ℝ)^6265 := by
    have hnat : (5369138183 : ℕ)^8313*100000000000000^6265 ≤ 43813870236907^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369138183 10000000000 43813870236907 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2200119283/10000000000 : ℝ)^8313 ≤ (13412041558047/100000000000000 : ℝ)^6265 := by
    have hnat : (2200119283 : ℕ)^8313*100000000000000^6265 ≤ 13412041558047^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200119283 10000000000 13412041558047 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272826507/10000000000 : ℝ)^8313 ≤ (42774088193983/100000000000000 : ℝ)^6265 := by
    have hnat : (5272826507 : ℕ)^8313*100000000000000^6265 ≤ 42774088193983^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272826507 10000000000 42774088193983 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369138183/10000000000 : ℝ), (-2200119283/10000000000 : ℝ), (5272826507/10000000000 : ℝ)] ![(43813870236907/100000000000000 : ℝ), (13412041558047/100000000000000 : ℝ), (42774088193983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369138183/10000000000 : ℝ)|^8313 ≤ (43813870236907/100000000000000 : ℝ)^6265
        have hw : |(5369138183/10000000000 : ℝ)|=(5369138183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2200119283/10000000000 : ℝ)|^8313 ≤ (13412041558047/100000000000000 : ℝ)^6265
        have hw : |(-2200119283/10000000000 : ℝ)|=(2200119283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272826507/10000000000 : ℝ)|^8313 ≤ (42774088193983/100000000000000 : ℝ)^6265
        have hw : |(5272826507/10000000000 : ℝ)|=(5272826507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_box_14 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369138443/10000000000 : ℝ)*x 0 + (5272826213/10000000000 : ℝ)*x 1 + (-1100059663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369138443/10000000000 : ℝ)^8313 ≤ (21906936526079/50000000000000 : ℝ)^6265 := by
    have hnat : (5369138443 : ℕ)^8313*50000000000000^6265 ≤ 21906936526079^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369138443 10000000000 21906936526079 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5272826213/10000000000 : ℝ)^8313 ≤ (8554817005873/20000000000000 : ℝ)^6265 := by
    have hnat : (5272826213 : ℕ)^8313*20000000000000^6265 ≤ 8554817005873^6265*10000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272826213 10000000000 8554817005873 20000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100059663/5000000000 : ℝ)^8313 ≤ (6706020952933/50000000000000 : ℝ)^6265 := by
    have hnat : (1100059663 : ℕ)^8313*50000000000000^6265 ≤ 6706020952933^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100059663 5000000000 6706020952933 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369138443/10000000000 : ℝ), (5272826213/10000000000 : ℝ), (-1100059663/5000000000 : ℝ)] ![(21906936526079/50000000000000 : ℝ), (8554817005873/20000000000000 : ℝ), (6706020952933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369138443/10000000000 : ℝ)|^8313 ≤ (21906936526079/50000000000000 : ℝ)^6265
        have hw : |(5369138443/10000000000 : ℝ)|=(5369138443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5272826213/10000000000 : ℝ)|^8313 ≤ (8554817005873/20000000000000 : ℝ)^6265
        have hw : |(5272826213/10000000000 : ℝ)|=(5272826213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1100059663/5000000000 : ℝ)|^8313 ≤ (6706020952933/50000000000000 : ℝ)^6265
        have hw : |(-1100059663/5000000000 : ℝ)|=(1100059663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1120_box_15 (p : ℝ) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (848264649/2000000000 : ℝ)*x 0 + (2216497287/5000000000 : ℝ)*x 1 + (2216497563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848264649/2000000000 : ℝ)^8313 ≤ (32043007097257/100000000000000 : ℝ)^6265 := by
    have hnat : (848264649 : ℕ)^8313*100000000000000^6265 ≤ 32043007097257^6265*2000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848264649 2000000000 32043007097257 100000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2216497287/5000000000 : ℝ)^8313 ≤ (4247311705219/12500000000000 : ℝ)^6265 := by
    have hnat : (2216497287 : ℕ)^8313*12500000000000^6265 ≤ 4247311705219^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216497287 5000000000 4247311705219 12500000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2216497563/5000000000 : ℝ)^8313 ≤ (16989249627943/50000000000000 : ℝ)^6265 := by
    have hnat : (2216497563 : ℕ)^8313*50000000000000^6265 ≤ 16989249627943^6265*5000000000^8313 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216497563 5000000000 16989249627943 50000000000000 8313 6265 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8313/2048 : ℝ)) 8313 6265 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(848264649/2000000000 : ℝ), (2216497287/5000000000 : ℝ), (2216497563/5000000000 : ℝ)] ![(32043007097257/100000000000000 : ℝ), (4247311705219/12500000000000 : ℝ), (16989249627943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(848264649/2000000000 : ℝ)|^8313 ≤ (32043007097257/100000000000000 : ℝ)^6265
        have hw : |(848264649/2000000000 : ℝ)|=(848264649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2216497287/5000000000 : ℝ)|^8313 ≤ (4247311705219/12500000000000 : ℝ)^6265
        have hw : |(2216497287/5000000000 : ℝ)|=(2216497287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2216497563/5000000000 : ℝ)|^8313 ≤ (16989249627943/50000000000000 : ℝ)^6265
        have hw : |(2216497563/5000000000 : ℝ)|=(2216497563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1120_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62229/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29641/50000 : ℝ) ∧ (79741/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (3323/4000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2807/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (453/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2807/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (453/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2807/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (453/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2807/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (453/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2807/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (453/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2807/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (453/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (453/4000 : ℝ) ^ (1039/256 : ℝ) ≤ (14478560798109227/100000000000000000000 : ℝ) := by
    have hpowers : (453/4000 : ℝ)^1039 ≤ (14478560798109227/100000000000000000000 : ℝ)^256 := by
      have hnat : (453 : ℕ)^1039*100000000000000000000^256 ≤ 14478560798109227^256*4000^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        453 4000 14478560798109227 100000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (453/4000 : ℝ)) (X := (14478560798109227/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2807/20000 : ℝ) ^ (1039/256 : ℝ) ≤ (6916902295414039/20000000000000000000 : ℝ) := by
    have hpowers : (2807/20000 : ℝ)^1039 ≤ (6916902295414039/20000000000000000000 : ℝ)^256 := by
      have hnat : (2807 : ℕ)^1039*20000000000000000000^256 ≤ 6916902295414039^256*20000^1039 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2807 20000 6916902295414039 20000000000000000000 1039 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2807/20000 : ℝ)) (X := (6916902295414039/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014478560798109227/50000000000000000000 : ℝ) ≤ (10000713398885219/10000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (50014478560798109227/50000000000000000000 : ℝ)^256 ≤ (10000713398885219/10000000000000000 : ℝ)^1039 := by
      have hnat : (50014478560798109227 : ℕ)^256*10000000000000000^1039 ≤ 10000713398885219^1039*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014478560798109227 50000000000000000000 10000713398885219 10000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000713398885219/10000000000000000 : ℝ)) (X := (50014478560798109227/50000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024531536137589711/50000000000000000000 : ℝ) ≤ (10001208645346461/10000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (50024531536137589711/50000000000000000000 : ℝ)^256 ≤ (10001208645346461/10000000000000000 : ℝ)^1039 := by
      have hnat : (50024531536137589711 : ℕ)^256*10000000000000000^1039 ≤ 10001208645346461^1039*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024531536137589711 50000000000000000000 10001208645346461 10000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001208645346461/10000000000000000 : ℝ)) (X := (50024531536137589711/50000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006916902295414039/10000000000000000000 : ℝ) ≤ (10001703891807703/10000000000000000 : ℝ) ^ (1039/256 : ℝ) := by
    have hpowers : (10006916902295414039/10000000000000000000 : ℝ)^256 ≤ (10001703891807703/10000000000000000 : ℝ)^1039 := by
      have hnat : (10006916902295414039 : ℕ)^256*10000000000000000^1039 ≤ 10001703891807703^1039*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006916902295414039 10000000000000000000 10001703891807703 10000000000000000 256 1039 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001703891807703/10000000000000000 : ℝ)) (X := (10006916902295414039/10000000000000000000 : ℝ)) (by norm_num) 1039 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14478560798109227/100000000000000000000 : ℝ) ≤ ((2709071597863181219/2710000000000000000 : ℝ)+2*(247623230621/135500000000000 : ℝ)*(453/4000 : ℝ))^(1039/256 : ℝ) := by
    rw [show (2709071597863181219/2710000000000000000 : ℝ)+2*(247623230621/135500000000000 : ℝ)*(453/4000 : ℝ)=(10000713398885219/10000000000000000 : ℝ) by norm_num, show 1+2*(14478560798109227/100000000000000000000 : ℝ)=(50014478560798109227/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6916902295414039/20000000000000000000 : ℝ)+(14478560798109227/100000000000000000000 : ℝ) ≤ ((2709071597863181219/2710000000000000000 : ℝ)+(247623230621/135500000000000 : ℝ)*((2807/20000 : ℝ)+(453/4000 : ℝ)))^(1039/256 : ℝ) := by
    rw [show (2709071597863181219/2710000000000000000 : ℝ)+(247623230621/135500000000000 : ℝ)*((2807/20000 : ℝ)+(453/4000 : ℝ))=(10001208645346461/10000000000000000 : ℝ) by norm_num, show 1+(6916902295414039/20000000000000000000 : ℝ)+(14478560798109227/100000000000000000000 : ℝ)=(50024531536137589711/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6916902295414039/20000000000000000000 : ℝ) ≤ ((2709071597863181219/2710000000000000000 : ℝ)+2*(247623230621/135500000000000 : ℝ)*(2807/20000 : ℝ))^(1039/256 : ℝ) := by
    rw [show (2709071597863181219/2710000000000000000 : ℝ)+2*(247623230621/135500000000000 : ℝ)*(2807/20000 : ℝ)=(10001703891807703/10000000000000000 : ℝ) by norm_num, show 1+2*(6916902295414039/20000000000000000000 : ℝ)=(10006916902295414039/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2709071597863181219/2710000000000000000 : ℝ)*(X 1 0+X 2 0)+(247623230621/135500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (453/4000 : ℝ)) (hi := (2807/20000 : ℝ)) (c := (2709071597863181219/2710000000000000000 : ℝ)) (alpha := (247623230621/135500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2709071597863181219/2710000000000000000 : ℝ)*(X 0 1+X 2 1)+(247623230621/135500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (453/4000 : ℝ)) (hi := (2807/20000 : ℝ)) (c := (2709071597863181219/2710000000000000000 : ℝ)) (alpha := (247623230621/135500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2709071597863181219/2710000000000000000 : ℝ)*(X 0 2+X 1 2)+(247623230621/135500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1039/256 : ℝ)) (lo := (453/4000 : ℝ)) (hi := (2807/20000 : ℝ)) (c := (2709071597863181219/2710000000000000000 : ℝ)) (alpha := (247623230621/135500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-512459183/2500000000 : ℝ)*X 0 0+(2688309621/5000000000 : ℝ)*X 0 1+(5376618881/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295774493/10000000000 : ℝ)*X 1 0+(-2159420097/10000000000 : ℝ)*X 1 1+(5376619117/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((661971777/1250000000 : ℝ)*X 2 0+(2688309497/5000000000 : ℝ)*X 2 1+(-539855159/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4475562529/10000000000 : ℝ)*X 0 0+(4316017629/10000000000 : ℝ)*X 0 1+(4316018977/10000000000 : ℝ)*X 0 2+(4475562529/10000000000 : ℝ)*X 1 0+(4316017629/10000000000 : ℝ)*X 1 1+(4316018977/10000000000 : ℝ)*X 1 2+(4475562529/10000000000 : ℝ)*X 2 0+(4316017629/10000000000 : ℝ)*X 2 1+(4316018977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-230646163/1000000000 : ℝ)*X 0 0+(5280854499/10000000000 : ℝ)*X 0 1+(528085491/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681732429/5000000000 : ℝ)*X 1 0+(-2197025631/10000000000 : ℝ)*X 1 1+(330053423/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((536346547/1000000000 : ℝ)*X 2 0+(330053479/625000000 : ℝ)*X 2 1+(-2197023619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4259653541/10000000000 : ℝ)*X 0 0+(2211976373/5000000000 : ℝ)*X 0 1+(4423950821/10000000000 : ℝ)*X 0 2+(4259653541/10000000000 : ℝ)*X 1 0+(2211976373/5000000000 : ℝ)*X 1 1+(4423950821/10000000000 : ℝ)*X 1 2+(4259653541/10000000000 : ℝ)*X 2 0+(2211976373/5000000000 : ℝ)*X 2 1+(4423950821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2252823099/10000000000 : ℝ)*X 0 0+(81496377/156250000 : ℝ)*X 0 1+(5386225497/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644490341/5000000000 : ℝ)*X 1 0+(-538894593/2500000000 : ℝ)*X 1 1+(5386225459/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288980757/10000000000 : ℝ)*X 2 0+(5386225517/10000000000 : ℝ)*X 2 1+(-2155578193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((179877917/400000000 : ℝ)*X 0 0+(53814813/125000000 : ℝ)*X 0 1+(34441481/80000000 : ℝ)*X 0 2+(179877917/400000000 : ℝ)*X 1 0+(53814813/125000000 : ℝ)*X 1 1+(34441481/80000000 : ℝ)*X 1 2+(179877917/400000000 : ℝ)*X 2 0+(53814813/125000000 : ℝ)*X 2 1+(34441481/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2103808931/10000000000 : ℝ)*X 0 0+(42503217/78125000 : ℝ)*X 0 1+(5272826113/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369138183/10000000000 : ℝ)*X 1 0+(-2200119283/10000000000 : ℝ)*X 1 1+(5272826507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369138443/10000000000 : ℝ)*X 2 0+(5272826213/10000000000 : ℝ)*X 2 1+(-1100059663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((848264649/2000000000 : ℝ)*X 0 0+(2216497287/5000000000 : ℝ)*X 0 1+(2216497563/5000000000 : ℝ)*X 0 2+(848264649/2000000000 : ℝ)*X 1 0+(2216497287/5000000000 : ℝ)*X 1 1+(2216497563/5000000000 : ℝ)*X 1 2+(848264649/2000000000 : ℝ)*X 2 0+(2216497287/5000000000 : ℝ)*X 2 1+(2216497563/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1120_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62229/100000 : ℝ) ≤ (-2107912058491183026371446670799/3387500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (339092353/50000000000000 : ℝ)*(lower2) + (108582451/25000000000000 : ℝ)*(upper4) + (26896139/25000000000000 : ℝ)*(upper5) + (97555927412131/2500000000000 : ℝ)*(major0) + (97555927412131/2500000000000 : ℝ)*(major1) + (97555927412131/2500000000000 : ℝ)*(major2) + (21625811051/50000000000000 : ℝ)*(sp1) + (14765986583/100000000000000 : ℝ)*(sp3) + (650877167574957/12500000000000 : ℝ)*(sp4) + (5207006380364339/100000000000000 : ℝ)*(sp5) + (650770796442953/12500000000000 : ℝ)*(sp6) + (2618151857073623/100000000000000 : ℝ)*(sp7) + (6458277357/20000000000000 : ℝ)*(sp8) + (883260442817/100000000000000 : ℝ)*(sp14) + (1309083311530103/50000000000000 : ℝ)*(f.failure) + (130176240799661/2500000000000 : ℝ)*(f.sum) + (12099055785283/1355000000000000000000000000 : ℝ)*base65 + (41908087463987311/6775000000000000000000000000000 : ℝ)*base68 + (12078554393737311/6775000000000000000000000000000 : ℝ)*base70 + (5298760532462311/6775000000000000000000000000000 : ℝ)*base72 + (750053302601/677500000000000000000000000 : ℝ)*base74 + (49141016970012311/6775000000000000000000000000000 : ℝ)*base76 + (44397516309287311/6775000000000000000000000000000 : ℝ)*base78 + (13587283500062311/6775000000000000000000000000000 : ℝ)*base80 + (276623399207/338750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (14611771/5000000000000000000000 : ℝ)*base90 + (14611771/5000000000000000000000 : ℝ)*base92 + (14611771/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29641/50000 : ℝ) ≤ (4016498084039141555448569626917/6775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42764233/25000000000000 : ℝ)*(upper0) + (356947827/100000000000000 : ℝ)*(upper2) + (11238773/50000000000000 : ℝ)*(upper5) + (396602223060181/10000000000000 : ℝ)*(major0) + (396602223060181/10000000000000 : ℝ)*(major1) + (396602223060181/10000000000000 : ℝ)*(major2) + (5251308925925029/100000000000000 : ℝ)*(sp0) + (1050259003246129/20000000000000 : ℝ)*(sp1) + (5251262866645929/100000000000000 : ℝ)*(sp2) + (166309709706223/6250000000000 : ℝ)*(sp3) + (203690467/800000000000 : ℝ)*(sp5) + (726017787/10000000000000 : ℝ)*(sp7) + (5761089309/10000000000000 : ℝ)*(sp10) + (1155161399/10000000000000 : ℝ)*(sp12) + (1330481307738719/50000000000000 : ℝ)*(f.failure) + (5251320477539019/100000000000000 : ℝ)*(f.sum) + (3028079438141/677500000000000000000000000 : ℝ)*base65 + (207135909188960639/27100000000000000000000000000000 : ℝ)*base67 + (90740707543539361/27100000000000000000000000000000 : ℝ)*base70 + (476214420572739361/27100000000000000000000000000000 : ℝ)*base72 + (27468887301/169375000000000000000000000 : ℝ)*base74 + (300639124690139361/27100000000000000000000000000000 : ℝ)*base76 + (340289277371639361/27100000000000000000000000000000 : ℝ)*base78 + (412857855526839361/27100000000000000000000000000000 : ℝ)*base80 + (889252067821/677500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (10632317/5000000000000000000000 : ℝ)*base89 + (10632317/5000000000000000000000 : ℝ)*base91 + (10632317/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79741/100000 : ℝ) ≤ (5402596723841080701063883719/6775000000000000000000000000 : ℝ) := by norm_num
    linear_combination (119931/3125000000000 : ℝ)*(upper0) + (38062953/100000000000000 : ℝ)*(lower1) + (60155757/100000000000000 : ℝ)*(lower3) + (23486613/25000000000000 : ℝ)*(upper4) + (4434076397194037/100000000000000 : ℝ)*(major0) + (4434076397194037/100000000000000 : ℝ)*(major1) + (4434076397194037/100000000000000 : ℝ)*(major2) + (2083811/1000000000000 : ℝ)*(sp0) + (73522421387/100000000000000 : ℝ)*(sp2) + (2510257459/4000000000000 : ℝ)*(sp3) + (2933286353210359/50000000000000 : ℝ)*(sp8) + (5866572914801817/100000000000000 : ℝ)*(sp9) + (586649939238043/10000000000000 : ℝ)*(sp10) + (1487468040729023/50000000000000 : ℝ)*(sp11) + (74374970947363/2500000000000 : ℝ)*(f.failure) + (5866572914801817/100000000000000 : ℝ)*(f.sum) + (481205364893/105859375000000000000000000 : ℝ)*base65 + (4453112409672268897/271000000000000000000000000000000 : ℝ)*base68 + (5794049060235731103/271000000000000000000000000000000 : ℝ)*base69 + (1453401072027731103/271000000000000000000000000000000 : ℝ)*base71 + (935414649887/1693750000000000000000000000 : ℝ)*base74 + (21593390628211268897/271000000000000000000000000000000 : ℝ)*base76 + (400987772959731103/271000000000000000000000000000000 : ℝ)*base77 + (1152618283236268897/271000000000000000000000000000000 : ℝ)*base80 + (15666701949269/846875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2373591/250000000000000000000 : ℝ)*base90 + (2373591/250000000000000000000 : ℝ)*base92 + (2373591/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-3323/4000 : ℝ) ≤ (-22512638919478612814652013547169/27100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17488037/12500000000000 : ℝ)*(lower0) + (333996667/100000000000000 : ℝ)*(lower1) + (55969129/100000000000000 : ℝ)*(lower2) + (893783212374983/20000000000000 : ℝ)*(major0) + (893783212374983/20000000000000 : ℝ)*(major1) + (893783212374983/20000000000000 : ℝ)*(major2) + (41735483789/100000000000000 : ℝ)*(sp0) + (662752673063/100000000000000 : ℝ)*(sp5) + (104702126653/12500000000000 : ℝ)*(sp6) + (14240320543/12500000000000 : ℝ)*(sp7) + (5967107051515771/100000000000000 : ℝ)*(sp12) + (5966486034326497/100000000000000 : ℝ)*(sp13) + (1193262233997267/20000000000000 : ℝ)*(sp14) + (2998260236965103/100000000000000 : ℝ)*(sp15) + (2998374159529447/100000000000000 : ℝ)*(f.failure) + (5967148786999559/100000000000000 : ℝ)*(f.sum) + (5859592447007/1355000000000000000000000000 : ℝ)*base66 + (39210618516095723/54200000000000000000000000000000 : ℝ)*base68 + (8039009037104277/54200000000000000000000000000000 : ℝ)*base69 + (141447502044895723/54200000000000000000000000000000 : ℝ)*base72 + (53226662608967/1355000000000000000000000000 : ℝ)*base74 + (186854550463095723/54200000000000000000000000000000 : ℝ)*base76 + (21963422100895723/54200000000000000000000000000000 : ℝ)*base78 + (1074679984634504277/54200000000000000000000000000000 : ℝ)*base79 + (2898502201837/1355000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (23897579/10000000000000000000000 : ℝ)*base90 + (23897579/10000000000000000000000 : ℝ)*base92 + (23897579/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1120_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2807/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29641/50000 : ℝ) else (79741/100000 : ℝ) ≤ X j i ∧ X j i ≤ (3323/4000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1120_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1120_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3509/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29641/50000 : ℝ) else (79741/100000 : ℝ) ≤ X j i ∧ X j i ≤ (3323/4000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1120_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1120_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1039/256 : ℝ) ≤ p) (hpb : p ≤ (8313/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149044643/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3509/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (453/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62229/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29641/50000 : ℝ) else (79741/100000 : ℝ) ≤ X j i ∧ X j i ≤ (3323/4000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1120_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

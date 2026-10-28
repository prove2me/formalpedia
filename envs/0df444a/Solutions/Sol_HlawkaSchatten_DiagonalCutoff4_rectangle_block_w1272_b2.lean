-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1272_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:22.136573+00:00
-- url     : https://prove2.me/submissions/c11e0841-0e50-468b-aff0-983cea471520

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
theorem support_rectangle_w1272_s6_0 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2105757651/10000000000 : ℝ)*x 0 + (1347693787/2500000000 : ℝ)*x 1 + (658433481/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105757651/10000000000 : ℝ)^4233 ≤ (12808736630119/100000000000000 : ℝ)^3209 := by
    have hnat : (2105757651 : ℕ)^4233*100000000000000^3209 ≤ 12808736630119^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105757651 10000000000 12808736630119 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347693787/2500000000 : ℝ)^4233 ≤ (22130460350309/50000000000000 : ℝ)^3209 := by
    have hnat : (1347693787 : ℕ)^4233*50000000000000^3209 ≤ 22130460350309^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347693787 2500000000 22130460350309 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658433481/1250000000 : ℝ)^4233 ≤ (21465171327159/50000000000000 : ℝ)^3209 := by
    have hnat : (658433481 : ℕ)^4233*50000000000000^3209 ≤ 21465171327159^3209*1250000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658433481 1250000000 21465171327159 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2105757651/10000000000 : ℝ), (1347693787/2500000000 : ℝ), (658433481/1250000000 : ℝ)] ![(12808736630119/100000000000000 : ℝ), (22130460350309/50000000000000 : ℝ), (21465171327159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2105757651/10000000000 : ℝ)|^4233 ≤ (12808736630119/100000000000000 : ℝ)^3209
        have hw : |(-2105757651/10000000000 : ℝ)|=(2105757651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347693787/2500000000 : ℝ)|^4233 ≤ (22130460350309/50000000000000 : ℝ)^3209
        have hw : |(1347693787/2500000000 : ℝ)|=(1347693787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658433481/1250000000 : ℝ)|^4233 ≤ (21465171327159/50000000000000 : ℝ)^3209
        have hw : |(658433481/1250000000 : ℝ)|=(658433481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s6_1 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344178689/10000000000 : ℝ)*x 0 + (-2168272717/10000000000 : ℝ)*x 1 + (2633733943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344178689/10000000000 : ℝ)^4233 ≤ (21878477979257/50000000000000 : ℝ)^3209 := by
    have hnat : (5344178689 : ℕ)^4233*50000000000000^3209 ≤ 21878477979257^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344178689 10000000000 21878477979257 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2168272717/10000000000 : ℝ)^4233 ≤ (13312700957707/100000000000000 : ℝ)^3209 := by
    have hnat : (2168272717 : ℕ)^4233*100000000000000^3209 ≤ 13312700957707^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168272717 10000000000 13312700957707 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633733943/5000000000 : ℝ)^4233 ≤ (670786610357/1562500000000 : ℝ)^3209 := by
    have hnat : (2633733943 : ℕ)^4233*1562500000000^3209 ≤ 670786610357^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633733943 5000000000 670786610357 1562500000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344178689/10000000000 : ℝ), (-2168272717/10000000000 : ℝ), (2633733943/5000000000 : ℝ)] ![(21878477979257/50000000000000 : ℝ), (13312700957707/100000000000000 : ℝ), (670786610357/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344178689/10000000000 : ℝ)|^4233 ≤ (21878477979257/50000000000000 : ℝ)^3209
        have hw : |(5344178689/10000000000 : ℝ)|=(5344178689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2168272717/10000000000 : ℝ)|^4233 ≤ (13312700957707/100000000000000 : ℝ)^3209
        have hw : |(-2168272717/10000000000 : ℝ)|=(2168272717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633733943/5000000000 : ℝ)|^4233 ≤ (670786610357/1562500000000 : ℝ)^3209
        have hw : |(2633733943/5000000000 : ℝ)|=(2633733943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s6_2 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336044701/2500000000 : ℝ)*x 0 + (5267467913/10000000000 : ℝ)*x 1 + (-2168272529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336044701/2500000000 : ℝ)^4233 ≤ (21878478600287/50000000000000 : ℝ)^3209 := by
    have hnat : (1336044701 : ℕ)^4233*50000000000000^3209 ≤ 21878478600287^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336044701 2500000000 21878478600287 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267467913/10000000000 : ℝ)^4233 ≤ (268314645957/625000000000 : ℝ)^3209 := by
    have hnat : (5267467913 : ℕ)^4233*625000000000^3209 ≤ 268314645957^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267467913 10000000000 268314645957 625000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2168272529/10000000000 : ℝ)^4233 ≤ (13312699435097/100000000000000 : ℝ)^3209 := by
    have hnat : (2168272529 : ℕ)^4233*100000000000000^3209 ≤ 13312699435097^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168272529 10000000000 13312699435097 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336044701/2500000000 : ℝ), (5267467913/10000000000 : ℝ), (-2168272529/10000000000 : ℝ)] ![(21878478600287/50000000000000 : ℝ), (268314645957/625000000000 : ℝ), (13312699435097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336044701/2500000000 : ℝ)|^4233 ≤ (21878478600287/50000000000000 : ℝ)^3209
        have hw : |(1336044701/2500000000 : ℝ)|=(1336044701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267467913/10000000000 : ℝ)|^4233 ≤ (268314645957/625000000000 : ℝ)^3209
        have hw : |(5267467913/10000000000 : ℝ)|=(5267467913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2168272529/10000000000 : ℝ)|^4233 ≤ (13312699435097/100000000000000 : ℝ)^3209
        have hw : |(-2168272529/10000000000 : ℝ)|=(2168272529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s6_3 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2173265557/5000000000 : ℝ)*x 0 + (2111235979/5000000000 : ℝ)*x 1 + (894821343/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173265557/5000000000 : ℝ)^4233 ≤ (33317564304883/100000000000000 : ℝ)^3209 := by
    have hnat : (2173265557 : ℕ)^4233*100000000000000^3209 ≤ 33317564304883^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173265557 5000000000 33317564304883 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111235979/5000000000 : ℝ)^4233 ≤ (16034454546083/50000000000000 : ℝ)^3209 := by
    have hnat : (2111235979 : ℕ)^4233*50000000000000^3209 ≤ 16034454546083^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111235979 5000000000 16034454546083 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (894821343/2000000000 : ℝ)^4233 ≤ (17306763293909/50000000000000 : ℝ)^3209 := by
    have hnat : (894821343 : ℕ)^4233*50000000000000^3209 ≤ 17306763293909^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894821343 2000000000 17306763293909 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173265557/5000000000 : ℝ), (2111235979/5000000000 : ℝ), (894821343/2000000000 : ℝ)] ![(33317564304883/100000000000000 : ℝ), (16034454546083/50000000000000 : ℝ), (17306763293909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173265557/5000000000 : ℝ)|^4233 ≤ (33317564304883/100000000000000 : ℝ)^3209
        have hw : |(2173265557/5000000000 : ℝ)|=(2173265557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2111235979/5000000000 : ℝ)|^4233 ≤ (16034454546083/50000000000000 : ℝ)^3209
        have hw : |(2111235979/5000000000 : ℝ)|=(2111235979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(894821343/2000000000 : ℝ)|^4233 ≤ (17306763293909/50000000000000 : ℝ)^3209
        have hw : |(894821343/2000000000 : ℝ)|=(894821343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s6_4 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2105762039/10000000000 : ℝ)*x 0 + (2633890159/5000000000 : ℝ)*x 1 + (134761543/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105762039/10000000000 : ℝ)^4233 ≤ (12808771838271/100000000000000 : ℝ)^3209 := by
    have hnat : (2105762039 : ℕ)^4233*100000000000000^3209 ≤ 12808771838271^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105762039 10000000000 12808771838271 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633890159/5000000000 : ℝ)^4233 ≤ (42933701990369/100000000000000 : ℝ)^3209 := by
    have hnat : (2633890159 : ℕ)^4233*100000000000000^3209 ≤ 42933701990369^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633890159 5000000000 42933701990369 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134761543/250000000 : ℝ)^4233 ≤ (44257526155853/100000000000000 : ℝ)^3209 := by
    have hnat : (134761543 : ℕ)^4233*100000000000000^3209 ≤ 44257526155853^3209*250000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134761543 250000000 44257526155853 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2105762039/10000000000 : ℝ), (2633890159/5000000000 : ℝ), (134761543/250000000 : ℝ)] ![(12808771838271/100000000000000 : ℝ), (42933701990369/100000000000000 : ℝ), (44257526155853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2105762039/10000000000 : ℝ)|^4233 ≤ (12808771838271/100000000000000 : ℝ)^3209
        have hw : |(-2105762039/10000000000 : ℝ)|=(2105762039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633890159/5000000000 : ℝ)|^4233 ≤ (42933701990369/100000000000000 : ℝ)^3209
        have hw : |(2633890159/5000000000 : ℝ)|=(2633890159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134761543/250000000 : ℝ)|^4233 ≤ (44257526155853/100000000000000 : ℝ)^3209
        have hw : |(134761543/250000000 : ℝ)|=(134761543/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s6_5 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (664081409/1250000000 : ℝ)*x 0 + (-798937/3906250 : ℝ)*x 1 + (5390461833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664081409/1250000000 : ℝ)^4233 ≤ (8683352877407/20000000000000 : ℝ)^3209 := by
    have hnat : (664081409 : ℕ)^4233*20000000000000^3209 ≤ 8683352877407^3209*1250000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664081409 1250000000 8683352877407 20000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (798937/3906250 : ℝ)^4233 ≤ (12325708220131/100000000000000 : ℝ)^3209 := by
    have hnat : (798937 : ℕ)^4233*100000000000000^3209 ≤ 12325708220131^3209*3906250^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      798937 3906250 12325708220131 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390461833/10000000000 : ℝ)^4233 ≤ (1770301095187/4000000000000 : ℝ)^3209 := by
    have hnat : (5390461833 : ℕ)^4233*4000000000000^3209 ≤ 1770301095187^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390461833 10000000000 1770301095187 4000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664081409/1250000000 : ℝ), (-798937/3906250 : ℝ), (5390461833/10000000000 : ℝ)] ![(8683352877407/20000000000000 : ℝ), (12325708220131/100000000000000 : ℝ), (1770301095187/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664081409/1250000000 : ℝ)|^4233 ≤ (8683352877407/20000000000000 : ℝ)^3209
        have hw : |(664081409/1250000000 : ℝ)|=(664081409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-798937/3906250 : ℝ)|^4233 ≤ (12325708220131/100000000000000 : ℝ)^3209
        have hw : |(-798937/3906250 : ℝ)|=(798937/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390461833/10000000000 : ℝ)|^4233 ≤ (1770301095187/4000000000000 : ℝ)^3209
        have hw : |(5390461833/10000000000 : ℝ)|=(5390461833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s6_6 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312651581/10000000000 : ℝ)*x 0 + (1078092363/2000000000 : ℝ)*x 1 + (-1022639163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312651581/10000000000 : ℝ)^4233 ≤ (43416767718101/100000000000000 : ℝ)^3209 := by
    have hnat : (5312651581 : ℕ)^4233*100000000000000^3209 ≤ 43416767718101^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312651581 10000000000 43416767718101 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078092363/2000000000 : ℝ)^4233 ≤ (4425752718473/10000000000000 : ℝ)^3209 := by
    have hnat : (1078092363 : ℕ)^4233*10000000000000^3209 ≤ 4425752718473^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078092363 2000000000 4425752718473 10000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1022639163/5000000000 : ℝ)^4233 ≤ (6162852544021/50000000000000 : ℝ)^3209 := by
    have hnat : (1022639163 : ℕ)^4233*50000000000000^3209 ≤ 6162852544021^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022639163 5000000000 6162852544021 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312651581/10000000000 : ℝ), (1078092363/2000000000 : ℝ), (-1022639163/5000000000 : ℝ)] ![(43416767718101/100000000000000 : ℝ), (4425752718473/10000000000000 : ℝ), (6162852544021/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312651581/10000000000 : ℝ)|^4233 ≤ (43416767718101/100000000000000 : ℝ)^3209
        have hw : |(5312651581/10000000000 : ℝ)|=(5312651581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078092363/2000000000 : ℝ)|^4233 ≤ (4425752718473/10000000000000 : ℝ)^3209
        have hw : |(1078092363/2000000000 : ℝ)|=(1078092363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1022639163/5000000000 : ℝ)|^4233 ≤ (6162852544021/50000000000000 : ℝ)^3209
        have hw : |(-1022639163/5000000000 : ℝ)|=(1022639163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s6_7 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (869308149/2000000000 : ℝ)*x 0 + (447346997/1000000000 : ℝ)*x 1 + (4223110823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869308149/2000000000 : ℝ)^4233 ≤ (33317661687297/100000000000000 : ℝ)^3209 := by
    have hnat : (869308149 : ℕ)^4233*100000000000000^3209 ≤ 33317661687297^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869308149 2000000000 33317661687297 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447346997/1000000000 : ℝ)^4233 ≤ (432587858463/1250000000000 : ℝ)^3209 := by
    have hnat : (447346997 : ℕ)^4233*1250000000000^3209 ≤ 432587858463^3209*1000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447346997 1000000000 432587858463 1250000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4223110823/10000000000 : ℝ)^4233 ≤ (32075309616359/100000000000000 : ℝ)^3209 := by
    have hnat : (4223110823 : ℕ)^4233*100000000000000^3209 ≤ 32075309616359^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223110823 10000000000 32075309616359 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869308149/2000000000 : ℝ), (447346997/1000000000 : ℝ), (4223110823/10000000000 : ℝ)] ![(33317661687297/100000000000000 : ℝ), (432587858463/1250000000000 : ℝ), (32075309616359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869308149/2000000000 : ℝ)|^4233 ≤ (33317661687297/100000000000000 : ℝ)^3209
        have hw : |(869308149/2000000000 : ℝ)|=(869308149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(447346997/1000000000 : ℝ)|^4233 ≤ (432587858463/1250000000000 : ℝ)^3209
        have hw : |(447346997/1000000000 : ℝ)|=(447346997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4223110823/10000000000 : ℝ)|^4233 ≤ (32075309616359/100000000000000 : ℝ)^3209
        have hw : |(4223110823/10000000000 : ℝ)|=(4223110823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1272_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14143/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5747/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1439/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3531/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14143/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5747/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14143/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5747/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14143/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5747/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14143/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5747/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14143/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5747/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14143/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5747/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5747/50000 : ℝ) ^ (8465/2048 : ℝ) ≤ (13081117514840673/100000000000000000000 : ℝ) := by
    have hpowers : (5747/50000 : ℝ)^8465 ≤ (13081117514840673/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5747 : ℕ)^8465*100000000000000000000^2048 ≤ 13081117514840673^2048*50000^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5747 50000 13081117514840673 100000000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5747/50000 : ℝ)) (X := (13081117514840673/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14143/100000 : ℝ) ^ (8465/2048 : ℝ) ≤ (15413550642035941/50000000000000000000 : ℝ) := by
    have hpowers : (14143/100000 : ℝ)^8465 ≤ (15413550642035941/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14143 : ℕ)^8465*50000000000000000000^2048 ≤ 15413550642035941^2048*100000^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14143 100000 15413550642035941 50000000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14143/100000 : ℝ)) (X := (15413550642035941/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013081117514840673/50000000000000000000 : ℝ) ≤ (10000632899527147/10000000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (50013081117514840673/50000000000000000000 : ℝ)^2048 ≤ (10000632899527147/10000000000000000 : ℝ)^8465 := by
      have hnat : (50013081117514840673 : ℕ)^2048*10000000000000000^8465 ≤ 10000632899527147^8465*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013081117514840673 50000000000000000000 10000632899527147 10000000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000632899527147/10000000000000000 : ℝ)) (X := (50013081117514840673/50000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008781643759782511/20000000000000000000 : ℝ) ≤ (10001062127232869/10000000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (20008781643759782511/20000000000000000000 : ℝ)^2048 ≤ (10001062127232869/10000000000000000 : ℝ)^8465 := by
      have hnat : (20008781643759782511 : ℕ)^2048*10000000000000000^8465 ≤ 10001062127232869^8465*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008781643759782511 20000000000000000000 10001062127232869 10000000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001062127232869/10000000000000000 : ℝ)) (X := (20008781643759782511/20000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015413550642035941/25000000000000000000 : ℝ) ≤ (10001491354938591/10000000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (25015413550642035941/25000000000000000000 : ℝ)^2048 ≤ (10001491354938591/10000000000000000 : ℝ)^8465 := by
      have hnat : (25015413550642035941 : ℕ)^2048*10000000000000000^8465 ≤ 10001491354938591^8465*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015413550642035941 25000000000000000000 10001491354938591 10000000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001491354938591/10000000000000000 : ℝ)) (X := (25015413550642035941/25000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13081117514840673/100000000000000000000 : ℝ) ≤ ((26481809464348275067/26490000000000000000 : ℝ)+2*(214613852861/132450000000000 : ℝ)*(5747/50000 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (26481809464348275067/26490000000000000000 : ℝ)+2*(214613852861/132450000000000 : ℝ)*(5747/50000 : ℝ)=(10000632899527147/10000000000000000 : ℝ) by norm_num, show 1+2*(13081117514840673/100000000000000000000 : ℝ)=(50013081117514840673/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15413550642035941/50000000000000000000 : ℝ)+(13081117514840673/100000000000000000000 : ℝ) ≤ ((26481809464348275067/26490000000000000000 : ℝ)+(214613852861/132450000000000 : ℝ)*((14143/100000 : ℝ)+(5747/50000 : ℝ)))^(8465/2048 : ℝ) := by
    rw [show (26481809464348275067/26490000000000000000 : ℝ)+(214613852861/132450000000000 : ℝ)*((14143/100000 : ℝ)+(5747/50000 : ℝ))=(10001062127232869/10000000000000000 : ℝ) by norm_num, show 1+(15413550642035941/50000000000000000000 : ℝ)+(13081117514840673/100000000000000000000 : ℝ)=(20008781643759782511/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15413550642035941/50000000000000000000 : ℝ) ≤ ((26481809464348275067/26490000000000000000 : ℝ)+2*(214613852861/132450000000000 : ℝ)*(14143/100000 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (26481809464348275067/26490000000000000000 : ℝ)+2*(214613852861/132450000000000 : ℝ)*(14143/100000 : ℝ)=(10001491354938591/10000000000000000 : ℝ) by norm_num, show 1+2*(15413550642035941/50000000000000000000 : ℝ)=(25015413550642035941/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26481809464348275067/26490000000000000000 : ℝ)*(X 1 0+X 2 0)+(214613852861/132450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (5747/50000 : ℝ)) (hi := (14143/100000 : ℝ)) (c := (26481809464348275067/26490000000000000000 : ℝ)) (alpha := (214613852861/132450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26481809464348275067/26490000000000000000 : ℝ)*(X 0 1+X 2 1)+(214613852861/132450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (5747/50000 : ℝ)) (hi := (14143/100000 : ℝ)) (c := (26481809464348275067/26490000000000000000 : ℝ)) (alpha := (214613852861/132450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26481809464348275067/26490000000000000000 : ℝ)*(X 0 2+X 1 2)+(214613852861/132450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (5747/50000 : ℝ)) (hi := (14143/100000 : ℝ)) (c := (26481809464348275067/26490000000000000000 : ℝ)) (alpha := (214613852861/132450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2105757651/10000000000 : ℝ)*X 0 0+(1347693787/2500000000 : ℝ)*X 0 1+(658433481/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344178689/10000000000 : ℝ)*X 1 0+(-2168272717/10000000000 : ℝ)*X 1 1+(2633733943/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336044701/2500000000 : ℝ)*X 2 0+(5267467913/10000000000 : ℝ)*X 2 1+(-2168272529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2173265557/5000000000 : ℝ)*X 0 0+(2111235979/5000000000 : ℝ)*X 0 1+(894821343/2000000000 : ℝ)*X 0 2+(2173265557/5000000000 : ℝ)*X 1 0+(2111235979/5000000000 : ℝ)*X 1 1+(894821343/2000000000 : ℝ)*X 1 2+(2173265557/5000000000 : ℝ)*X 2 0+(2111235979/5000000000 : ℝ)*X 2 1+(894821343/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2105762039/10000000000 : ℝ)*X 0 0+(2633890159/5000000000 : ℝ)*X 0 1+(134761543/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664081409/1250000000 : ℝ)*X 1 0+(-798937/3906250 : ℝ)*X 1 1+(5390461833/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312651581/10000000000 : ℝ)*X 2 0+(1078092363/2000000000 : ℝ)*X 2 1+(-1022639163/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((869308149/2000000000 : ℝ)*X 0 0+(447346997/1000000000 : ℝ)*X 0 1+(4223110823/10000000000 : ℝ)*X 0 2+(869308149/2000000000 : ℝ)*X 1 0+(447346997/1000000000 : ℝ)*X 1 1+(4223110823/10000000000 : ℝ)*X 1 2+(869308149/2000000000 : ℝ)*X 2 0+(447346997/1000000000 : ℝ)*X 2 1+(4223110823/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2205287398947836951719052009/441500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9953179/1000000000000 : ℝ)*(base19) + (915006507/100000000000000 : ℝ)*(base23) + (30492931/100000000000000 : ℝ)*(upper3) + (68091739/50000000000000 : ℝ)*(upper4) + (95730029/50000000000000 : ℝ)*(upper5) + (6041956101744373/100000000000000 : ℝ)*(major0) + (6041956101744373/100000000000000 : ℝ)*(major1) + (6041956101744373/100000000000000 : ℝ)*(major2) + (8109843706449507/100000000000000 : ℝ)*(sp0) + (8109881035155937/100000000000000 : ℝ)*(sp1) + (810988111546733/10000000000000 : ℝ)*(sp2) + (3974022405129037/100000000000000 : ℝ)*(sp3) + (38324024329/100000000000000 : ℝ)*(sp4) + (1520277249/20000000000000 : ℝ)*(sp7) + (3974030006515281/100000000000000 : ℝ)*(f.failure) + (8109882030473837/100000000000000 : ℝ)*(f.sum) + (86535026752169/13245000000000000000000000000 : ℝ)*base66 + (55409507860208047991/2649000000000000000000000000000000 : ℝ)*base67 + (35591718591560047991/2649000000000000000000000000000000 : ℝ)*base69 + (17455265161509952009/2649000000000000000000000000000000 : ℝ)*base72 + (23456732545891/13245000000000000000000000000 : ℝ)*base73 + (48919890924026047991/2649000000000000000000000000000000 : ℝ)*base75 + (26959864258667047991/2649000000000000000000000000000000 : ℝ)*base77 + (3565109290959952009/2649000000000000000000000000000000 : ℝ)*base80 + (623253530047/6622500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (15986281/2500000000000000000000 : ℝ)*base90 + (15986281/2500000000000000000000 : ℝ)*base92 + (15986281/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (791709660764294968354607571/220750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (455704459/100000000000000 : ℝ)*(base19) + (87035611/6250000000000 : ℝ)*(base23) + (47945929/100000000000000 : ℝ)*(upper3) + (123203587/100000000000000 : ℝ)*(lower4) + (3036367666174887/50000000000000 : ℝ)*(major0) + (3036367666174887/50000000000000 : ℝ)*(major1) + (3036367666174887/50000000000000 : ℝ)*(major2) + (20669414823/100000000000000 : ℝ)*(sp1) + (59571914217/100000000000000 : ℝ)*(sp2) + (4752848473/100000000000000 : ℝ)*(sp3) + (2037798959770241/25000000000000 : ℝ)*(sp4) + (4075587356980841/50000000000000 : ℝ)*(sp5) + (8151134874596971/100000000000000 : ℝ)*(sp6) + (998567488305411/25000000000000 : ℝ)*(sp7) + (998568676517529/25000000000000 : ℝ)*(f.failure) + (2037798959770241/25000000000000 : ℝ)*(f.sum) + (3694930507143/2207500000000000000000000000 : ℝ)*base65 + (1115388939826014143/441500000000000000000000000000000 : ℝ)*base67 + (2948587620295485857/441500000000000000000000000000000 : ℝ)*base70 + (2059747335215514143/441500000000000000000000000000000 : ℝ)*base71 + (9618094598169/4415000000000000000000000000 : ℝ)*base74 + (14068939158861485857/441500000000000000000000000000000 : ℝ)*base76 + (2190099738693514143/441500000000000000000000000000000 : ℝ)*base77 + (74104596465014143/441500000000000000000000000000000 : ℝ)*base79 + (1314841651559/275937500000000000000000000 : ℝ)*base82 + (4256529/625000000000000000000 : ℝ)*base90 + (4256529/625000000000000000000 : ℝ)*base92 + (4256529/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1272_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14143/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5747/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1439/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1272_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1272_s7_0 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2105772603/10000000000 : ℝ)*x 0 + (5390605271/10000000000 : ℝ)*x 1 + (5267627823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105772603/10000000000 : ℝ)^4233 ≤ (3202214150277/25000000000000 : ℝ)^3209 := by
    have hnat : (2105772603 : ℕ)^4233*25000000000000^3209 ≤ 3202214150277^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105772603 10000000000 3202214150277 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390605271/10000000000 : ℝ)^4233 ≤ (44259080860109/100000000000000 : ℝ)^3209 := by
    have hnat : (5390605271 : ℕ)^4233*100000000000000^3209 ≤ 44259080860109^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390605271 10000000000 44259080860109 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267627823/10000000000 : ℝ)^4233 ≤ (42932062522793/100000000000000 : ℝ)^3209 := by
    have hnat : (5267627823 : ℕ)^4233*100000000000000^3209 ≤ 42932062522793^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267627823 10000000000 42932062522793 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2105772603/10000000000 : ℝ), (5390605271/10000000000 : ℝ), (5267627823/10000000000 : ℝ)] ![(3202214150277/25000000000000 : ℝ), (44259080860109/100000000000000 : ℝ), (42932062522793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2105772603/10000000000 : ℝ)|^4233 ≤ (3202214150277/25000000000000 : ℝ)^3209
        have hw : |(-2105772603/10000000000 : ℝ)|=(2105772603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390605271/10000000000 : ℝ)|^4233 ≤ (44259080860109/100000000000000 : ℝ)^3209
        have hw : |(5390605271/10000000000 : ℝ)|=(5390605271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267627823/10000000000 : ℝ)|^4233 ≤ (42932062522793/100000000000000 : ℝ)^3209
        have hw : |(5267627823/10000000000 : ℝ)|=(5267627823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s7_1 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344135633/10000000000 : ℝ)*x 0 + (-271014731/1250000000 : ℝ)*x 1 + (164613369/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344135633/10000000000 : ℝ)^4233 ≤ (8751298186381/20000000000000 : ℝ)^3209 := by
    have hnat : (5344135633 : ℕ)^4233*20000000000000^3209 ≤ 8751298186381^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344135633 10000000000 8751298186381 20000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271014731/1250000000 : ℝ)^4233 ≤ (6655723344817/50000000000000 : ℝ)^3209 := by
    have hnat : (271014731 : ℕ)^4233*50000000000000^3209 ≤ 6655723344817^3209*1250000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271014731 1250000000 6655723344817 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164613369/312500000 : ℝ)^4233 ≤ (42932062361529/100000000000000 : ℝ)^3209 := by
    have hnat : (164613369 : ℕ)^4233*100000000000000^3209 ≤ 42932062361529^3209*312500000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164613369 312500000 42932062361529 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344135633/10000000000 : ℝ), (-271014731/1250000000 : ℝ), (164613369/312500000 : ℝ)] ![(8751298186381/20000000000000 : ℝ), (6655723344817/50000000000000 : ℝ), (42932062361529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344135633/10000000000 : ℝ)|^4233 ≤ (8751298186381/20000000000000 : ℝ)^3209
        have hw : |(5344135633/10000000000 : ℝ)|=(5344135633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-271014731/1250000000 : ℝ)|^4233 ≤ (6655723344817/50000000000000 : ℝ)^3209
        have hw : |(-271014731/1250000000 : ℝ)|=(271014731/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164613369/312500000 : ℝ)|^4233 ≤ (42932062361529/100000000000000 : ℝ)^3209
        have hw : |(164613369/312500000 : ℝ)|=(164613369/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s7_2 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672067703/5000000000 : ℝ)*x 0 + (5267628179/10000000000 : ℝ)*x 1 + (-2168117659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672067703/5000000000 : ℝ)^4233 ≤ (43756488480193/100000000000000 : ℝ)^3209 := by
    have hnat : (2672067703 : ℕ)^4233*100000000000000^3209 ≤ 43756488480193^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672067703 5000000000 43756488480193 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267628179/10000000000 : ℝ)^4233 ≤ (42932066350117/100000000000000 : ℝ)^3209 := by
    have hnat : (5267628179 : ℕ)^4233*100000000000000^3209 ≤ 42932066350117^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267628179 10000000000 42932066350117 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2168117659/10000000000 : ℝ)^4233 ≤ (166393064487/1250000000000 : ℝ)^3209 := by
    have hnat : (2168117659 : ℕ)^4233*1250000000000^3209 ≤ 166393064487^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168117659 10000000000 166393064487 1250000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672067703/5000000000 : ℝ), (5267628179/10000000000 : ℝ), (-2168117659/10000000000 : ℝ)] ![(43756488480193/100000000000000 : ℝ), (42932066350117/100000000000000 : ℝ), (166393064487/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672067703/5000000000 : ℝ)|^4233 ≤ (43756488480193/100000000000000 : ℝ)^3209
        have hw : |(2672067703/5000000000 : ℝ)|=(2672067703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267628179/10000000000 : ℝ)|^4233 ≤ (42932066350117/100000000000000 : ℝ)^3209
        have hw : |(5267628179/10000000000 : ℝ)|=(5267628179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2168117659/10000000000 : ℝ)|^4233 ≤ (166393064487/1250000000000 : ℝ)^3209
        have hw : |(-2168117659/10000000000 : ℝ)|=(2168117659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s7_3 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (869307983/2000000000 : ℝ)*x 0 + (4222807181/10000000000 : ℝ)*x 1 + (4473768899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869307983/2000000000 : ℝ)^4233 ≤ (16658826647437/50000000000000 : ℝ)^3209 := by
    have hnat : (869307983 : ℕ)^4233*50000000000000^3209 ≤ 16658826647437^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869307983 2000000000 16658826647437 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222807181/10000000000 : ℝ)^4233 ≤ (1603613375711/5000000000000 : ℝ)^3209 := by
    have hnat : (4222807181 : ℕ)^4233*5000000000000^3209 ≤ 1603613375711^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222807181 10000000000 1603613375711 5000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4473768899/10000000000 : ℝ)^4233 ≤ (8652519794239/25000000000000 : ℝ)^3209 := by
    have hnat : (4473768899 : ℕ)^4233*25000000000000^3209 ≤ 8652519794239^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473768899 10000000000 8652519794239 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869307983/2000000000 : ℝ), (4222807181/10000000000 : ℝ), (4473768899/10000000000 : ℝ)] ![(16658826647437/50000000000000 : ℝ), (1603613375711/5000000000000 : ℝ), (8652519794239/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869307983/2000000000 : ℝ)|^4233 ≤ (16658826647437/50000000000000 : ℝ)^3209
        have hw : |(869307983/2000000000 : ℝ)|=(869307983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222807181/10000000000 : ℝ)|^4233 ≤ (1603613375711/5000000000000 : ℝ)^3209
        have hw : |(4222807181/10000000000 : ℝ)|=(4222807181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4473768899/10000000000 : ℝ)|^4233 ≤ (8652519794239/25000000000000 : ℝ)^3209
        have hw : |(4473768899/10000000000 : ℝ)|=(4473768899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s7_4 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2105777287/10000000000 : ℝ)*x 0 + (2633969353/5000000000 : ℝ)*x 1 + (5390293193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105777287/10000000000 : ℝ)^4233 ≤ (3202223546093/25000000000000 : ℝ)^3209 := by
    have hnat : (2105777287 : ℕ)^4233*25000000000000^3209 ≤ 3202223546093^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105777287 10000000000 3202223546093 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633969353/5000000000 : ℝ)^4233 ≤ (42935404829383/100000000000000 : ℝ)^3209 := by
    have hnat : (2633969353 : ℕ)^4233*100000000000000^3209 ≤ 42935404829383^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633969353 5000000000 42935404829383 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390293193/10000000000 : ℝ)^4233 ≤ (44255700970213/100000000000000 : ℝ)^3209 := by
    have hnat : (5390293193 : ℕ)^4233*100000000000000^3209 ≤ 44255700970213^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390293193 10000000000 44255700970213 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2105777287/10000000000 : ℝ), (2633969353/5000000000 : ℝ), (5390293193/10000000000 : ℝ)] ![(3202223546093/25000000000000 : ℝ), (42935404829383/100000000000000 : ℝ), (44255700970213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2105777287/10000000000 : ℝ)|^4233 ≤ (3202223546093/25000000000000 : ℝ)^3209
        have hw : |(-2105777287/10000000000 : ℝ)|=(2105777287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633969353/5000000000 : ℝ)|^4233 ≤ (42935404829383/100000000000000 : ℝ)^3209
        have hw : |(2633969353/5000000000 : ℝ)|=(2633969353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390293193/10000000000 : ℝ)|^4233 ≤ (44255700970213/100000000000000 : ℝ)^3209
        have hw : |(5390293193/10000000000 : ℝ)|=(5390293193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s7_5 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312691853/10000000000 : ℝ)*x 0 + (-31960201/156250000 : ℝ)*x 1 + (2695146807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312691853/10000000000 : ℝ)^4233 ≤ (5427150232091/12500000000000 : ℝ)^3209 := by
    have hnat : (5312691853 : ℕ)^4233*12500000000000^3209 ≤ 5427150232091^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312691853 10000000000 5427150232091 12500000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (31960201/156250000 : ℝ)^4233 ≤ (6163546295337/50000000000000 : ℝ)^3209 := by
    have hnat : (31960201 : ℕ)^4233*50000000000000^3209 ≤ 6163546295337^3209*156250000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31960201 156250000 6163546295337 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695146807/5000000000 : ℝ)^4233 ≤ (11063926382429/25000000000000 : ℝ)^3209 := by
    have hnat : (2695146807 : ℕ)^4233*25000000000000^3209 ≤ 11063926382429^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695146807 5000000000 11063926382429 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312691853/10000000000 : ℝ), (-31960201/156250000 : ℝ), (2695146807/5000000000 : ℝ)] ![(5427150232091/12500000000000 : ℝ), (6163546295337/50000000000000 : ℝ), (11063926382429/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312691853/10000000000 : ℝ)|^4233 ≤ (5427150232091/12500000000000 : ℝ)^3209
        have hw : |(5312691853/10000000000 : ℝ)|=(5312691853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-31960201/156250000 : ℝ)|^4233 ≤ (6163546295337/50000000000000 : ℝ)^3209
        have hw : |(-31960201/156250000 : ℝ)|=(31960201/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695146807/5000000000 : ℝ)|^4233 ≤ (11063926382429/25000000000000 : ℝ)^3209
        have hw : |(2695146807/5000000000 : ℝ)|=(2695146807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s7_6 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656345589/5000000000 : ℝ)*x 0 + (5390294549/10000000000 : ℝ)*x 1 + (-2045452507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656345589/5000000000 : ℝ)^4233 ≤ (43417194580111/100000000000000 : ℝ)^3209 := by
    have hnat : (2656345589 : ℕ)^4233*100000000000000^3209 ≤ 43417194580111^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656345589 5000000000 43417194580111 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390294549/10000000000 : ℝ)^4233 ≤ (5531964456991/12500000000000 : ℝ)^3209 := by
    have hnat : (5390294549 : ℕ)^4233*12500000000000^3209 ≤ 5531964456991^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390294549 10000000000 5531964456991 12500000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2045452507/10000000000 : ℝ)^4233 ≤ (6163544876319/50000000000000 : ℝ)^3209 := by
    have hnat : (2045452507 : ℕ)^4233*50000000000000^3209 ≤ 6163544876319^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045452507 10000000000 6163544876319 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656345589/5000000000 : ℝ), (5390294549/10000000000 : ℝ), (-2045452507/10000000000 : ℝ)] ![(43417194580111/100000000000000 : ℝ), (5531964456991/12500000000000 : ℝ), (6163544876319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656345589/5000000000 : ℝ)|^4233 ≤ (43417194580111/100000000000000 : ℝ)^3209
        have hw : |(2656345589/5000000000 : ℝ)|=(2656345589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390294549/10000000000 : ℝ)|^4233 ≤ (5531964456991/12500000000000 : ℝ)^3209
        have hw : |(5390294549/10000000000 : ℝ)|=(5390294549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2045452507/10000000000 : ℝ)|^4233 ≤ (6163544876319/50000000000000 : ℝ)^3209
        have hw : |(-2045452507/10000000000 : ℝ)|=(2045452507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s7_7 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (543318739/1250000000 : ℝ)*x 0 + (4473135457/10000000000 : ℝ)*x 1 + (4223442281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543318739/1250000000 : ℝ)^4233 ≤ (3331775437811/10000000000000 : ℝ)^3209 := by
    have hnat : (543318739 : ℕ)^4233*10000000000000^3209 ≤ 3331775437811^3209*1250000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543318739 1250000000 3331775437811 10000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4473135457/10000000000 : ℝ)^4233 ≤ (34603615127921/100000000000000 : ℝ)^3209 := by
    have hnat : (4473135457 : ℕ)^4233*100000000000000^3209 ≤ 34603615127921^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473135457 10000000000 34603615127921 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4223442281/10000000000 : ℝ)^4233 ≤ (32078630478707/100000000000000 : ℝ)^3209 := by
    have hnat : (4223442281 : ℕ)^4233*100000000000000^3209 ≤ 32078630478707^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223442281 10000000000 32078630478707 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543318739/1250000000 : ℝ), (4473135457/10000000000 : ℝ), (4223442281/10000000000 : ℝ)] ![(3331775437811/10000000000000 : ℝ), (34603615127921/100000000000000 : ℝ), (32078630478707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543318739/1250000000 : ℝ)|^4233 ≤ (3331775437811/10000000000000 : ℝ)^3209
        have hw : |(543318739/1250000000 : ℝ)|=(543318739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4473135457/10000000000 : ℝ)|^4233 ≤ (34603615127921/100000000000000 : ℝ)^3209
        have hw : |(4473135457/10000000000 : ℝ)|=(4473135457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4223442281/10000000000 : ℝ)|^4233 ≤ (32078630478707/100000000000000 : ℝ)^3209
        have hw : |(4223442281/10000000000 : ℝ)|=(4223442281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1272_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1439/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2303/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14121/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3531/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1439/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3531/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1439/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3531/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1439/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3531/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1439/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3531/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1439/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3531/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1439/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1439/12500 : ℝ) ^ (8465/2048 : ℝ) ≤ (13165998138000261/100000000000000000000 : ℝ) := by
    have hpowers : (1439/12500 : ℝ)^8465 ≤ (13165998138000261/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1439 : ℕ)^8465*100000000000000000000^2048 ≤ 13165998138000261^2048*12500^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1439 12500 13165998138000261 100000000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1439/12500 : ℝ)) (X := (13165998138000261/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3531/25000 : ℝ) ^ (8465/2048 : ℝ) ≤ (30656285647546599/100000000000000000000 : ℝ) := by
    have hpowers : (3531/25000 : ℝ)^8465 ≤ (30656285647546599/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3531 : ℕ)^8465*100000000000000000000^2048 ≤ 30656285647546599^2048*25000^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3531 25000 30656285647546599 100000000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3531/25000 : ℝ)) (X := (30656285647546599/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013165998138000261/50000000000000000000 : ℝ) ≤ (312519906433419/312500000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (50013165998138000261/50000000000000000000 : ℝ)^2048 ≤ (312519906433419/312500000000000 : ℝ)^8465 := by
      have hnat : (50013165998138000261 : ℕ)^2048*312500000000000^8465 ≤ 312519906433419^8465*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013165998138000261 50000000000000000000 312519906433419 312500000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312519906433419/312500000000000 : ℝ)) (X := (50013165998138000261/50000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002191114189277343/5000000000000000000 : ℝ) ≤ (2500265012208669/2500000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (5002191114189277343/5000000000000000000 : ℝ)^2048 ≤ (2500265012208669/2500000000000000 : ℝ)^8465 := by
      have hnat : (5002191114189277343 : ℕ)^2048*2500000000000000^8465 ≤ 2500265012208669^8465*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002191114189277343 5000000000000000000 2500265012208669 2500000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500265012208669/2500000000000000 : ℝ)) (X := (5002191114189277343/5000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030656285647546599/50000000000000000000 : ℝ) ≤ (1250185386474993/1250000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (50030656285647546599/50000000000000000000 : ℝ)^2048 ≤ (1250185386474993/1250000000000000 : ℝ)^8465 := by
      have hnat : (50030656285647546599 : ℕ)^2048*1250000000000000^8465 ≤ 1250185386474993^8465*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030656285647546599 50000000000000000000 1250185386474993 1250000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250185386474993/1250000000000000 : ℝ)) (X := (50030656285647546599/50000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13165998138000261/100000000000000000000 : ℝ) ≤ ((407998808095290051/408125000000000000 : ℝ)+2*(105760741317/65300000000000 : ℝ)*(1439/12500 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (407998808095290051/408125000000000000 : ℝ)+2*(105760741317/65300000000000 : ℝ)*(1439/12500 : ℝ)=(312519906433419/312500000000000 : ℝ) by norm_num, show 1+2*(13165998138000261/100000000000000000000 : ℝ)=(50013165998138000261/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30656285647546599/100000000000000000000 : ℝ)+(13165998138000261/100000000000000000000 : ℝ) ≤ ((407998808095290051/408125000000000000 : ℝ)+(105760741317/65300000000000 : ℝ)*((3531/25000 : ℝ)+(1439/12500 : ℝ)))^(8465/2048 : ℝ) := by
    rw [show (407998808095290051/408125000000000000 : ℝ)+(105760741317/65300000000000 : ℝ)*((3531/25000 : ℝ)+(1439/12500 : ℝ))=(2500265012208669/2500000000000000 : ℝ) by norm_num, show 1+(30656285647546599/100000000000000000000 : ℝ)+(13165998138000261/100000000000000000000 : ℝ)=(5002191114189277343/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30656285647546599/100000000000000000000 : ℝ) ≤ ((407998808095290051/408125000000000000 : ℝ)+2*(105760741317/65300000000000 : ℝ)*(3531/25000 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (407998808095290051/408125000000000000 : ℝ)+2*(105760741317/65300000000000 : ℝ)*(3531/25000 : ℝ)=(1250185386474993/1250000000000000 : ℝ) by norm_num, show 1+2*(30656285647546599/100000000000000000000 : ℝ)=(50030656285647546599/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (407998808095290051/408125000000000000 : ℝ)*(X 1 0+X 2 0)+(105760741317/65300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (1439/12500 : ℝ)) (hi := (3531/25000 : ℝ)) (c := (407998808095290051/408125000000000000 : ℝ)) (alpha := (105760741317/65300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (407998808095290051/408125000000000000 : ℝ)*(X 0 1+X 2 1)+(105760741317/65300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (1439/12500 : ℝ)) (hi := (3531/25000 : ℝ)) (c := (407998808095290051/408125000000000000 : ℝ)) (alpha := (105760741317/65300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (407998808095290051/408125000000000000 : ℝ)*(X 0 2+X 1 2)+(105760741317/65300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (1439/12500 : ℝ)) (hi := (3531/25000 : ℝ)) (c := (407998808095290051/408125000000000000 : ℝ)) (alpha := (105760741317/65300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2105772603/10000000000 : ℝ)*X 0 0+(5390605271/10000000000 : ℝ)*X 0 1+(5267627823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344135633/10000000000 : ℝ)*X 1 0+(-271014731/1250000000 : ℝ)*X 1 1+(164613369/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672067703/5000000000 : ℝ)*X 2 0+(5267628179/10000000000 : ℝ)*X 2 1+(-2168117659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869307983/2000000000 : ℝ)*X 0 0+(4222807181/10000000000 : ℝ)*X 0 1+(4473768899/10000000000 : ℝ)*X 0 2+(869307983/2000000000 : ℝ)*X 1 0+(4222807181/10000000000 : ℝ)*X 1 1+(4473768899/10000000000 : ℝ)*X 1 2+(869307983/2000000000 : ℝ)*X 2 0+(4222807181/10000000000 : ℝ)*X 2 1+(4473768899/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2105777287/10000000000 : ℝ)*X 0 0+(2633969353/5000000000 : ℝ)*X 0 1+(5390293193/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312691853/10000000000 : ℝ)*X 1 0+(-31960201/156250000 : ℝ)*X 1 1+(2695146807/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656345589/5000000000 : ℝ)*X 2 0+(5390294549/10000000000 : ℝ)*X 2 1+(-2045452507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543318739/1250000000 : ℝ)*X 0 0+(4473135457/10000000000 : ℝ)*X 0 1+(4223442281/10000000000 : ℝ)*X 0 2+(543318739/1250000000 : ℝ)*X 1 0+(4473135457/10000000000 : ℝ)*X 1 1+(4223442281/10000000000 : ℝ)*X 1 2+(543318739/1250000000 : ℝ)*X 2 0+(4473135457/10000000000 : ℝ)*X 2 1+(4223442281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22289540288666950863411/3265000000000000000000000000 : ℝ) := by norm_num
    linear_combination (604279053/25000000000000 : ℝ)*(base19) + (204456921/10000000000000 : ℝ)*(base23) + (14504109/100000000000000 : ℝ)*(lower2) + (76138939/50000000000000 : ℝ)*(upper3) + (385137333/100000000000000 : ℝ)*(upper5) + (3029113872813431/50000000000000 : ℝ)*(major0) + (3029113872813431/50000000000000 : ℝ)*(major1) + (3029113872813431/50000000000000 : ℝ)*(major2) + (4065821460045059/50000000000000 : ℝ)*(sp0) + (406586017285571/5000000000000 : ℝ)*(sp1) + (8131720718258423/100000000000000 : ℝ)*(sp2) + (3984705107220451/100000000000000 : ℝ)*(sp3) + (39921368757/50000000000000 : ℝ)*(sp4) + (684841131/2500000000000 : ℝ)*(sp7) + (3984732500865691/100000000000000 : ℝ)*(f.failure) + (8131722762827633/100000000000000 : ℝ)*(f.sum) + (16080975963091/3265000000000000000000000000 : ℝ)*base66 + (146904541810387519/20406250000000000000000000000000 : ℝ)*base68 + (155709410807137519/20406250000000000000000000000000 : ℝ)*base70 + (559566215611612481/20406250000000000000000000000000 : ℝ)*base71 + (17384266920761/3265000000000000000000000000 : ℝ)*base74 + (128119650294987481/20406250000000000000000000000000 : ℝ)*base75 + (138075205976174981/20406250000000000000000000000000 : ℝ)*base77 + (22717672257731269/20406250000000000000000000000000 : ℝ)*base80 + (1709024891863/1632500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1646691/2500000000000000000000 : ℝ)*base90 + (1646691/2500000000000000000000 : ℝ)*base92 + (1646691/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (66058310983425871822167123/5101562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1218077891/100000000000000 : ℝ)*(base19) + (1815607/400000000000 : ℝ)*(base23) + (116315461/100000000000000 : ℝ)*(lower2) + (226394629/25000000000000 : ℝ)*(upper3) + (7282701/6250000000000 : ℝ)*(lower4) + (221198083/100000000000000 : ℝ)*(upper5) + (3044464050754143/50000000000000 : ℝ)*(major0) + (3044464050754143/50000000000000 : ℝ)*(major1) + (3044464050754143/50000000000000 : ℝ)*(major2) + (23133305059/50000000000000 : ℝ)*(sp2) + (4086465224977311/50000000000000 : ℝ)*(sp4) + (8172929231876731/100000000000000 : ℝ)*(sp5) + (4086441864721377/50000000000000 : ℝ)*(sp6) + (2002462660720257/50000000000000 : ℝ)*(sp7) + (2002462660720257/50000000000000 : ℝ)*(f.failure) + (4086465224977311/50000000000000 : ℝ)*(f.sum) + (1639436782919/408125000000000000000000000 : ℝ)*base65 + (42271337677312543/20406250000000000000000000000000 : ℝ)*base67 + (139454951369500043/20406250000000000000000000000000 : ℝ)*base69 + (103674229275593707/20406250000000000000000000000000 : ℝ)*base72 + (2202131205613/816250000000000000000000000 : ℝ)*base73 + (298235823695625043/20406250000000000000000000000000 : ℝ)*base75 + (74074750956249957/20406250000000000000000000000000 : ℝ)*base78 + (187162570483312543/20406250000000000000000000000000 : ℝ)*base79 + (4734941014063/816250000000000000000000000 : ℝ)*base81 + (12592743/1250000000000000000000 : ℝ)*base89 + (12592743/1250000000000000000000 : ℝ)*base91 + (12592743/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1272_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3531/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1439/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2303/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1272_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1272_s8_0 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-526443587/2500000000 : ℝ)*x 0 + (5390578023/10000000000 : ℝ)*x 1 + (526765397/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526443587/2500000000 : ℝ)^4233 ≤ (3202217650639/25000000000000 : ℝ)^3209 := by
    have hnat : (526443587 : ℕ)^4233*25000000000000^3209 ≤ 3202217650639^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526443587 2500000000 3202217650639 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390578023/10000000000 : ℝ)^4233 ≤ (22129392877173/50000000000000 : ℝ)^3209 := by
    have hnat : (5390578023 : ℕ)^4233*50000000000000^3209 ≤ 22129392877173^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390578023 10000000000 22129392877173 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526765397/1000000000 : ℝ)^4233 ≤ (2683271476691/6250000000000 : ℝ)^3209 := by
    have hnat : (526765397 : ℕ)^4233*6250000000000^3209 ≤ 2683271476691^3209*1000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526765397 1000000000 2683271476691 6250000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-526443587/2500000000 : ℝ), (5390578023/10000000000 : ℝ), (526765397/1000000000 : ℝ)] ![(3202217650639/25000000000000 : ℝ), (22129392877173/50000000000000 : ℝ), (2683271476691/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-526443587/2500000000 : ℝ)|^4233 ≤ (3202217650639/25000000000000 : ℝ)^3209
        have hw : |(-526443587/2500000000 : ℝ)|=(526443587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390578023/10000000000 : ℝ)|^4233 ≤ (22129392877173/50000000000000 : ℝ)^3209
        have hw : |(5390578023/10000000000 : ℝ)|=(5390578023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526765397/1000000000 : ℝ)|^4233 ≤ (2683271476691/6250000000000 : ℝ)^3209
        have hw : |(526765397/1000000000 : ℝ)|=(526765397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s8_1 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344128651/10000000000 : ℝ)*x 0 + (-2168092481/10000000000 : ℝ)*x 1 + (1316913483/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344128651/10000000000 : ℝ)^4233 ≤ (43756415522881/100000000000000 : ℝ)^3209 := by
    have hnat : (5344128651 : ℕ)^4233*100000000000000^3209 ≤ 43756415522881^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344128651 10000000000 43756415522881 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2168092481/10000000000 : ℝ)^4233 ≤ (332781031191/2500000000000 : ℝ)^3209 := by
    have hnat : (2168092481 : ℕ)^4233*2500000000000^3209 ≤ 332781031191^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168092481 10000000000 332781031191 2500000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316913483/2500000000 : ℝ)^4233 ≤ (42932343218521/100000000000000 : ℝ)^3209 := by
    have hnat : (1316913483 : ℕ)^4233*100000000000000^3209 ≤ 42932343218521^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316913483 2500000000 42932343218521 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344128651/10000000000 : ℝ), (-2168092481/10000000000 : ℝ), (1316913483/2500000000 : ℝ)] ![(43756415522881/100000000000000 : ℝ), (332781031191/2500000000000 : ℝ), (42932343218521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344128651/10000000000 : ℝ)|^4233 ≤ (43756415522881/100000000000000 : ℝ)^3209
        have hw : |(5344128651/10000000000 : ℝ)|=(5344128651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2168092481/10000000000 : ℝ)|^4233 ≤ (332781031191/2500000000000 : ℝ)^3209
        have hw : |(-2168092481/10000000000 : ℝ)|=(2168092481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316913483/2500000000 : ℝ)|^4233 ≤ (42932343218521/100000000000000 : ℝ)^3209
        have hw : |(1316913483/2500000000 : ℝ)|=(1316913483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s8_2 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344128621/10000000000 : ℝ)*x 0 + (5267653957/10000000000 : ℝ)*x 1 + (-271011561/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344128621/10000000000 : ℝ)^4233 ≤ (21878207599433/50000000000000 : ℝ)^3209 := by
    have hnat : (5344128621 : ℕ)^4233*50000000000000^3209 ≤ 21878207599433^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344128621 10000000000 21878207599433 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267653957/10000000000 : ℝ)^4233 ≤ (21466171743647/50000000000000 : ℝ)^3209 := by
    have hnat : (5267653957 : ℕ)^4233*50000000000000^3209 ≤ 21466171743647^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267653957 10000000000 21466171743647 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271011561/1250000000 : ℝ)^4233 ≤ (13311241304331/100000000000000 : ℝ)^3209 := by
    have hnat : (271011561 : ℕ)^4233*100000000000000^3209 ≤ 13311241304331^3209*1250000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271011561 1250000000 13311241304331 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344128621/10000000000 : ℝ), (5267653957/10000000000 : ℝ), (-271011561/1250000000 : ℝ)] ![(21878207599433/50000000000000 : ℝ), (21466171743647/50000000000000 : ℝ), (13311241304331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344128621/10000000000 : ℝ)|^4233 ≤ (21878207599433/50000000000000 : ℝ)^3209
        have hw : |(5344128621/10000000000 : ℝ)|=(5344128621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267653957/10000000000 : ℝ)|^4233 ≤ (21466171743647/50000000000000 : ℝ)^3209
        have hw : |(5267653957/10000000000 : ℝ)|=(5267653957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-271011561/1250000000 : ℝ)|^4233 ≤ (13311241304331/100000000000000 : ℝ)^3209
        have hw : |(-271011561/1250000000 : ℝ)|=(271011561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s8_3 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4346540933/10000000000 : ℝ)*x 0 + (2111430587/5000000000 : ℝ)*x 1 + (2236857441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4346540933/10000000000 : ℝ)^4233 ≤ (4164707948529/12500000000000 : ℝ)^3209 := by
    have hnat : (4346540933 : ℕ)^4233*12500000000000^3209 ≤ 4164707948529^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346540933 10000000000 4164707948529 12500000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111430587/5000000000 : ℝ)^4233 ≤ (1002275264047/3125000000000 : ℝ)^3209 := by
    have hnat : (2111430587 : ℕ)^4233*3125000000000^3209 ≤ 1002275264047^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111430587 5000000000 1002275264047 3125000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2236857441/5000000000 : ℝ)^4233 ≤ (34609527941401/100000000000000 : ℝ)^3209 := by
    have hnat : (2236857441 : ℕ)^4233*100000000000000^3209 ≤ 34609527941401^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236857441 5000000000 34609527941401 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4346540933/10000000000 : ℝ), (2111430587/5000000000 : ℝ), (2236857441/5000000000 : ℝ)] ![(4164707948529/12500000000000 : ℝ), (1002275264047/3125000000000 : ℝ), (34609527941401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4346540933/10000000000 : ℝ)|^4233 ≤ (4164707948529/12500000000000 : ℝ)^3209
        have hw : |(4346540933/10000000000 : ℝ)|=(4346540933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2111430587/5000000000 : ℝ)|^4233 ≤ (1002275264047/3125000000000 : ℝ)^3209
        have hw : |(2111430587/5000000000 : ℝ)|=(2111430587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2236857441/5000000000 : ℝ)|^4233 ≤ (34609527941401/100000000000000 : ℝ)^3209
        have hw : |(2236857441/5000000000 : ℝ)|=(2236857441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s8_4 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-105288947/500000000 : ℝ)*x 0 + (5267964117/10000000000 : ℝ)*x 1 + (5390266743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105288947/500000000 : ℝ)^4233 ≤ (12808907447643/100000000000000 : ℝ)^3209 := by
    have hnat : (105288947 : ℕ)^4233*100000000000000^3209 ≤ 12808907447643^3209*500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105288947 500000000 12808907447643 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267964117/10000000000 : ℝ)^4233 ≤ (42935678026109/100000000000000 : ℝ)^3209 := by
    have hnat : (5267964117 : ℕ)^4233*100000000000000^3209 ≤ 42935678026109^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267964117 10000000000 42935678026109 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390266743/10000000000 : ℝ)^4233 ≤ (22127707256183/50000000000000 : ℝ)^3209 := by
    have hnat : (5390266743 : ℕ)^4233*50000000000000^3209 ≤ 22127707256183^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390266743 10000000000 22127707256183 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-105288947/500000000 : ℝ), (5267964117/10000000000 : ℝ), (5390266743/10000000000 : ℝ)] ![(12808907447643/100000000000000 : ℝ), (42935678026109/100000000000000 : ℝ), (22127707256183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-105288947/500000000 : ℝ)|^4233 ≤ (12808907447643/100000000000000 : ℝ)^3209
        have hw : |(-105288947/500000000 : ℝ)|=(105288947/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267964117/10000000000 : ℝ)|^4233 ≤ (42935678026109/100000000000000 : ℝ)^3209
        have hw : |(5267964117/10000000000 : ℝ)|=(5267964117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390266743/10000000000 : ℝ)|^4233 ≤ (22127707256183/50000000000000 : ℝ)^3209
        have hw : |(5390266743/10000000000 : ℝ)|=(5390266743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s8_5 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132817477/250000000 : ℝ)*x 0 + (-204547969/1000000000 : ℝ)*x 1 + (539026673/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132817477/250000000 : ℝ)^4233 ≤ (43417279765059/100000000000000 : ℝ)^3209 := by
    have hnat : (132817477 : ℕ)^4233*100000000000000^3209 ≤ 43417279765059^3209*250000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132817477 250000000 43417279765059 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (204547969/1000000000 : ℝ)^4233 ≤ (12327305849279/100000000000000 : ℝ)^3209 := by
    have hnat : (204547969 : ℕ)^4233*100000000000000^3209 ≤ 12327305849279^3209*1000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204547969 1000000000 12327305849279 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539026673/1000000000 : ℝ)^4233 ≤ (22127707185787/50000000000000 : ℝ)^3209 := by
    have hnat : (539026673 : ℕ)^4233*50000000000000^3209 ≤ 22127707185787^3209*1000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539026673 1000000000 22127707185787 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132817477/250000000 : ℝ), (-204547969/1000000000 : ℝ), (539026673/1000000000 : ℝ)] ![(43417279765059/100000000000000 : ℝ), (12327305849279/100000000000000 : ℝ), (22127707185787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132817477/250000000 : ℝ)|^4233 ≤ (43417279765059/100000000000000 : ℝ)^3209
        have hw : |(132817477/250000000 : ℝ)|=(132817477/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-204547969/1000000000 : ℝ)|^4233 ≤ (12327305849279/100000000000000 : ℝ)^3209
        have hw : |(-204547969/1000000000 : ℝ)|=(204547969/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539026673/1000000000 : ℝ)|^4233 ≤ (22127707185787/50000000000000 : ℝ)^3209
        have hw : |(539026673/1000000000 : ℝ)|=(539026673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s8_6 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062539817/2000000000 : ℝ)*x 0 + (5390266723/10000000000 : ℝ)*x 1 + (-511369923/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062539817/2000000000 : ℝ)^4233 ≤ (542715997737/1250000000000 : ℝ)^3209 := by
    have hnat : (1062539817 : ℕ)^4233*1250000000000^3209 ≤ 542715997737^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062539817 2000000000 542715997737 1250000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390266723/10000000000 : ℝ)^4233 ≤ (44255414295763/100000000000000 : ℝ)^3209 := by
    have hnat : (5390266723 : ℕ)^4233*100000000000000^3209 ≤ 44255414295763^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390266723 10000000000 44255414295763 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (511369923/2500000000 : ℝ)^4233 ≤ (6163652932589/50000000000000 : ℝ)^3209 := by
    have hnat : (511369923 : ℕ)^4233*50000000000000^3209 ≤ 6163652932589^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511369923 2500000000 6163652932589 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062539817/2000000000 : ℝ), (5390266723/10000000000 : ℝ), (-511369923/2500000000 : ℝ)] ![(542715997737/1250000000000 : ℝ), (44255414295763/100000000000000 : ℝ), (6163652932589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062539817/2000000000 : ℝ)|^4233 ≤ (542715997737/1250000000000 : ℝ)^3209
        have hw : |(1062539817/2000000000 : ℝ)|=(1062539817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390266723/10000000000 : ℝ)|^4233 ≤ (44255414295763/100000000000000 : ℝ)^3209
        have hw : |(5390266723/10000000000 : ℝ)|=(5390266723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-511369923/2500000000 : ℝ)|^4233 ≤ (6163652932589/50000000000000 : ℝ)^3209
        have hw : |(-511369923/2500000000 : ℝ)|=(511369923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_s8_7 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2173275161/5000000000 : ℝ)*x 0 + (2236540923/5000000000 : ℝ)*x 1 + (4223496471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173275161/5000000000 : ℝ)^4233 ≤ (4164719815471/12500000000000 : ℝ)^3209 := by
    have hnat : (2173275161 : ℕ)^4233*12500000000000^3209 ≤ 4164719815471^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173275161 5000000000 4164719815471 12500000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2236540923/5000000000 : ℝ)^4233 ≤ (4325383507531/12500000000000 : ℝ)^3209 := by
    have hnat : (2236540923 : ℕ)^4233*12500000000000^3209 ≤ 4325383507531^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236540923 5000000000 4325383507531 12500000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4223496471/10000000000 : ℝ)^4233 ≤ (8019793353429/25000000000000 : ℝ)^3209 := by
    have hnat : (4223496471 : ℕ)^4233*25000000000000^3209 ≤ 8019793353429^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223496471 10000000000 8019793353429 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173275161/5000000000 : ℝ), (2236540923/5000000000 : ℝ), (4223496471/10000000000 : ℝ)] ![(4164719815471/12500000000000 : ℝ), (4325383507531/12500000000000 : ℝ), (8019793353429/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173275161/5000000000 : ℝ)|^4233 ≤ (4164719815471/12500000000000 : ℝ)^3209
        have hw : |(2173275161/5000000000 : ℝ)|=(2173275161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2236540923/5000000000 : ℝ)|^4233 ≤ (4325383507531/12500000000000 : ℝ)^3209
        have hw : |(2236540923/5000000000 : ℝ)|=(2236540923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4223496471/10000000000 : ℝ)|^4233 ≤ (8019793353429/25000000000000 : ℝ)^3209
        have hw : |(4223496471/10000000000 : ℝ)|=(4223496471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1272_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2303/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2879/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (353/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2303/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2303/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2303/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2303/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2303/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2303/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2303/20000 : ℝ) ^ (8465/2048 : ℝ) ≤ (3295046349904459/25000000000000000000 : ℝ) := by
    have hpowers : (2303/20000 : ℝ)^8465 ≤ (3295046349904459/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2303 : ℕ)^8465*25000000000000000000^2048 ≤ 3295046349904459^2048*20000^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2303 20000 3295046349904459 25000000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2303/20000 : ℝ)) (X := (3295046349904459/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14121/100000 : ℝ) ^ (8465/2048 : ℝ) ≤ (30629380488078027/100000000000000000000 : ℝ) := by
    have hpowers : (14121/100000 : ℝ)^8465 ≤ (30629380488078027/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14121 : ℕ)^8465*100000000000000000000^2048 ≤ 30629380488078027^2048*100000^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14121 100000 30629380488078027 100000000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14121/100000 : ℝ)) (X := (30629380488078027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503295046349904459/12500000000000000000 : ℝ) ≤ (5000318846109071/5000000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (12503295046349904459/12500000000000000000 : ℝ)^2048 ≤ (5000318846109071/5000000000000000 : ℝ)^8465 := by
      have hnat : (12503295046349904459 : ℕ)^2048*5000000000000000^8465 ≤ 5000318846109071^8465*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503295046349904459 12500000000000000000 5000318846109071 5000000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000318846109071/5000000000000000 : ℝ)) (X := (12503295046349904459/12500000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043809565887695863/100000000000000000000 : ℝ) ≤ (5000529870621669/5000000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (100043809565887695863/100000000000000000000 : ℝ)^2048 ≤ (5000529870621669/5000000000000000 : ℝ)^8465 := by
      have hnat : (100043809565887695863 : ℕ)^2048*5000000000000000^8465 ≤ 5000529870621669^8465*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043809565887695863 100000000000000000000 5000529870621669 5000000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000529870621669/5000000000000000 : ℝ)) (X := (100043809565887695863/100000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030629380488078027/50000000000000000000 : ℝ) ≤ (5000740895134267/5000000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (50030629380488078027/50000000000000000000 : ℝ)^2048 ≤ (5000740895134267/5000000000000000 : ℝ)^8465 := by
      have hnat : (50030629380488078027 : ℕ)^2048*5000000000000000^8465 ≤ 5000740895134267^8465*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030629380488078027 50000000000000000000 5000740895134267 5000000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000740895134267/5000000000000000 : ℝ)) (X := (50030629380488078027/50000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3295046349904459/25000000000000000000 : ℝ) ≤ ((6512985509217553543/6515000000000000000 : ℝ)+2*(105512256299/65150000000000 : ℝ)*(2303/20000 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (6512985509217553543/6515000000000000000 : ℝ)+2*(105512256299/65150000000000 : ℝ)*(2303/20000 : ℝ)=(5000318846109071/5000000000000000 : ℝ) by norm_num, show 1+2*(3295046349904459/25000000000000000000 : ℝ)=(12503295046349904459/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30629380488078027/100000000000000000000 : ℝ)+(3295046349904459/25000000000000000000 : ℝ) ≤ ((6512985509217553543/6515000000000000000 : ℝ)+(105512256299/65150000000000 : ℝ)*((14121/100000 : ℝ)+(2303/20000 : ℝ)))^(8465/2048 : ℝ) := by
    rw [show (6512985509217553543/6515000000000000000 : ℝ)+(105512256299/65150000000000 : ℝ)*((14121/100000 : ℝ)+(2303/20000 : ℝ))=(5000529870621669/5000000000000000 : ℝ) by norm_num, show 1+(30629380488078027/100000000000000000000 : ℝ)+(3295046349904459/25000000000000000000 : ℝ)=(100043809565887695863/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30629380488078027/100000000000000000000 : ℝ) ≤ ((6512985509217553543/6515000000000000000 : ℝ)+2*(105512256299/65150000000000 : ℝ)*(14121/100000 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (6512985509217553543/6515000000000000000 : ℝ)+2*(105512256299/65150000000000 : ℝ)*(14121/100000 : ℝ)=(5000740895134267/5000000000000000 : ℝ) by norm_num, show 1+2*(30629380488078027/100000000000000000000 : ℝ)=(50030629380488078027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6512985509217553543/6515000000000000000 : ℝ)*(X 1 0+X 2 0)+(105512256299/65150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (2303/20000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (6512985509217553543/6515000000000000000 : ℝ)) (alpha := (105512256299/65150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6512985509217553543/6515000000000000000 : ℝ)*(X 0 1+X 2 1)+(105512256299/65150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (2303/20000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (6512985509217553543/6515000000000000000 : ℝ)) (alpha := (105512256299/65150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6512985509217553543/6515000000000000000 : ℝ)*(X 0 2+X 1 2)+(105512256299/65150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (2303/20000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (6512985509217553543/6515000000000000000 : ℝ)) (alpha := (105512256299/65150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-526443587/2500000000 : ℝ)*X 0 0+(5390578023/10000000000 : ℝ)*X 0 1+(526765397/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344128651/10000000000 : ℝ)*X 1 0+(-2168092481/10000000000 : ℝ)*X 1 1+(1316913483/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344128621/10000000000 : ℝ)*X 2 0+(5267653957/10000000000 : ℝ)*X 2 1+(-271011561/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4346540933/10000000000 : ℝ)*X 0 0+(2111430587/5000000000 : ℝ)*X 0 1+(2236857441/5000000000 : ℝ)*X 0 2+(4346540933/10000000000 : ℝ)*X 1 0+(2111430587/5000000000 : ℝ)*X 1 1+(2236857441/5000000000 : ℝ)*X 1 2+(4346540933/10000000000 : ℝ)*X 2 0+(2111430587/5000000000 : ℝ)*X 2 1+(2236857441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-105288947/500000000 : ℝ)*X 0 0+(5267964117/10000000000 : ℝ)*X 0 1+(5390266743/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132817477/250000000 : ℝ)*X 1 0+(-204547969/1000000000 : ℝ)*X 1 1+(539026673/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062539817/2000000000 : ℝ)*X 2 0+(5390266723/10000000000 : ℝ)*X 2 1+(-511369923/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2173275161/5000000000 : ℝ)*X 0 0+(2236540923/5000000000 : ℝ)*X 0 1+(4223496471/10000000000 : ℝ)*X 0 2+(2173275161/5000000000 : ℝ)*X 1 0+(2236540923/5000000000 : ℝ)*X 1 1+(4223496471/10000000000 : ℝ)*X 1 2+(2173275161/5000000000 : ℝ)*X 2 0+(2236540923/5000000000 : ℝ)*X 2 1+(4223496471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30882996844912987720749/6515000000000000000000000000 : ℝ) := by norm_num
    linear_combination (225777029/25000000000000 : ℝ)*(base19) + (824869541/100000000000000 : ℝ)*(base23) + (3481249/20000000000000 : ℝ)*(lower2) + (11058901/10000000000000 : ℝ)*(upper3) + (67108713/100000000000000 : ℝ)*(upper5) + (6060783302689509/100000000000000 : ℝ)*(major0) + (6060783302689509/100000000000000 : ℝ)*(major1) + (6060783302689509/100000000000000 : ℝ)*(major2) + (4067564870695999/50000000000000 : ℝ)*(sp0) + (2033788038478863/25000000000000 : ℝ)*(sp1) + (8135152232154027/100000000000000 : ℝ)*(sp2) + (1993199912311823/50000000000000 : ℝ)*(sp3) + (2331563157/10000000000000 : ℝ)*(sp4) + (13565722091/100000000000000 : ℝ)*(sp7) + (3986413390345737/100000000000000 : ℝ)*(f.failure) + (508447066063973/6250000000000 : ℝ)*(f.sum) + (8562890775821/3257500000000000000000000000 : ℝ)*base65 + (5360248121320019613/651500000000000000000000000000000 : ℝ)*base68 + (5092851016076480387/651500000000000000000000000000000 : ℝ)*base69 + (4993692225377019613/651500000000000000000000000000000 : ℝ)*base72 + (1147508367643/407187500000000000000000000 : ℝ)*base74 + (15177713541935480387/651500000000000000000000000000000 : ℝ)*base75 + (632741147399519613/651500000000000000000000000000000 : ℝ)*base78 + (14731489900137480387/651500000000000000000000000000000 : ℝ)*base79 + (18978455092027/6515000000000000000000000000 : ℝ)*base81 + (2287263/2500000000000000000000 : ℝ)*base89 + (2287263/2500000000000000000000 : ℝ)*base91 + (2287263/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (434918274521036580940418187/81437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41084609/4000000000000 : ℝ)*(base19) + (54741723/5000000000000 : ℝ)*(base23) + (356240727/100000000000000 : ℝ)*(lower1) + (53301331/50000000000000 : ℝ)*(upper3) + (28754543/100000000000000 : ℝ)*(lower4) + (118180271/100000000000000 : ℝ)*(upper5) + (1522880064249703/25000000000000 : ℝ)*(major0) + (1522880064249703/25000000000000 : ℝ)*(major1) + (1522880064249703/25000000000000 : ℝ)*(major2) + (498643083/50000000000000 : ℝ)*(sp2) + (8176410052847439/100000000000000 : ℝ)*(sp4) + (4088204512866107/50000000000000 : ℝ)*(sp5) + (8176407960726813/100000000000000 : ℝ)*(sp6) + (2003315141566479/50000000000000 : ℝ)*(sp7) + (2003315141566479/50000000000000 : ℝ)*(f.failure) + (8176410052847439/100000000000000 : ℝ)*(f.sum) + (118264357427/203593750000000000000000000 : ℝ)*base66 + (4989878589655077271/162875000000000000000000000000000 : ℝ)*base68 + (49128263391577271/162875000000000000000000000000000 : ℝ)*base70 + (30853964194754452271/162875000000000000000000000000000 : ℝ)*base72 + (181742743429/101796875000000000000000000 : ℝ)*base73 + (720013490020202271/162875000000000000000000000000000 : ℝ)*base76 + (1922372096181422729/162875000000000000000000000000000 : ℝ)*base77 + (1969500390808172729/162875000000000000000000000000000 : ℝ)*base79 + (1984485856683/3257500000000000000000000000 : ℝ)*base81 + (8744521/1250000000000000000000 : ℝ)*base89 + (8744521/1250000000000000000000 : ℝ)*base91 + (8744521/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1272_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2303/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2879/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (353/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1272_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1272_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14143/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5747/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2879/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (353/2500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1272_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1272_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1272_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14143/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5747/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2879/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (353/2500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1272_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1209_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:06:24.586382+00:00
-- url     : https://prove2.me/submissions/dc19f0a7-4828-48ce-8d3b-73a47db9f5c4

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
theorem support_rectangle_w1209_s6_0 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-533807071/2500000000 : ℝ)*x 0 + (53920483/100000000 : ℝ)*x 1 + (5266535277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533807071/2500000000 : ℝ)^4201 ≤ (1298114647997/10000000000000 : ℝ)^3177 := by
    have hnat : (533807071 : ℕ)^4201*10000000000000^3177 ≤ 1298114647997^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533807071 2500000000 1298114647997 10000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53920483/100000000 : ℝ)^4201 ≤ (44186901476187/100000000000000 : ℝ)^3177 := by
    have hnat : (53920483 : ℕ)^4201*100000000000000^3177 ≤ 44186901476187^3177*100000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53920483 100000000 44186901476187 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266535277/10000000000 : ℝ)^4201 ≤ (42831952028053/100000000000000 : ℝ)^3177 := by
    have hnat : (5266535277 : ℕ)^4201*100000000000000^3177 ≤ 42831952028053^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266535277 10000000000 42831952028053 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-533807071/2500000000 : ℝ), (53920483/100000000 : ℝ), (5266535277/10000000000 : ℝ)] ![(1298114647997/10000000000000 : ℝ), (44186901476187/100000000000000 : ℝ), (42831952028053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-533807071/2500000000 : ℝ)|^4201 ≤ (1298114647997/10000000000000 : ℝ)^3177
        have hw : |(-533807071/2500000000 : ℝ)|=(533807071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53920483/100000000 : ℝ)|^4201 ≤ (44186901476187/100000000000000 : ℝ)^3177
        have hw : |(53920483/100000000 : ℝ)|=(53920483/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266535277/10000000000 : ℝ)|^4201 ≤ (42831952028053/100000000000000 : ℝ)^3177
        have hw : |(5266535277/10000000000 : ℝ)|=(5266535277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s6_1 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133613389/250000000 : ℝ)*x 0 + (-219887739/1000000000 : ℝ)*x 1 + (5266535593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133613389/250000000 : ℝ)^4201 ≤ (8734555722473/20000000000000 : ℝ)^3177 := by
    have hnat : (133613389 : ℕ)^4201*20000000000000^3177 ≤ 8734555722473^3177*250000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133613389 250000000 8734555722473 20000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219887739/1000000000 : ℝ)^4201 ≤ (13495265944293/100000000000000 : ℝ)^3177 := by
    have hnat : (219887739 : ℕ)^4201*100000000000000^3177 ≤ 13495265944293^3177*1000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219887739 1000000000 13495265944293 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266535593/10000000000 : ℝ)^4201 ≤ (42831955426383/100000000000000 : ℝ)^3177 := by
    have hnat : (5266535593 : ℕ)^4201*100000000000000^3177 ≤ 42831955426383^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266535593 10000000000 42831955426383 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133613389/250000000 : ℝ), (-219887739/1000000000 : ℝ), (5266535593/10000000000 : ℝ)] ![(8734555722473/20000000000000 : ℝ), (13495265944293/100000000000000 : ℝ), (42831955426383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133613389/250000000 : ℝ)|^4201 ≤ (8734555722473/20000000000000 : ℝ)^3177
        have hw : |(133613389/250000000 : ℝ)|=(133613389/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219887739/1000000000 : ℝ)|^4201 ≤ (13495265944293/100000000000000 : ℝ)^3177
        have hw : |(-219887739/1000000000 : ℝ)|=(219887739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266535593/10000000000 : ℝ)|^4201 ≤ (42831955426383/100000000000000 : ℝ)^3177
        have hw : |(5266535593/10000000000 : ℝ)|=(5266535593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s6_2 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668066959/1250000000 : ℝ)*x 0 + (2633267697/5000000000 : ℝ)*x 1 + (-439775501/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668066959/1250000000 : ℝ)^4201 ≤ (43672779822557/100000000000000 : ℝ)^3177 := by
    have hnat : (668066959 : ℕ)^4201*100000000000000^3177 ≤ 43672779822557^3177*1250000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668066959 1250000000 43672779822557 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633267697/5000000000 : ℝ)^4201 ≤ (5353994160787/12500000000000 : ℝ)^3177 := by
    have hnat : (2633267697 : ℕ)^4201*12500000000000^3177 ≤ 5353994160787^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633267697 5000000000 5353994160787 12500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (439775501/2000000000 : ℝ)^4201 ≤ (1686908359697/12500000000000 : ℝ)^3177 := by
    have hnat : (439775501 : ℕ)^4201*12500000000000^3177 ≤ 1686908359697^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439775501 2000000000 1686908359697 12500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668066959/1250000000 : ℝ), (2633267697/5000000000 : ℝ), (-439775501/2000000000 : ℝ)] ![(43672779822557/100000000000000 : ℝ), (5353994160787/12500000000000 : ℝ), (1686908359697/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668066959/1250000000 : ℝ)|^4201 ≤ (43672779822557/100000000000000 : ℝ)^3177
        have hw : |(668066959/1250000000 : ℝ)|=(668066959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633267697/5000000000 : ℝ)|^4201 ≤ (5353994160787/12500000000000 : ℝ)^3177
        have hw : |(2633267697/5000000000 : ℝ)|=(2633267697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-439775501/2000000000 : ℝ)|^4201 ≤ (1686908359697/12500000000000 : ℝ)^3177
        have hw : |(-439775501/2000000000 : ℝ)|=(439775501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s6_3 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (136103357/312500000 : ℝ)*x 0 + (846122329/2000000000 : ℝ)*x 1 + (2241801063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136103357/312500000 : ℝ)^4201 ≤ (33317205621747/100000000000000 : ℝ)^3177 := by
    have hnat : (136103357 : ℕ)^4201*100000000000000^3177 ≤ 33317205621747^3177*312500000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136103357 312500000 33317205621747 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846122329/2000000000 : ℝ)^4201 ≤ (32061709763247/100000000000000 : ℝ)^3177 := by
    have hnat : (846122329 : ℕ)^4201*100000000000000^3177 ≤ 32061709763247^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846122329 2000000000 32061709763247 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241801063/5000000000 : ℝ)^4201 ≤ (34621084598847/100000000000000 : ℝ)^3177 := by
    have hnat : (2241801063 : ℕ)^4201*100000000000000^3177 ≤ 34621084598847^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241801063 5000000000 34621084598847 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136103357/312500000 : ℝ), (846122329/2000000000 : ℝ), (2241801063/5000000000 : ℝ)] ![(33317205621747/100000000000000 : ℝ), (32061709763247/100000000000000 : ℝ), (34621084598847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136103357/312500000 : ℝ)|^4201 ≤ (33317205621747/100000000000000 : ℝ)^3177
        have hw : |(136103357/312500000 : ℝ)|=(136103357/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846122329/2000000000 : ℝ)|^4201 ≤ (32061709763247/100000000000000 : ℝ)^3177
        have hw : |(846122329/2000000000 : ℝ)|=(846122329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2241801063/5000000000 : ℝ)|^4201 ≤ (34621084598847/100000000000000 : ℝ)^3177
        have hw : |(2241801063/5000000000 : ℝ)|=(2241801063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s6_4 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-427046593/2000000000 : ℝ)*x 0 + (263342633/500000000 : ℝ)*x 1 + (2695864919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427046593/2000000000 : ℝ)^4201 ≤ (12981184110731/100000000000000 : ℝ)^3177 := by
    have hnat : (427046593 : ℕ)^4201*100000000000000^3177 ≤ 12981184110731^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427046593 2000000000 12981184110731 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263342633/500000000 : ℝ)^4201 ≤ (171341461053/400000000000 : ℝ)^3177 := by
    have hnat : (263342633 : ℕ)^4201*400000000000^3177 ≤ 171341461053^3177*500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263342633 500000000 171341461053 400000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695864919/5000000000 : ℝ)^4201 ≤ (44183450605179/100000000000000 : ℝ)^3177 := by
    have hnat : (2695864919 : ℕ)^4201*100000000000000^3177 ≤ 44183450605179^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695864919 5000000000 44183450605179 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-427046593/2000000000 : ℝ), (263342633/500000000 : ℝ), (2695864919/5000000000 : ℝ)] ![(12981184110731/100000000000000 : ℝ), (171341461053/400000000000 : ℝ), (44183450605179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-427046593/2000000000 : ℝ)|^4201 ≤ (12981184110731/100000000000000 : ℝ)^3177
        have hw : |(-427046593/2000000000 : ℝ)|=(427046593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263342633/500000000 : ℝ)|^4201 ≤ (171341461053/400000000000 : ℝ)^3177
        have hw : |(263342633/500000000 : ℝ)|=(263342633/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695864919/5000000000 : ℝ)|^4201 ≤ (44183450605179/100000000000000 : ℝ)^3177
        have hw : |(2695864919/5000000000 : ℝ)|=(2695864919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s6_5 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312582939/10000000000 : ℝ)*x 0 + (-32401297/156250000 : ℝ)*x 1 + (1078345967/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312582939/10000000000 : ℝ)^4201 ≤ (21663927232749/50000000000000 : ℝ)^3177 := by
    have hnat : (5312582939 : ℕ)^4201*50000000000000^3177 ≤ 21663927232749^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312582939 10000000000 21663927232749 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32401297/156250000 : ℝ)^4201 ≤ (6244347476001/50000000000000 : ℝ)^3177 := by
    have hnat : (32401297 : ℕ)^4201*50000000000000^3177 ≤ 6244347476001^3177*156250000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32401297 156250000 6244347476001 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078345967/2000000000 : ℝ)^4201 ≤ (44183450572671/100000000000000 : ℝ)^3177 := by
    have hnat : (1078345967 : ℕ)^4201*100000000000000^3177 ≤ 44183450572671^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078345967 2000000000 44183450572671 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312582939/10000000000 : ℝ), (-32401297/156250000 : ℝ), (1078345967/2000000000 : ℝ)] ![(21663927232749/50000000000000 : ℝ), (6244347476001/50000000000000 : ℝ), (44183450572671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312582939/10000000000 : ℝ)|^4201 ≤ (21663927232749/50000000000000 : ℝ)^3177
        have hw : |(5312582939/10000000000 : ℝ)|=(5312582939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32401297/156250000 : ℝ)|^4201 ≤ (6244347476001/50000000000000 : ℝ)^3177
        have hw : |(-32401297/156250000 : ℝ)|=(32401297/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078345967/2000000000 : ℝ)|^4201 ≤ (44183450572671/100000000000000 : ℝ)^3177
        have hw : |(1078345967/2000000000 : ℝ)|=(1078345967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s6_6 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312582939/10000000000 : ℝ)*x 0 + (1078345967/2000000000 : ℝ)*x 1 + (-32401297/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312582939/10000000000 : ℝ)^4201 ≤ (21663927232749/50000000000000 : ℝ)^3177 := by
    have hnat : (5312582939 : ℕ)^4201*50000000000000^3177 ≤ 21663927232749^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312582939 10000000000 21663927232749 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078345967/2000000000 : ℝ)^4201 ≤ (44183450572671/100000000000000 : ℝ)^3177 := by
    have hnat : (1078345967 : ℕ)^4201*100000000000000^3177 ≤ 44183450572671^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078345967 2000000000 44183450572671 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32401297/156250000 : ℝ)^4201 ≤ (6244347476001/50000000000000 : ℝ)^3177 := by
    have hnat : (32401297 : ℕ)^4201*50000000000000^3177 ≤ 6244347476001^3177*156250000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32401297 156250000 6244347476001 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312582939/10000000000 : ℝ), (1078345967/2000000000 : ℝ), (-32401297/156250000 : ℝ)] ![(21663927232749/50000000000000 : ℝ), (44183450572671/100000000000000 : ℝ), (6244347476001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312582939/10000000000 : ℝ)|^4201 ≤ (21663927232749/50000000000000 : ℝ)^3177
        have hw : |(5312582939/10000000000 : ℝ)|=(5312582939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078345967/2000000000 : ℝ)|^4201 ≤ (44183450572671/100000000000000 : ℝ)^3177
        have hw : |(1078345967/2000000000 : ℝ)|=(1078345967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-32401297/156250000 : ℝ)|^4201 ≤ (6244347476001/50000000000000 : ℝ)^3177
        have hw : |(-32401297/156250000 : ℝ)|=(32401297/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s6_7 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4355316941/10000000000 : ℝ)*x 0 + (4482962607/10000000000 : ℝ)*x 1 + (4231253611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355316941/10000000000 : ℝ)^4201 ≤ (33317301890521/100000000000000 : ℝ)^3177 := by
    have hnat : (4355316941 : ℕ)^4201*100000000000000^3177 ≤ 33317301890521^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355316941 10000000000 33317301890521 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4482962607/10000000000 : ℝ)^4201 ≤ (34614554909233/100000000000000 : ℝ)^3177 := by
    have hnat : (4482962607 : ℕ)^4201*100000000000000^3177 ≤ 34614554909233^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482962607 10000000000 34614554909233 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231253611/10000000000 : ℝ)^4201 ≤ (16034071589603/50000000000000 : ℝ)^3177 := by
    have hnat : (4231253611 : ℕ)^4201*50000000000000^3177 ≤ 16034071589603^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231253611 10000000000 16034071589603 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355316941/10000000000 : ℝ), (4482962607/10000000000 : ℝ), (4231253611/10000000000 : ℝ)] ![(33317301890521/100000000000000 : ℝ), (34614554909233/100000000000000 : ℝ), (16034071589603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355316941/10000000000 : ℝ)|^4201 ≤ (33317301890521/100000000000000 : ℝ)^3177
        have hw : |(4355316941/10000000000 : ℝ)|=(4355316941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4482962607/10000000000 : ℝ)|^4201 ≤ (34614554909233/100000000000000 : ℝ)^3177
        have hw : |(4482962607/10000000000 : ℝ)|=(4482962607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231253611/10000000000 : ℝ)|^4201 ≤ (16034071589603/50000000000000 : ℝ)^3177
        have hw : |(4231253611/10000000000 : ℝ)|=(4231253611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1209_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11433/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3523/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14117/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1141/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14117/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1141/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14117/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1141/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14117/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1141/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14117/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1141/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14117/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1141/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1141/10000 : ℝ) ^ (8401/2048 : ℝ) ≤ (13581190505980057/100000000000000000000 : ℝ) := by
    have hpowers : (1141/10000 : ℝ)^8401 ≤ (13581190505980057/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1141 : ℕ)^8401*100000000000000000000^2048 ≤ 13581190505980057^2048*10000^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1141 10000 13581190505980057 100000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1141/10000 : ℝ)) (X := (13581190505980057/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14117/100000 : ℝ) ^ (8401/2048 : ℝ) ≤ (16261859793606891/50000000000000000000 : ℝ) := by
    have hpowers : (14117/100000 : ℝ)^8401 ≤ (16261859793606891/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14117 : ℕ)^8401*50000000000000000000^2048 ≤ 16261859793606891^2048*100000^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14117 100000 16261859793606891 50000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14117/100000 : ℝ)) (X := (16261859793606891/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013581190505980057/50000000000000000000 : ℝ) ≤ (5000331048946359/5000000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (50013581190505980057/50000000000000000000 : ℝ)^2048 ≤ (5000331048946359/5000000000000000 : ℝ)^8401 := by
      have hnat : (50013581190505980057 : ℕ)^2048*5000000000000000^8401 ≤ 5000331048946359^8401*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013581190505980057 50000000000000000000 5000331048946359 5000000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000331048946359/5000000000000000 : ℝ)) (X := (50013581190505980057/50000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046104910093193839/100000000000000000000 : ℝ) ≤ (2500280937983109/2500000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (100046104910093193839/100000000000000000000 : ℝ)^2048 ≤ (2500280937983109/2500000000000000 : ℝ)^8401 := by
      have hnat : (100046104910093193839 : ℕ)^2048*2500000000000000^8401 ≤ 2500280937983109^8401*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046104910093193839 100000000000000000000 2500280937983109 2500000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500280937983109/2500000000000000 : ℝ)) (X := (100046104910093193839/100000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016261859793606891/25000000000000000000 : ℝ) ≤ (5000792702986077/5000000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (25016261859793606891/25000000000000000000 : ℝ)^2048 ≤ (5000792702986077/5000000000000000 : ℝ)^8401 := by
      have hnat : (25016261859793606891 : ℕ)^2048*5000000000000000^8401 ≤ 5000792702986077^8401*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016261859793606891 25000000000000000000 5000792702986077 5000000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000792702986077/5000000000000000 : ℝ)) (X := (25016261859793606891/25000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13581190505980057/100000000000000000000 : ℝ) ≤ ((13530628676904611433/13535000000000000000 : ℝ)+2*(230827019859/135350000000000 : ℝ)*(1141/10000 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (13530628676904611433/13535000000000000000 : ℝ)+2*(230827019859/135350000000000 : ℝ)*(1141/10000 : ℝ)=(5000331048946359/5000000000000000 : ℝ) by norm_num, show 1+2*(13581190505980057/100000000000000000000 : ℝ)=(50013581190505980057/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16261859793606891/50000000000000000000 : ℝ)+(13581190505980057/100000000000000000000 : ℝ) ≤ ((13530628676904611433/13535000000000000000 : ℝ)+(230827019859/135350000000000 : ℝ)*((14117/100000 : ℝ)+(1141/10000 : ℝ)))^(8401/2048 : ℝ) := by
    rw [show (13530628676904611433/13535000000000000000 : ℝ)+(230827019859/135350000000000 : ℝ)*((14117/100000 : ℝ)+(1141/10000 : ℝ))=(2500280937983109/2500000000000000 : ℝ) by norm_num, show 1+(16261859793606891/50000000000000000000 : ℝ)+(13581190505980057/100000000000000000000 : ℝ)=(100046104910093193839/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16261859793606891/50000000000000000000 : ℝ) ≤ ((13530628676904611433/13535000000000000000 : ℝ)+2*(230827019859/135350000000000 : ℝ)*(14117/100000 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (13530628676904611433/13535000000000000000 : ℝ)+2*(230827019859/135350000000000 : ℝ)*(14117/100000 : ℝ)=(5000792702986077/5000000000000000 : ℝ) by norm_num, show 1+2*(16261859793606891/50000000000000000000 : ℝ)=(25016261859793606891/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13530628676904611433/13535000000000000000 : ℝ)*(X 1 0+X 2 0)+(230827019859/135350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (1141/10000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (13530628676904611433/13535000000000000000 : ℝ)) (alpha := (230827019859/135350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13530628676904611433/13535000000000000000 : ℝ)*(X 0 1+X 2 1)+(230827019859/135350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (1141/10000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (13530628676904611433/13535000000000000000 : ℝ)) (alpha := (230827019859/135350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13530628676904611433/13535000000000000000 : ℝ)*(X 0 2+X 1 2)+(230827019859/135350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (1141/10000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (13530628676904611433/13535000000000000000 : ℝ)) (alpha := (230827019859/135350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-533807071/2500000000 : ℝ)*X 0 0+(53920483/100000000 : ℝ)*X 0 1+(5266535277/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133613389/250000000 : ℝ)*X 1 0+(-219887739/1000000000 : ℝ)*X 1 1+(5266535593/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668066959/1250000000 : ℝ)*X 2 0+(2633267697/5000000000 : ℝ)*X 2 1+(-439775501/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((136103357/312500000 : ℝ)*X 0 0+(846122329/2000000000 : ℝ)*X 0 1+(2241801063/5000000000 : ℝ)*X 0 2+(136103357/312500000 : ℝ)*X 1 0+(846122329/2000000000 : ℝ)*X 1 1+(2241801063/5000000000 : ℝ)*X 1 2+(136103357/312500000 : ℝ)*X 2 0+(846122329/2000000000 : ℝ)*X 2 1+(2241801063/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-427046593/2000000000 : ℝ)*X 0 0+(263342633/500000000 : ℝ)*X 0 1+(2695864919/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312582939/10000000000 : ℝ)*X 1 0+(-32401297/156250000 : ℝ)*X 1 1+(1078345967/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312582939/10000000000 : ℝ)*X 2 0+(1078345967/2000000000 : ℝ)*X 2 1+(-32401297/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4355316941/10000000000 : ℝ)*X 0 0+(4482962607/10000000000 : ℝ)*X 0 1+(4231253611/10000000000 : ℝ)*X 0 2+(4355316941/10000000000 : ℝ)*X 1 0+(4482962607/10000000000 : ℝ)*X 1 1+(4231253611/10000000000 : ℝ)*X 1 2+(4355316941/10000000000 : ℝ)*X 2 0+(4482962607/10000000000 : ℝ)*X 2 1+(4231253611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2958671883313633215664983279/338375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (396244283/25000000000000 : ℝ)*(base19) + (847433433/50000000000000 : ℝ)*(base23) + (7626013/25000000000000 : ℝ)*(lower2) + (6829483/2000000000000 : ℝ)*(upper3) + (7146429/5000000000000 : ℝ)*(upper5) + (2980046239329007/50000000000000 : ℝ)*(major0) + (2980046239329007/50000000000000 : ℝ)*(major1) + (2980046239329007/50000000000000 : ℝ)*(major2) + (7967360556270209/100000000000000 : ℝ)*(sp0) + (3983705866161361/50000000000000 : ℝ)*(sp1) + (1991852905608247/25000000000000 : ℝ)*(sp2) + (15810967814619/400000000000 : ℝ)*(sp3) + (10552205929/20000000000000 : ℝ)*(sp4) + (1837181409/6250000000000 : ℝ)*(sp7) + (1976385674278647/50000000000000 : ℝ)*(f.failure) + (3983706658649927/50000000000000 : ℝ)*(f.sum) + (30914206969753/13535000000000000000000000000 : ℝ)*base66 + (6706421149294462969/676750000000000000000000000000000 : ℝ)*base68 + (7237574429495212969/676750000000000000000000000000000 : ℝ)*base70 + (11562860268609962969/676750000000000000000000000000000 : ℝ)*base72 + (19420850541911/6767500000000000000000000000 : ℝ)*base73 + (10069051590070462969/676750000000000000000000000000000 : ℝ)*base76 + (5249157428237962969/676750000000000000000000000000000 : ℝ)*base78 + (486396247420462969/676750000000000000000000000000000 : ℝ)*base80 + (265781872997/3383750000000000000000000000 : ℝ)*base82 + (24665669/5000000000000000000000 : ℝ)*base89 + (24665669/5000000000000000000000 : ℝ)*base91 + (24665669/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (77685150213609177542907/13535000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1040336299/100000000000000 : ℝ)*(base19) + (565470509/50000000000000 : ℝ)*(base23) + (114822389/100000000000000 : ℝ)*(upper3) + (41427847/100000000000000 : ℝ)*(lower4) + (59309959/50000000000000 : ℝ)*(upper5) + (5990354432282641/100000000000000 : ℝ)*(major0) + (5990354432282641/100000000000000 : ℝ)*(major1) + (5990354432282641/100000000000000 : ℝ)*(major2) + (14465135079/50000000000000 : ℝ)*(sp1) + (31029100547/100000000000000 : ℝ)*(sp2) + (8007867404017757/100000000000000 : ℝ)*(sp4) + (8007837433411299/100000000000000 : ℝ)*(sp5) + (8007835243976191/100000000000000 : ℝ)*(sp6) + (794568253845669/20000000000000 : ℝ)*(sp7) + (794568253845669/20000000000000 : ℝ)*(f.failure) + (8007867404017757/100000000000000 : ℝ)*(f.sum) + (50856813057331/6767500000000000000000000000 : ℝ)*base66 + (12744325559774565447/1353500000000000000000000000000000 : ℝ)*base68 + (16370430733315565447/1353500000000000000000000000000000 : ℝ)*base70 + (7980086568103065447/1353500000000000000000000000000000 : ℝ)*base72 + (52526451619367/13535000000000000000000000000 : ℝ)*base74 + (739966755158934553/1353500000000000000000000000000000 : ℝ)*base75 + (1670406746774934553/1353500000000000000000000000000000 : ℝ)*base77 + (1248244899334934553/1353500000000000000000000000000000 : ℝ)*base79 + (39798128553941/6767500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4392463/2000000000000000000000 : ℝ)*base89 + (4392463/2000000000000000000000 : ℝ)*base91 + (4392463/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1209_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11433/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1209_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1209_s7_0 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-533812713/2500000000 : ℝ)*x 0 + (1347953763/2500000000 : ℝ)*x 1 + (5266753429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533812713/2500000000 : ℝ)^4201 ≤ (649066395267/5000000000000 : ℝ)^3177 := by
    have hnat : (533812713 : ℕ)^4201*5000000000000^3177 ≤ 649066395267^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533812713 2500000000 649066395267 5000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347953763/2500000000 : ℝ)^4201 ≤ (8836874796427/20000000000000 : ℝ)^3177 := by
    have hnat : (1347953763 : ℕ)^4201*20000000000000^3177 ≤ 8836874796427^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347953763 2500000000 8836874796427 20000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266753429/10000000000 : ℝ)^4201 ≤ (21417149047591/50000000000000 : ℝ)^3177 := by
    have hnat : (5266753429 : ℕ)^4201*50000000000000^3177 ≤ 21417149047591^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266753429 10000000000 21417149047591 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-533812713/2500000000 : ℝ), (1347953763/2500000000 : ℝ), (5266753429/10000000000 : ℝ)] ![(649066395267/5000000000000 : ℝ), (8836874796427/20000000000000 : ℝ), (21417149047591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-533812713/2500000000 : ℝ)|^4201 ≤ (649066395267/5000000000000 : ℝ)^3177
        have hw : |(-533812713/2500000000 : ℝ)|=(533812713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347953763/2500000000 : ℝ)|^4201 ≤ (8836874796427/20000000000000 : ℝ)^3177
        have hw : |(1347953763/2500000000 : ℝ)|=(1347953763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266753429/10000000000 : ℝ)|^4201 ≤ (21417149047591/50000000000000 : ℝ)^3177
        have hw : |(5266753429/10000000000 : ℝ)|=(5266753429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s7_1 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668059493/1250000000 : ℝ)*x 0 + (-2198668091/10000000000 : ℝ)*x 1 + (5266753433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668059493/1250000000 : ℝ)^4201 ≤ (21836067222757/50000000000000 : ℝ)^3177 := by
    have hnat : (668059493 : ℕ)^4201*50000000000000^3177 ≤ 21836067222757^3177*1250000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668059493 1250000000 21836067222757 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2198668091/10000000000 : ℝ)^4201 ≤ (1686695925237/12500000000000 : ℝ)^3177 := by
    have hnat : (2198668091 : ℕ)^4201*12500000000000^3177 ≤ 1686695925237^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198668091 10000000000 1686695925237 12500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266753433/10000000000 : ℝ)^4201 ≤ (214171490691/500000000000 : ℝ)^3177 := by
    have hnat : (5266753433 : ℕ)^4201*500000000000^3177 ≤ 214171490691^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266753433 10000000000 214171490691 500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668059493/1250000000 : ℝ), (-2198668091/10000000000 : ℝ), (5266753433/10000000000 : ℝ)] ![(21836067222757/50000000000000 : ℝ), (1686695925237/12500000000000 : ℝ), (214171490691/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668059493/1250000000 : ℝ)|^4201 ≤ (21836067222757/50000000000000 : ℝ)^3177
        have hw : |(668059493/1250000000 : ℝ)|=(668059493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2198668091/10000000000 : ℝ)|^4201 ≤ (1686695925237/12500000000000 : ℝ)^3177
        have hw : |(-2198668091/10000000000 : ℝ)|=(2198668091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266753433/10000000000 : ℝ)|^4201 ≤ (214171490691/500000000000 : ℝ)^3177
        have hw : |(5266753433/10000000000 : ℝ)|=(5266753433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s7_2 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344475947/10000000000 : ℝ)*x 0 + (526675343/1000000000 : ℝ)*x 1 + (-2198668091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344475947/10000000000 : ℝ)^4201 ≤ (4367213447793/10000000000000 : ℝ)^3177 := by
    have hnat : (5344475947 : ℕ)^4201*10000000000000^3177 ≤ 4367213447793^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344475947 10000000000 4367213447793 10000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526675343/1000000000 : ℝ)^4201 ≤ (42834298105937/100000000000000 : ℝ)^3177 := by
    have hnat : (526675343 : ℕ)^4201*100000000000000^3177 ≤ 42834298105937^3177*1000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526675343 1000000000 42834298105937 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2198668091/10000000000 : ℝ)^4201 ≤ (1686695925237/12500000000000 : ℝ)^3177 := by
    have hnat : (2198668091 : ℕ)^4201*12500000000000^3177 ≤ 1686695925237^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198668091 10000000000 1686695925237 12500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344475947/10000000000 : ℝ), (526675343/1000000000 : ℝ), (-2198668091/10000000000 : ℝ)] ![(4367213447793/10000000000000 : ℝ), (42834298105937/100000000000000 : ℝ), (1686695925237/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344475947/10000000000 : ℝ)|^4201 ≤ (4367213447793/10000000000000 : ℝ)^3177
        have hw : |(5344475947/10000000000 : ℝ)|=(5344475947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526675343/1000000000 : ℝ)|^4201 ≤ (42834298105937/100000000000000 : ℝ)^3177
        have hw : |(526675343/1000000000 : ℝ)|=(526675343/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2198668091/10000000000 : ℝ)|^4201 ≤ (1686695925237/12500000000000 : ℝ)^3177
        have hw : |(-2198668091/10000000000 : ℝ)|=(2198668091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s7_3 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2177659371/5000000000 : ℝ)*x 0 + (4231065093/10000000000 : ℝ)*x 1 + (224157293/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177659371/5000000000 : ℝ)^4201 ≤ (33317320108461/100000000000000 : ℝ)^3177 := by
    have hnat : (2177659371 : ℕ)^4201*100000000000000^3177 ≤ 33317320108461^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177659371 5000000000 33317320108461 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4231065093/10000000000 : ℝ)^4201 ≤ (16033126963519/50000000000000 : ℝ)^3177 := by
    have hnat : (4231065093 : ℕ)^4201*50000000000000^3177 ≤ 16033126963519^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231065093 10000000000 16033126963519 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224157293/500000000 : ℝ)^4201 ≤ (34616425949163/100000000000000 : ℝ)^3177 := by
    have hnat : (224157293 : ℕ)^4201*100000000000000^3177 ≤ 34616425949163^3177*500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224157293 500000000 34616425949163 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177659371/5000000000 : ℝ), (4231065093/10000000000 : ℝ), (224157293/500000000 : ℝ)] ![(33317320108461/100000000000000 : ℝ), (16033126963519/50000000000000 : ℝ), (34616425949163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177659371/5000000000 : ℝ)|^4201 ≤ (33317320108461/100000000000000 : ℝ)^3177
        have hw : |(2177659371/5000000000 : ℝ)|=(2177659371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4231065093/10000000000 : ℝ)|^4201 ≤ (16033126963519/50000000000000 : ℝ)^3177
        have hw : |(4231065093/10000000000 : ℝ)|=(4231065093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224157293/500000000 : ℝ)|^4201 ≤ (34616425949163/100000000000000 : ℝ)^3177
        have hw : |(224157293/500000000 : ℝ)|=(224157293/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s7_4 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2135255577/10000000000 : ℝ)*x 0 + (105341369/200000000 : ℝ)*x 1 + (5391498893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135255577/10000000000 : ℝ)^4201 ≤ (3245341472487/25000000000000 : ℝ)^3177 := by
    have hnat : (2135255577 : ℕ)^4201*25000000000000^3177 ≤ 3245341472487^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135255577 10000000000 3245341472487 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105341369/200000000 : ℝ)^4201 ≤ (42837685973683/100000000000000 : ℝ)^3177 := by
    have hnat : (105341369 : ℕ)^4201*100000000000000^3177 ≤ 42837685973683^3177*200000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105341369 200000000 42837685973683 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391498893/10000000000 : ℝ)^4201 ≤ (5522618514261/12500000000000 : ℝ)^3177 := by
    have hnat : (5391498893 : ℕ)^4201*12500000000000^3177 ≤ 5522618514261^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391498893 10000000000 5522618514261 12500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2135255577/10000000000 : ℝ), (105341369/200000000 : ℝ), (5391498893/10000000000 : ℝ)] ![(3245341472487/25000000000000 : ℝ), (42837685973683/100000000000000 : ℝ), (5522618514261/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2135255577/10000000000 : ℝ)|^4201 ≤ (3245341472487/25000000000000 : ℝ)^3177
        have hw : |(-2135255577/10000000000 : ℝ)|=(2135255577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105341369/200000000 : ℝ)|^4201 ≤ (42837685973683/100000000000000 : ℝ)^3177
        have hw : |(105341369/200000000 : ℝ)|=(105341369/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391498893/10000000000 : ℝ)|^4201 ≤ (5522618514261/12500000000000 : ℝ)^3177
        have hw : |(5391498893/10000000000 : ℝ)|=(5391498893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s7_5 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656319017/5000000000 : ℝ)*x 0 + (-207392263/1000000000 : ℝ)*x 1 + (1347874723/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656319017/5000000000 : ℝ)^4201 ≤ (8665689726859/20000000000000 : ℝ)^3177 := by
    have hnat : (2656319017 : ℕ)^4201*20000000000000^3177 ≤ 8665689726859^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656319017 5000000000 8665689726859 20000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207392263/1000000000 : ℝ)^4201 ≤ (12490603244449/100000000000000 : ℝ)^3177 := by
    have hnat : (207392263 : ℕ)^4201*100000000000000^3177 ≤ 12490603244449^3177*1000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207392263 1000000000 12490603244449 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347874723/2500000000 : ℝ)^4201 ≤ (44180948103253/100000000000000 : ℝ)^3177 := by
    have hnat : (1347874723 : ℕ)^4201*100000000000000^3177 ≤ 44180948103253^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347874723 2500000000 44180948103253 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656319017/5000000000 : ℝ), (-207392263/1000000000 : ℝ), (1347874723/2500000000 : ℝ)] ![(8665689726859/20000000000000 : ℝ), (12490603244449/100000000000000 : ℝ), (44180948103253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656319017/5000000000 : ℝ)|^4201 ≤ (8665689726859/20000000000000 : ℝ)^3177
        have hw : |(2656319017/5000000000 : ℝ)|=(2656319017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-207392263/1000000000 : ℝ)|^4201 ≤ (12490603244449/100000000000000 : ℝ)^3177
        have hw : |(-207392263/1000000000 : ℝ)|=(207392263/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347874723/2500000000 : ℝ)|^4201 ≤ (44180948103253/100000000000000 : ℝ)^3177
        have hw : |(1347874723/2500000000 : ℝ)|=(1347874723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s7_6 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312638037/10000000000 : ℝ)*x 0 + (539149889/1000000000 : ℝ)*x 1 + (-207392263/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312638037/10000000000 : ℝ)^4201 ≤ (5416056083331/12500000000000 : ℝ)^3177 := by
    have hnat : (5312638037 : ℕ)^4201*12500000000000^3177 ≤ 5416056083331^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312638037 10000000000 5416056083331 12500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539149889/1000000000 : ℝ)^4201 ≤ (44180948081581/100000000000000 : ℝ)^3177 := by
    have hnat : (539149889 : ℕ)^4201*100000000000000^3177 ≤ 44180948081581^3177*1000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539149889 1000000000 44180948081581 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207392263/1000000000 : ℝ)^4201 ≤ (12490603244449/100000000000000 : ℝ)^3177 := by
    have hnat : (207392263 : ℕ)^4201*100000000000000^3177 ≤ 12490603244449^3177*1000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207392263 1000000000 12490603244449 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312638037/10000000000 : ℝ), (539149889/1000000000 : ℝ), (-207392263/1000000000 : ℝ)] ![(5416056083331/12500000000000 : ℝ), (44180948081581/100000000000000 : ℝ), (12490603244449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312638037/10000000000 : ℝ)|^4201 ≤ (5416056083331/12500000000000 : ℝ)^3177
        have hw : |(5312638037/10000000000 : ℝ)|=(5312638037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539149889/1000000000 : ℝ)|^4201 ≤ (44180948081581/100000000000000 : ℝ)^3177
        have hw : |(539149889/1000000000 : ℝ)|=(539149889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-207392263/1000000000 : ℝ)|^4201 ≤ (12490603244449/100000000000000 : ℝ)^3177
        have hw : |(-207392263/1000000000 : ℝ)|=(207392263/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s7_7 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2177664137/5000000000 : ℝ)*x 0 + (280156931/625000000 : ℝ)*x 1 + (4231702361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177664137/5000000000 : ℝ)^4201 ≤ (4164677066131/12500000000000 : ℝ)^3177 := by
    have hnat : (2177664137 : ℕ)^4201*12500000000000^3177 ≤ 4164677066131^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177664137 5000000000 4164677066131 12500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280156931/625000000 : ℝ)^4201 ≤ (34609942979137/100000000000000 : ℝ)^3177 := by
    have hnat : (280156931 : ℕ)^4201*100000000000000^3177 ≤ 34609942979137^3177*625000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280156931 625000000 34609942979137 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231702361/10000000000 : ℝ)^4201 ≤ (32072640481789/100000000000000 : ℝ)^3177 := by
    have hnat : (4231702361 : ℕ)^4201*100000000000000^3177 ≤ 32072640481789^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231702361 10000000000 32072640481789 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177664137/5000000000 : ℝ), (280156931/625000000 : ℝ), (4231702361/10000000000 : ℝ)] ![(4164677066131/12500000000000 : ℝ), (34609942979137/100000000000000 : ℝ), (32072640481789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177664137/5000000000 : ℝ)|^4201 ≤ (4164677066131/12500000000000 : ℝ)^3177
        have hw : |(2177664137/5000000000 : ℝ)|=(2177664137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280156931/625000000 : ℝ)|^4201 ≤ (34609942979137/100000000000000 : ℝ)^3177
        have hw : |(280156931/625000000 : ℝ)|=(280156931/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231702361/10000000000 : ℝ)|^4201 ≤ (32072640481789/100000000000000 : ℝ)^3177
        have hw : |(4231702361/10000000000 : ℝ)|=(4231702361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1209_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11433/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5719/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14087/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3523/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11433/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3523/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11433/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3523/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11433/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3523/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11433/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3523/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11433/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3523/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11433/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11433/100000 : ℝ) ^ (8401/2048 : ℝ) ≤ (13693842449797719/100000000000000000000 : ℝ) := by
    have hpowers : (11433/100000 : ℝ)^8401 ≤ (13693842449797719/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11433 : ℕ)^8401*100000000000000000000^2048 ≤ 13693842449797719^2048*100000^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11433 100000 13693842449797719 100000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11433/100000 : ℝ)) (X := (13693842449797719/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3523/25000 : ℝ) ^ (8401/2048 : ℝ) ≤ (32288103041048997/100000000000000000000 : ℝ) := by
    have hpowers : (3523/25000 : ℝ)^8401 ≤ (32288103041048997/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3523 : ℕ)^8401*100000000000000000000^2048 ≤ 32288103041048997^2048*25000^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3523 25000 32288103041048997 100000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3523/25000 : ℝ)) (X := (32288103041048997/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013693842449797719/50000000000000000000 : ℝ) ≤ (1250083448653701/1250000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (50013693842449797719/50000000000000000000 : ℝ)^2048 ≤ (1250083448653701/1250000000000000 : ℝ)^8401 := by
      have hnat : (50013693842449797719 : ℕ)^2048*1250000000000000^8401 ≤ 1250083448653701^8401*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013693842449797719 50000000000000000000 1250083448653701 1250000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250083448653701/1250000000000000 : ℝ)) (X := (50013693842449797719/50000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011495486372711679/25000000000000000000 : ℝ) ≤ (5000560377669253/5000000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (25011495486372711679/25000000000000000000 : ℝ)^2048 ≤ (5000560377669253/5000000000000000 : ℝ)^8401 := by
      have hnat : (25011495486372711679 : ℕ)^2048*5000000000000000^8401 ≤ 5000560377669253^8401*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011495486372711679 25000000000000000000 5000560377669253 5000000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000560377669253/5000000000000000 : ℝ)) (X := (25011495486372711679/25000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032288103041048997/50000000000000000000 : ℝ) ≤ (2500393480361851/2500000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (50032288103041048997/50000000000000000000 : ℝ)^2048 ≤ (2500393480361851/2500000000000000 : ℝ)^8401 := by
      have hnat : (50032288103041048997 : ℕ)^2048*2500000000000000^8401 ≤ 2500393480361851^8401*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032288103041048997 50000000000000000000 2500393480361851 2500000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500393480361851/2500000000000000 : ℝ)) (X := (50032288103041048997/50000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13693842449797719/100000000000000000000 : ℝ) ≤ ((6645353255878866501/6647500000000000000 : ℝ)+2*(226583054449/132950000000000 : ℝ)*(11433/100000 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (6645353255878866501/6647500000000000000 : ℝ)+2*(226583054449/132950000000000 : ℝ)*(11433/100000 : ℝ)=(1250083448653701/1250000000000000 : ℝ) by norm_num, show 1+2*(13693842449797719/100000000000000000000 : ℝ)=(50013693842449797719/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32288103041048997/100000000000000000000 : ℝ)+(13693842449797719/100000000000000000000 : ℝ) ≤ ((6645353255878866501/6647500000000000000 : ℝ)+(226583054449/132950000000000 : ℝ)*((3523/25000 : ℝ)+(11433/100000 : ℝ)))^(8401/2048 : ℝ) := by
    rw [show (6645353255878866501/6647500000000000000 : ℝ)+(226583054449/132950000000000 : ℝ)*((3523/25000 : ℝ)+(11433/100000 : ℝ))=(5000560377669253/5000000000000000 : ℝ) by norm_num, show 1+(32288103041048997/100000000000000000000 : ℝ)+(13693842449797719/100000000000000000000 : ℝ)=(25011495486372711679/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32288103041048997/100000000000000000000 : ℝ) ≤ ((6645353255878866501/6647500000000000000 : ℝ)+2*(226583054449/132950000000000 : ℝ)*(3523/25000 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (6645353255878866501/6647500000000000000 : ℝ)+2*(226583054449/132950000000000 : ℝ)*(3523/25000 : ℝ)=(2500393480361851/2500000000000000 : ℝ) by norm_num, show 1+2*(32288103041048997/100000000000000000000 : ℝ)=(50032288103041048997/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6645353255878866501/6647500000000000000 : ℝ)*(X 1 0+X 2 0)+(226583054449/132950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (11433/100000 : ℝ)) (hi := (3523/25000 : ℝ)) (c := (6645353255878866501/6647500000000000000 : ℝ)) (alpha := (226583054449/132950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6645353255878866501/6647500000000000000 : ℝ)*(X 0 1+X 2 1)+(226583054449/132950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (11433/100000 : ℝ)) (hi := (3523/25000 : ℝ)) (c := (6645353255878866501/6647500000000000000 : ℝ)) (alpha := (226583054449/132950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6645353255878866501/6647500000000000000 : ℝ)*(X 0 2+X 1 2)+(226583054449/132950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (11433/100000 : ℝ)) (hi := (3523/25000 : ℝ)) (c := (6645353255878866501/6647500000000000000 : ℝ)) (alpha := (226583054449/132950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-533812713/2500000000 : ℝ)*X 0 0+(1347953763/2500000000 : ℝ)*X 0 1+(5266753429/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668059493/1250000000 : ℝ)*X 1 0+(-2198668091/10000000000 : ℝ)*X 1 1+(5266753433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344475947/10000000000 : ℝ)*X 2 0+(526675343/1000000000 : ℝ)*X 2 1+(-2198668091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2177659371/5000000000 : ℝ)*X 0 0+(4231065093/10000000000 : ℝ)*X 0 1+(224157293/500000000 : ℝ)*X 0 2+(2177659371/5000000000 : ℝ)*X 1 0+(4231065093/10000000000 : ℝ)*X 1 1+(224157293/500000000 : ℝ)*X 1 2+(2177659371/5000000000 : ℝ)*X 2 0+(4231065093/10000000000 : ℝ)*X 2 1+(224157293/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2135255577/10000000000 : ℝ)*X 0 0+(105341369/200000000 : ℝ)*X 0 1+(5391498893/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656319017/5000000000 : ℝ)*X 1 0+(-207392263/1000000000 : ℝ)*X 1 1+(1347874723/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312638037/10000000000 : ℝ)*X 2 0+(539149889/1000000000 : ℝ)*X 2 1+(-207392263/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177664137/5000000000 : ℝ)*X 0 0+(280156931/625000000 : ℝ)*X 0 1+(4231702361/10000000000 : ℝ)*X 0 2+(2177664137/5000000000 : ℝ)*X 1 0+(280156931/625000000 : ℝ)*X 1 1+(4231702361/10000000000 : ℝ)*X 1 2+(2177664137/5000000000 : ℝ)*X 2 0+(280156931/625000000 : ℝ)*X 2 1+(4231702361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (905772901603110548850737031/166187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106262559/10000000000000 : ℝ)*(base19) + (997575931/100000000000000 : ℝ)*(base23) + (3716447/10000000000000 : ℝ)*(lower2) + (68598361/50000000000000 : ℝ)*(upper3) + (86861837/100000000000000 : ℝ)*(upper5) + (2990782758775177/50000000000000 : ℝ)*(major0) + (2990782758775177/50000000000000 : ℝ)*(major1) + (2990782758775177/50000000000000 : ℝ)*(major2) + (7996088870788127/100000000000000 : ℝ)*(sp0) + (999514673235099/12500000000000 : ℝ)*(sp1) + (7996117450930451/100000000000000 : ℝ)*(sp2) + (991749178866967/25000000000000 : ℝ)*(sp3) + (1848607391/6250000000000 : ℝ)*(sp4) + (15689449547/100000000000000 : ℝ)*(sp7) + (1983506202458707/50000000000000 : ℝ)*(f.failure) + (3998059224253191/50000000000000 : ℝ)*(f.sum) + (35752067229709/6647500000000000000000000000 : ℝ)*base66 + (7867738124490704323/332375000000000000000000000000000 : ℝ)*base68 + (1736193275775954323/332375000000000000000000000000000 : ℝ)*base70 + (1544647738337954323/332375000000000000000000000000000 : ℝ)*base72 + (8322560921561/1661875000000000000000000000 : ℝ)*base74 + (2752487609617170677/332375000000000000000000000000000 : ℝ)*base75 + (1764579319175670677/332375000000000000000000000000000 : ℝ)*base77 + (5895952063119954323/332375000000000000000000000000000 : ℝ)*base80 + (69958386430189/6647500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (483289/5000000000000000000000 : ℝ)*base89 + (483289/5000000000000000000000 : ℝ)*base91 + (483289/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38980863243952369308419721/8309375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41974861/5000000000000 : ℝ)*(base19) + (460471437/50000000000000 : ℝ)*(base23) + (92616021/100000000000000 : ℝ)*(upper3) + (34958631/100000000000000 : ℝ)*(lower4) + (95632077/100000000000000 : ℝ)*(upper5) + (18787066629793/312500000000 : ℝ)*(major0) + (18787066629793/312500000000 : ℝ)*(major1) + (18787066629793/312500000000 : ℝ)*(major2) + (23524920597/100000000000000 : ℝ)*(sp1) + (12688952121/50000000000000 : ℝ)*(sp2) + (25114430347913/312500000000 : ℝ)*(sp4) + (8036593346914343/100000000000000 : ℝ)*(sp5) + (8036591412485043/100000000000000 : ℝ)*(sp6) + (996776193840581/25000000000000 : ℝ)*(sp7) + (996776193840581/25000000000000 : ℝ)*(f.failure) + (25114430347913/312500000000 : ℝ)*(f.sum) + (417639354849/332375000000000000000000000 : ℝ)*base65 + (22410965803335707/2077343750000000000000000000000 : ℝ)*base68 + (5928418559816291/1038671875000000000000000000000 : ℝ)*base70 + (38004316688887039/4154687500000000000000000000000 : ℝ)*base72 + (15163195209763/2659000000000000000000000000 : ℝ)*base73 + (238628298935539703/8309375000000000000000000000000 : ℝ)*base76 + (96242855051414703/8309375000000000000000000000000 : ℝ)*base78 + (31671516102718289/4154687500000000000000000000000 : ℝ)*base80 + (4174989758707/664750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (22386287/2500000000000000000000 : ℝ)*base89 + (22386287/2500000000000000000000 : ℝ)*base91 + (22386287/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1209_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11433/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5719/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1209_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1209_s8_0 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-427050849/2000000000 : ℝ)*x 0 + (5391767481/10000000000 : ℝ)*x 1 + (210671953/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427050849/2000000000 : ℝ)^4201 ≤ (811334698869/6250000000000 : ℝ)^3177 := by
    have hnat : (427050849 : ℕ)^4201*6250000000000^3177 ≤ 811334698869^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427050849 2000000000 811334698869 6250000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391767481/10000000000 : ℝ)^4201 ≤ (22091929251643/50000000000000 : ℝ)^3177 := by
    have hnat : (5391767481 : ℕ)^4201*50000000000000^3177 ≤ 22091929251643^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391767481 10000000000 22091929251643 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210671953/400000000 : ℝ)^4201 ≤ (21417393150149/50000000000000 : ℝ)^3177 := by
    have hnat : (210671953 : ℕ)^4201*50000000000000^3177 ≤ 21417393150149^3177*400000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210671953 400000000 21417393150149 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-427050849/2000000000 : ℝ), (5391767481/10000000000 : ℝ), (210671953/400000000 : ℝ)] ![(811334698869/6250000000000 : ℝ), (22091929251643/50000000000000 : ℝ), (21417393150149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-427050849/2000000000 : ℝ)|^4201 ≤ (811334698869/6250000000000 : ℝ)^3177
        have hw : |(-427050849/2000000000 : ℝ)|=(427050849/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391767481/10000000000 : ℝ)|^4201 ≤ (22091929251643/50000000000000 : ℝ)^3177
        have hw : |(5391767481/10000000000 : ℝ)|=(5391767481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210671953/400000000 : ℝ)|^4201 ≤ (21417393150149/50000000000000 : ℝ)^3177
        have hw : |(210671953/400000000 : ℝ)|=(210671953/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s8_1 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344464129/10000000000 : ℝ)*x 0 + (-1099311849/5000000000 : ℝ)*x 1 + (5266798803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344464129/10000000000 : ℝ)^4201 ≤ (43672006781549/100000000000000 : ℝ)^3177 := by
    have hnat : (5344464129 : ℕ)^4201*100000000000000^3177 ≤ 43672006781549^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344464129 10000000000 43672006781549 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099311849/5000000000 : ℝ)^4201 ≤ (13493207142217/100000000000000 : ℝ)^3177 := by
    have hnat : (1099311849 : ℕ)^4201*100000000000000^3177 ≤ 13493207142217^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099311849 5000000000 13493207142217 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266798803/10000000000 : ℝ)^4201 ≤ (42834786063701/100000000000000 : ℝ)^3177 := by
    have hnat : (5266798803 : ℕ)^4201*100000000000000^3177 ≤ 42834786063701^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266798803 10000000000 42834786063701 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344464129/10000000000 : ℝ), (-1099311849/5000000000 : ℝ), (5266798803/10000000000 : ℝ)] ![(43672006781549/100000000000000 : ℝ), (13493207142217/100000000000000 : ℝ), (42834786063701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344464129/10000000000 : ℝ)|^4201 ≤ (43672006781549/100000000000000 : ℝ)^3177
        have hw : |(5344464129/10000000000 : ℝ)|=(5344464129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1099311849/5000000000 : ℝ)|^4201 ≤ (13493207142217/100000000000000 : ℝ)^3177
        have hw : |(-1099311849/5000000000 : ℝ)|=(1099311849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266798803/10000000000 : ℝ)|^4201 ≤ (42834786063701/100000000000000 : ℝ)^3177
        have hw : |(5266798803/10000000000 : ℝ)|=(5266798803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s8_2 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334029007/625000000 : ℝ)*x 0 + (2633399411/5000000000 : ℝ)*x 1 + (-439724739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334029007/625000000 : ℝ)^4201 ≤ (2183600329893/5000000000000 : ℝ)^3177 := by
    have hnat : (334029007 : ℕ)^4201*5000000000000^3177 ≤ 2183600329893^3177*625000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334029007 625000000 2183600329893 5000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633399411/5000000000 : ℝ)^4201 ≤ (21417393134017/50000000000000 : ℝ)^3177 := by
    have hnat : (2633399411 : ℕ)^4201*50000000000000^3177 ≤ 21417393134017^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633399411 5000000000 21417393134017 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (439724739/2000000000 : ℝ)^4201 ≤ (13493207117871/100000000000000 : ℝ)^3177 := by
    have hnat : (439724739 : ℕ)^4201*100000000000000^3177 ≤ 13493207117871^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439724739 2000000000 13493207117871 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334029007/625000000 : ℝ), (2633399411/5000000000 : ℝ), (-439724739/2000000000 : ℝ)] ![(2183600329893/5000000000000 : ℝ), (21417393134017/50000000000000 : ℝ), (13493207117871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334029007/625000000 : ℝ)|^4201 ≤ (2183600329893/5000000000000 : ℝ)^3177
        have hw : |(334029007/625000000 : ℝ)|=(334029007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633399411/5000000000 : ℝ)|^4201 ≤ (21417393134017/50000000000000 : ℝ)^3177
        have hw : |(2633399411/5000000000 : ℝ)|=(2633399411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-439724739/2000000000 : ℝ)|^4201 ≤ (13493207117871/100000000000000 : ℝ)^3177
        have hw : |(-439724739/2000000000 : ℝ)|=(439724739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s8_3 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (435532109/1000000000 : ℝ)*x 0 + (4231158457/10000000000 : ℝ)*x 1 + (2241525947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435532109/1000000000 : ℝ)^4201 ≤ (832933596489/2500000000000 : ℝ)^3177 := by
    have hnat : (435532109 : ℕ)^4201*2500000000000^3177 ≤ 832933596489^3177*1000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435532109 1000000000 832933596489 2500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4231158457/10000000000 : ℝ)^4201 ≤ (16033594790199/50000000000000 : ℝ)^3177 := by
    have hnat : (4231158457 : ℕ)^4201*50000000000000^3177 ≤ 16033594790199^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231158457 10000000000 16033594790199 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241525947/5000000000 : ℝ)^4201 ≤ (34615466539481/100000000000000 : ℝ)^3177 := by
    have hnat : (2241525947 : ℕ)^4201*100000000000000^3177 ≤ 34615466539481^3177*5000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241525947 5000000000 34615466539481 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435532109/1000000000 : ℝ), (4231158457/10000000000 : ℝ), (2241525947/5000000000 : ℝ)] ![(832933596489/2500000000000 : ℝ), (16033594790199/50000000000000 : ℝ), (34615466539481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435532109/1000000000 : ℝ)|^4201 ≤ (832933596489/2500000000000 : ℝ)^3177
        have hw : |(435532109/1000000000 : ℝ)|=(435532109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4231158457/10000000000 : ℝ)|^4201 ≤ (16033594790199/50000000000000 : ℝ)^3177
        have hw : |(4231158457/10000000000 : ℝ)|=(4231158457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2241525947/5000000000 : ℝ)|^4201 ≤ (34615466539481/100000000000000 : ℝ)^3177
        have hw : |(2241525947/5000000000 : ℝ)|=(2241525947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s8_4 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2135259111/10000000000 : ℝ)*x 0 + (1053422787/2000000000 : ℝ)*x 1 + (673931391/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135259111/10000000000 : ℝ)^4201 ≤ (12981394300041/100000000000000 : ℝ)^3177 := by
    have hnat : (2135259111 : ℕ)^4201*100000000000000^3177 ≤ 12981394300041^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135259111 10000000000 12981394300041 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053422787/2000000000 : ℝ)^4201 ≤ (5354771893171/12500000000000 : ℝ)^3177 := by
    have hnat : (1053422787 : ℕ)^4201*12500000000000^3177 ≤ 5354771893171^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053422787 2000000000 5354771893171 12500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673931391/1250000000 : ℝ)^4201 ≤ (11045107635711/25000000000000 : ℝ)^3177 := by
    have hnat : (673931391 : ℕ)^4201*25000000000000^3177 ≤ 11045107635711^3177*1250000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673931391 1250000000 11045107635711 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2135259111/10000000000 : ℝ), (1053422787/2000000000 : ℝ), (673931391/1250000000 : ℝ)] ![(12981394300041/100000000000000 : ℝ), (5354771893171/12500000000000 : ℝ), (11045107635711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2135259111/10000000000 : ℝ)|^4201 ≤ (12981394300041/100000000000000 : ℝ)^3177
        have hw : |(-2135259111/10000000000 : ℝ)|=(2135259111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053422787/2000000000 : ℝ)|^4201 ≤ (5354771893171/12500000000000 : ℝ)^3177
        have hw : |(1053422787/2000000000 : ℝ)|=(1053422787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673931391/1250000000 : ℝ)|^4201 ≤ (11045107635711/25000000000000 : ℝ)^3177
        have hw : |(673931391/1250000000 : ℝ)|=(673931391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s8_5 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312649201/10000000000 : ℝ)*x 0 + (-414794141/2000000000 : ℝ)*x 1 + (1347863111/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312649201/10000000000 : ℝ)^4201 ≤ (21664284532197/50000000000000 : ℝ)^3177 := by
    have hnat : (5312649201 : ℕ)^4201*50000000000000^3177 ≤ 21664284532197^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312649201 10000000000 21664284532197 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (414794141/2000000000 : ℝ)^4201 ≤ (12490986110841/100000000000000 : ℝ)^3177 := by
    have hnat : (414794141 : ℕ)^4201*100000000000000^3177 ≤ 12490986110841^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414794141 2000000000 12490986110841 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347863111/2500000000 : ℝ)^4201 ≤ (11045111200679/25000000000000 : ℝ)^3177 := by
    have hnat : (1347863111 : ℕ)^4201*25000000000000^3177 ≤ 11045111200679^3177*2500000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347863111 2500000000 11045111200679 25000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312649201/10000000000 : ℝ), (-414794141/2000000000 : ℝ), (1347863111/2500000000 : ℝ)] ![(21664284532197/50000000000000 : ℝ), (12490986110841/100000000000000 : ℝ), (11045111200679/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312649201/10000000000 : ℝ)|^4201 ≤ (21664284532197/50000000000000 : ℝ)^3177
        have hw : |(5312649201/10000000000 : ℝ)|=(5312649201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-414794141/2000000000 : ℝ)|^4201 ≤ (12490986110841/100000000000000 : ℝ)^3177
        have hw : |(-414794141/2000000000 : ℝ)|=(414794141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347863111/2500000000 : ℝ)|^4201 ≤ (11045111200679/25000000000000 : ℝ)^3177
        have hw : |(1347863111/2500000000 : ℝ)|=(1347863111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s8_6 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312650167/10000000000 : ℝ)*x 0 + (673931423/1250000000 : ℝ)*x 1 + (-51849271/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312650167/10000000000 : ℝ)^4201 ≤ (43328579482189/100000000000000 : ℝ)^3177 := by
    have hnat : (5312650167 : ℕ)^4201*100000000000000^3177 ≤ 43328579482189^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312650167 10000000000 43328579482189 100000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673931423/1250000000 : ℝ)^4201 ≤ (27612770823/62500000000 : ℝ)^3177 := by
    have hnat : (673931423 : ℕ)^4201*62500000000^3177 ≤ 27612770823^3177*1250000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673931423 1250000000 27612770823 62500000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51849271/250000000 : ℝ)^4201 ≤ (1561373398247/12500000000000 : ℝ)^3177 := by
    have hnat : (51849271 : ℕ)^4201*12500000000000^3177 ≤ 1561373398247^3177*250000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51849271 250000000 1561373398247 12500000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312650167/10000000000 : ℝ), (673931423/1250000000 : ℝ), (-51849271/250000000 : ℝ)] ![(43328579482189/100000000000000 : ℝ), (27612770823/62500000000 : ℝ), (1561373398247/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312650167/10000000000 : ℝ)|^4201 ≤ (43328579482189/100000000000000 : ℝ)^3177
        have hw : |(5312650167/10000000000 : ℝ)|=(5312650167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673931423/1250000000 : ℝ)|^4201 ≤ (27612770823/62500000000 : ℝ)^3177
        have hw : |(673931423/1250000000 : ℝ)|=(673931423/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51849271/250000000 : ℝ)|^4201 ≤ (1561373398247/12500000000000 : ℝ)^3177
        have hw : |(-51849271/250000000 : ℝ)|=(51849271/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1209_s8_7 (p : ℝ) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (871066099/2000000000 : ℝ)*x 0 + (4482418323/10000000000 : ℝ)*x 1 + (528974303/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871066099/2000000000 : ℝ)^4201 ≤ (66634877991/200000000000 : ℝ)^3177 := by
    have hnat : (871066099 : ℕ)^4201*200000000000^3177 ≤ 66634877991^3177*2000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871066099 2000000000 66634877991 200000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4482418323/10000000000 : ℝ)^4201 ≤ (17304498917669/50000000000000 : ℝ)^3177 := by
    have hnat : (4482418323 : ℕ)^4201*50000000000000^3177 ≤ 17304498917669^3177*10000000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482418323 10000000000 17304498917669 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528974303/1250000000 : ℝ)^4201 ≤ (16036781570917/50000000000000 : ℝ)^3177 := by
    have hnat : (528974303 : ℕ)^4201*50000000000000^3177 ≤ 16036781570917^3177*1250000000^4201 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528974303 1250000000 16036781570917 50000000000000 4201 3177 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4201/1024 : ℝ)) 4201 3177 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871066099/2000000000 : ℝ), (4482418323/10000000000 : ℝ), (528974303/1250000000 : ℝ)] ![(66634877991/200000000000 : ℝ), (17304498917669/50000000000000 : ℝ), (16036781570917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871066099/2000000000 : ℝ)|^4201 ≤ (66634877991/200000000000 : ℝ)^3177
        have hw : |(871066099/2000000000 : ℝ)|=(871066099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4482418323/10000000000 : ℝ)|^4201 ≤ (17304498917669/50000000000000 : ℝ)^3177
        have hw : |(4482418323/10000000000 : ℝ)|=(4482418323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528974303/1250000000 : ℝ)|^4201 ≤ (16036781570917/50000000000000 : ℝ)^3177
        have hw : |(528974303/1250000000 : ℝ)|=(528974303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1209_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5719/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11439/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7043/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14087/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5719/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14087/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5719/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14087/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5719/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14087/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5719/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14087/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5719/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14087/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5719/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5719/50000 : ℝ) ^ (8401/2048 : ℝ) ≤ (13718425215229681/100000000000000000000 : ℝ) := by
    have hpowers : (5719/50000 : ℝ)^8401 ≤ (13718425215229681/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5719 : ℕ)^8401*100000000000000000000^2048 ≤ 13718425215229681^2048*50000^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5719 50000 13718425215229681 100000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5719/50000 : ℝ)) (X := (13718425215229681/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14087/100000 : ℝ) ^ (8401/2048 : ℝ) ≤ (16120567528226587/50000000000000000000 : ℝ) := by
    have hpowers : (14087/100000 : ℝ)^8401 ≤ (16120567528226587/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14087 : ℕ)^8401*50000000000000000000^2048 ≤ 16120567528226587^2048*100000^8401 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14087 100000 16120567528226587 50000000000000000000 8401 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14087/100000 : ℝ)) (X := (16120567528226587/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013718425215229681/50000000000000000000 : ℝ) ≤ (10000668787540991/10000000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (50013718425215229681/50000000000000000000 : ℝ)^2048 ≤ (10000668787540991/10000000000000000 : ℝ)^8401 := by
      have hnat : (50013718425215229681 : ℕ)^2048*10000000000000000^8401 ≤ 10000668787540991^8401*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013718425215229681 50000000000000000000 10000668787540991 10000000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000668787540991/10000000000000000 : ℝ)) (X := (50013718425215229681/50000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009191912054336571/20000000000000000000 : ℝ) ≤ (5000560104910071/5000000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (20009191912054336571/20000000000000000000 : ℝ)^2048 ≤ (5000560104910071/5000000000000000 : ℝ)^8401 := by
      have hnat : (20009191912054336571 : ℕ)^2048*5000000000000000^8401 ≤ 5000560104910071^8401*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009191912054336571 20000000000000000000 5000560104910071 5000000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000560104910071/5000000000000000 : ℝ)) (X := (20009191912054336571/20000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016120567528226587/25000000000000000000 : ℝ) ≤ (10001571632099293/10000000000000000 : ℝ) ^ (8401/2048 : ℝ) := by
    have hpowers : (25016120567528226587/25000000000000000000 : ℝ)^2048 ≤ (10001571632099293/10000000000000000 : ℝ)^8401 := by
      have hnat : (25016120567528226587 : ℕ)^2048*10000000000000000^8401 ≤ 10001571632099293^8401*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016120567528226587 25000000000000000000 10001571632099293 10000000000000000 2048 8401 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001571632099293/10000000000000000 : ℝ)) (X := (25016120567528226587/25000000000000000000 : ℝ)) (by norm_num) 8401 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13718425215229681/100000000000000000000 : ℝ) ≤ ((26481444882138226883/26490000000000000000 : ℝ)+2*(451422279151/264900000000000 : ℝ)*(5719/50000 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (26481444882138226883/26490000000000000000 : ℝ)+2*(451422279151/264900000000000 : ℝ)*(5719/50000 : ℝ)=(10000668787540991/10000000000000000 : ℝ) by norm_num, show 1+2*(13718425215229681/100000000000000000000 : ℝ)=(50013718425215229681/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16120567528226587/50000000000000000000 : ℝ)+(13718425215229681/100000000000000000000 : ℝ) ≤ ((26481444882138226883/26490000000000000000 : ℝ)+(451422279151/264900000000000 : ℝ)*((14087/100000 : ℝ)+(5719/50000 : ℝ)))^(8401/2048 : ℝ) := by
    rw [show (26481444882138226883/26490000000000000000 : ℝ)+(451422279151/264900000000000 : ℝ)*((14087/100000 : ℝ)+(5719/50000 : ℝ))=(5000560104910071/5000000000000000 : ℝ) by norm_num, show 1+(16120567528226587/50000000000000000000 : ℝ)+(13718425215229681/100000000000000000000 : ℝ)=(20009191912054336571/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16120567528226587/50000000000000000000 : ℝ) ≤ ((26481444882138226883/26490000000000000000 : ℝ)+2*(451422279151/264900000000000 : ℝ)*(14087/100000 : ℝ))^(8401/2048 : ℝ) := by
    rw [show (26481444882138226883/26490000000000000000 : ℝ)+2*(451422279151/264900000000000 : ℝ)*(14087/100000 : ℝ)=(10001571632099293/10000000000000000 : ℝ) by norm_num, show 1+2*(16120567528226587/50000000000000000000 : ℝ)=(25016120567528226587/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26481444882138226883/26490000000000000000 : ℝ)*(X 1 0+X 2 0)+(451422279151/264900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (5719/50000 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (26481444882138226883/26490000000000000000 : ℝ)) (alpha := (451422279151/264900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26481444882138226883/26490000000000000000 : ℝ)*(X 0 1+X 2 1)+(451422279151/264900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (5719/50000 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (26481444882138226883/26490000000000000000 : ℝ)) (alpha := (451422279151/264900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26481444882138226883/26490000000000000000 : ℝ)*(X 0 2+X 1 2)+(451422279151/264900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8401/2048 : ℝ)) (lo := (5719/50000 : ℝ)) (hi := (14087/100000 : ℝ)) (c := (26481444882138226883/26490000000000000000 : ℝ)) (alpha := (451422279151/264900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-427050849/2000000000 : ℝ)*X 0 0+(5391767481/10000000000 : ℝ)*X 0 1+(210671953/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344464129/10000000000 : ℝ)*X 1 0+(-1099311849/5000000000 : ℝ)*X 1 1+(5266798803/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334029007/625000000 : ℝ)*X 2 0+(2633399411/5000000000 : ℝ)*X 2 1+(-439724739/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((435532109/1000000000 : ℝ)*X 0 0+(4231158457/10000000000 : ℝ)*X 0 1+(2241525947/5000000000 : ℝ)*X 0 2+(435532109/1000000000 : ℝ)*X 1 0+(4231158457/10000000000 : ℝ)*X 1 1+(2241525947/5000000000 : ℝ)*X 1 2+(435532109/1000000000 : ℝ)*X 2 0+(4231158457/10000000000 : ℝ)*X 2 1+(2241525947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2135259111/10000000000 : ℝ)*X 0 0+(1053422787/2000000000 : ℝ)*X 0 1+(673931391/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312649201/10000000000 : ℝ)*X 1 0+(-414794141/2000000000 : ℝ)*X 1 1+(1347863111/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312650167/10000000000 : ℝ)*X 2 0+(673931423/1250000000 : ℝ)*X 2 1+(-51849271/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871066099/2000000000 : ℝ)*X 0 0+(4482418323/10000000000 : ℝ)*X 0 1+(528974303/1250000000 : ℝ)*X 0 2+(871066099/2000000000 : ℝ)*X 1 0+(4482418323/10000000000 : ℝ)*X 1 1+(528974303/1250000000 : ℝ)*X 1 2+(871066099/2000000000 : ℝ)*X 2 0+(4482418323/10000000000 : ℝ)*X 2 1+(528974303/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1209_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2818083120821756853409/551875000000000000000000000 : ℝ) := by norm_num
    linear_combination (511716847/50000000000000 : ℝ)*(base19) + (924027323/100000000000000 : ℝ)*(base23) + (316191/800000000000 : ℝ)*(lower2) + (16127221/12500000000000 : ℝ)*(upper3) + (14913123/20000000000000 : ℝ)*(upper5) + (748251490535681/12500000000000 : ℝ)*(major0) + (748251490535681/12500000000000 : ℝ)*(major1) + (748251490535681/12500000000000 : ℝ)*(major2) + (1000254411199971/12500000000000 : ℝ)*(sp0) + (8002061364698817/100000000000000 : ℝ)*(sp1) + (2000515366026297/25000000000000 : ℝ)*(sp2) + (1984973138782343/50000000000000 : ℝ)*(sp3) + (27098532743/100000000000000 : ℝ)*(sp4) + (15012661043/100000000000000 : ℝ)*(sp7) + (62030645159777/1562500000000 : ℝ)*(f.failure) + (8002062388132511/100000000000000 : ℝ)*(f.sum) + (4398695548451/1655625000000000000000000000 : ℝ)*base65 + (214132632410337441/110375000000000000000000000000000 : ℝ)*base67 + (1164600707006837441/110375000000000000000000000000000 : ℝ)*base69 + (489144959722412559/110375000000000000000000000000000 : ℝ)*base72 + (67066176435977/13245000000000000000000000000 : ℝ)*base74 + (890157880918287559/110375000000000000000000000000000 : ℝ)*base76 + (712421830723962441/110375000000000000000000000000000 : ℝ)*base77 + (241260315528287559/110375000000000000000000000000000 : ℝ)*base80 + (6246104068991/1655625000000000000000000000 : ℝ)*base81 + (1705821/156250000000000000000 : ℝ)*base90 + (1705821/156250000000000000000 : ℝ)*base92 + (1705821/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1155603872145517554007660667/220750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1296519793/100000000000000 : ℝ)*(base23) + (773668621/100000000000000 : ℝ)*(lower1) + (70097/1250000000000 : ℝ)*(upper2) + (142367967/50000000000000 : ℝ)*(upper3) + (2296461/2000000000000 : ℝ)*(upper4) + (6016327318210151/100000000000000 : ℝ)*(major0) + (6016327318210151/100000000000000 : ℝ)*(major1) + (6016327318210151/100000000000000 : ℝ)*(major2) + (3315671483/50000000000000 : ℝ)*(sp2) + (20247169381/100000000000000 : ℝ)*(sp3) + (4021293904539507/50000000000000 : ℝ)*(sp4) + (4021293904539507/50000000000000 : ℝ)*(sp5) + (1608515976243251/20000000000000 : ℝ)*(sp6) + (49875580070941/1250000000000 : ℝ)*(sp7) + (1995033326422331/50000000000000 : ℝ)*(f.failure) + (4021293904539507/50000000000000 : ℝ)*(f.sum) + (11473444471481/13245000000000000000000000000 : ℝ)*base65 + (4967838595803736889/883000000000000000000000000000000 : ℝ)*base68 + (7201222832239263111/883000000000000000000000000000000 : ℝ)*base69 + (9611766405865263111/883000000000000000000000000000000 : ℝ)*base71 + (8585515806257/6622500000000000000000000000 : ℝ)*base74 + (1242754351847263111/883000000000000000000000000000000 : ℝ)*base75 + (1517717799536263111/883000000000000000000000000000000 : ℝ)*base77 + (2913490149390263111/883000000000000000000000000000000 : ℝ)*base79 + (19347591302621/13245000000000000000000000000 : ℝ)*base81 + (29643537/5000000000000000000000 : ℝ)*base89 + (29643537/5000000000000000000000 : ℝ)*base91 + (29643537/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1209_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5719/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11439/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1209_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1209_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11439/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1209_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1209_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1209_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8401/2048 : ℝ) ≤ p) (hpb : p ≤ (4201/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150782627/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11439/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7043/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1209_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

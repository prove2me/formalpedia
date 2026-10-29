-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1703_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:44:58.026215+00:00
-- url     : https://prove2.me/submissions/58085d56-da4f-4d08-8d79-eb92ca2fca12

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
theorem support_rectangle_w1703_s3_0 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1437771371/10000000000 : ℝ)*x 0 + (1368637511/2500000000 : ℝ)*x 1 + (2568683473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1437771371/10000000000 : ℝ)^5247 ≤ (2245872423009/25000000000000 : ℝ)^4223 := by
    have hnat : (1437771371 : ℕ)^5247*25000000000000^4223 ≤ 2245872423009^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1437771371 10000000000 2245872423009 25000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368637511/2500000000 : ℝ)^5247 ≤ (47304529383771/100000000000000 : ℝ)^4223 := by
    have hnat : (1368637511 : ℕ)^5247*100000000000000^4223 ≤ 47304529383771^4223*2500000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368637511 2500000000 47304529383771 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568683473/5000000000 : ℝ)^5247 ≤ (8742396181141/20000000000000 : ℝ)^4223 := by
    have hnat : (2568683473 : ℕ)^5247*20000000000000^4223 ≤ 8742396181141^4223*5000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568683473 5000000000 8742396181141 20000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1437771371/10000000000 : ℝ), (1368637511/2500000000 : ℝ), (2568683473/5000000000 : ℝ)] ![(2245872423009/25000000000000 : ℝ), (47304529383771/100000000000000 : ℝ), (8742396181141/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1437771371/10000000000 : ℝ)|^5247 ≤ (2245872423009/25000000000000 : ℝ)^4223
        have hw : |(-1437771371/10000000000 : ℝ)|=(1437771371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368637511/2500000000 : ℝ)|^5247 ≤ (47304529383771/100000000000000 : ℝ)^4223
        have hw : |(1368637511/2500000000 : ℝ)|=(1368637511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2568683473/5000000000 : ℝ)|^5247 ≤ (8742396181141/20000000000000 : ℝ)^4223
        have hw : |(2568683473/5000000000 : ℝ)|=(2568683473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_s3_1 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672933943/5000000000 : ℝ)*x 0 + (-806356841/5000000000 : ℝ)*x 1 + (160542717/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672933943/5000000000 : ℝ)^5247 ≤ (45926952843213/100000000000000 : ℝ)^4223 := by
    have hnat : (2672933943 : ℕ)^5247*100000000000000^4223 ≤ 45926952843213^4223*5000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672933943 5000000000 45926952843213 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (806356841/5000000000 : ℝ)^5247 ≤ (10361066266729/100000000000000 : ℝ)^4223 := by
    have hnat : (806356841 : ℕ)^5247*100000000000000^4223 ≤ 10361066266729^4223*5000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806356841 5000000000 10361066266729 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160542717/312500000 : ℝ)^5247 ≤ (21855990442281/50000000000000 : ℝ)^4223 := by
    have hnat : (160542717 : ℕ)^5247*50000000000000^4223 ≤ 21855990442281^4223*312500000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160542717 312500000 21855990442281 50000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672933943/5000000000 : ℝ), (-806356841/5000000000 : ℝ), (160542717/312500000 : ℝ)] ![(45926952843213/100000000000000 : ℝ), (10361066266729/100000000000000 : ℝ), (21855990442281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672933943/5000000000 : ℝ)|^5247 ≤ (45926952843213/100000000000000 : ℝ)^4223
        have hw : |(2672933943/5000000000 : ℝ)|=(2672933943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-806356841/5000000000 : ℝ)|^5247 ≤ (10361066266729/100000000000000 : ℝ)^4223
        have hw : |(-806356841/5000000000 : ℝ)|=(806356841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(160542717/312500000 : ℝ)|^5247 ≤ (21855990442281/50000000000000 : ℝ)^4223
        have hw : |(160542717/312500000 : ℝ)|=(160542717/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_s3_2 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672933943/5000000000 : ℝ)*x 0 + (5137366973/10000000000 : ℝ)*x 1 + (-1612713641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672933943/5000000000 : ℝ)^5247 ≤ (45926952843213/100000000000000 : ℝ)^4223 := by
    have hnat : (2672933943 : ℕ)^5247*100000000000000^4223 ≤ 45926952843213^4223*5000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672933943 5000000000 45926952843213 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137366973/10000000000 : ℝ)^5247 ≤ (8742396238229/20000000000000 : ℝ)^4223 := by
    have hnat : (5137366973 : ℕ)^5247*20000000000000^4223 ≤ 8742396238229^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137366973 10000000000 8742396238229 20000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1612713641/10000000000 : ℝ)^5247 ≤ (1295133242431/12500000000000 : ℝ)^4223 := by
    have hnat : (1612713641 : ℕ)^5247*12500000000000^4223 ≤ 1295133242431^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1612713641 10000000000 1295133242431 12500000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672933943/5000000000 : ℝ), (5137366973/10000000000 : ℝ), (-1612713641/10000000000 : ℝ)] ![(45926952843213/100000000000000 : ℝ), (8742396238229/20000000000000 : ℝ), (1295133242431/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672933943/5000000000 : ℝ)|^5247 ≤ (45926952843213/100000000000000 : ℝ)^4223
        have hw : |(2672933943/5000000000 : ℝ)|=(2672933943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137366973/10000000000 : ℝ)|^5247 ≤ (8742396238229/20000000000000 : ℝ)^4223
        have hw : |(5137366973/10000000000 : ℝ)|=(5137366973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1612713641/10000000000 : ℝ)|^5247 ≤ (1295133242431/12500000000000 : ℝ)^4223
        have hw : |(-1612713641/10000000000 : ℝ)|=(1612713641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_s3_3 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4113796781/10000000000 : ℝ)*x 0 + (456365909/1250000000 : ℝ)*x 1 + (4612903647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4113796781/10000000000 : ℝ)^5247 ≤ (33166817465647/100000000000000 : ℝ)^4223 := by
    have hnat : (4113796781 : ℕ)^5247*100000000000000^4223 ≤ 33166817465647^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4113796781 10000000000 33166817465647 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (456365909/1250000000 : ℝ)^5247 ≤ (14297627837413/50000000000000 : ℝ)^4223 := by
    have hnat : (456365909 : ℕ)^5247*50000000000000^4223 ≤ 14297627837413^4223*1250000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456365909 1250000000 14297627837413 50000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4612903647/10000000000 : ℝ)^5247 ≤ (38237926839891/100000000000000 : ℝ)^4223 := by
    have hnat : (4612903647 : ℕ)^5247*100000000000000^4223 ≤ 38237926839891^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4612903647 10000000000 38237926839891 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4113796781/10000000000 : ℝ), (456365909/1250000000 : ℝ), (4612903647/10000000000 : ℝ)] ![(33166817465647/100000000000000 : ℝ), (14297627837413/50000000000000 : ℝ), (38237926839891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4113796781/10000000000 : ℝ)|^5247 ≤ (33166817465647/100000000000000 : ℝ)^4223
        have hw : |(4113796781/10000000000 : ℝ)|=(4113796781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(456365909/1250000000 : ℝ)|^5247 ≤ (14297627837413/50000000000000 : ℝ)^4223
        have hw : |(456365909/1250000000 : ℝ)|=(456365909/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4612903647/10000000000 : ℝ)|^5247 ≤ (38237926839891/100000000000000 : ℝ)^4223
        have hw : |(4612903647/10000000000 : ℝ)|=(4612903647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_s3_4 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-179740693/1250000000 : ℝ)*x 0 + (5141078309/10000000000 : ℝ)*x 1 + (1367695833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179740693/1250000000 : ℝ)^5247 ≤ (8984686595693/100000000000000 : ℝ)^4223 := by
    have hnat : (179740693 : ℕ)^5247*100000000000000^4223 ≤ 8984686595693^4223*1250000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179740693 1250000000 8984686595693 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5141078309/10000000000 : ℝ)^5247 ≤ (13672256317/31250000000 : ℝ)^4223 := by
    have hnat : (5141078309 : ℕ)^5247*31250000000^4223 ≤ 13672256317^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5141078309 10000000000 13672256317 31250000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367695833/2500000000 : ℝ)^5247 ≤ (47264093172361/100000000000000 : ℝ)^4223 := by
    have hnat : (1367695833 : ℕ)^5247*100000000000000^4223 ≤ 47264093172361^4223*2500000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367695833 2500000000 47264093172361 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-179740693/1250000000 : ℝ), (5141078309/10000000000 : ℝ), (1367695833/2500000000 : ℝ)] ![(8984686595693/100000000000000 : ℝ), (13672256317/31250000000 : ℝ), (47264093172361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-179740693/1250000000 : ℝ)|^5247 ≤ (8984686595693/100000000000000 : ℝ)^4223
        have hw : |(-179740693/1250000000 : ℝ)|=(179740693/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5141078309/10000000000 : ℝ)|^5247 ≤ (13672256317/31250000000 : ℝ)^4223
        have hw : |(5141078309/10000000000 : ℝ)|=(5141078309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1367695833/2500000000 : ℝ)|^5247 ≤ (47264093172361/100000000000000 : ℝ)^4223
        have hw : |(1367695833/2500000000 : ℝ)|=(1367695833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_s3_5 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313909083/2500000000 : ℝ)*x 0 + (-639648657/5000000000 : ℝ)*x 1 + (547078333/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313909083/2500000000 : ℝ)^5247 ≤ (22482886828267/50000000000000 : ℝ)^4223 := by
    have hnat : (1313909083 : ℕ)^5247*50000000000000^4223 ≤ 22482886828267^4223*2500000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313909083 2500000000 22482886828267 50000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (639648657/5000000000 : ℝ)^5247 ≤ (3885066589871/50000000000000 : ℝ)^4223 := by
    have hnat : (639648657 : ℕ)^5247*50000000000000^4223 ≤ 3885066589871^4223*5000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639648657 5000000000 3885066589871 50000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547078333/1000000000 : ℝ)^5247 ≤ (47264093150893/100000000000000 : ℝ)^4223 := by
    have hnat : (547078333 : ℕ)^5247*100000000000000^4223 ≤ 47264093150893^4223*1000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547078333 1000000000 47264093150893 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313909083/2500000000 : ℝ), (-639648657/5000000000 : ℝ), (547078333/1000000000 : ℝ)] ![(22482886828267/50000000000000 : ℝ), (3885066589871/50000000000000 : ℝ), (47264093150893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313909083/2500000000 : ℝ)|^5247 ≤ (22482886828267/50000000000000 : ℝ)^4223
        have hw : |(1313909083/2500000000 : ℝ)|=(1313909083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-639648657/5000000000 : ℝ)|^5247 ≤ (3885066589871/50000000000000 : ℝ)^4223
        have hw : |(-639648657/5000000000 : ℝ)|=(639648657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547078333/1000000000 : ℝ)|^5247 ≤ (47264093150893/100000000000000 : ℝ)^4223
        have hw : |(547078333/1000000000 : ℝ)|=(547078333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_s3_6 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2627818169/5000000000 : ℝ)*x 0 + (5470783329/10000000000 : ℝ)*x 1 + (-1279297307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627818169/5000000000 : ℝ)^5247 ≤ (11241443430079/25000000000000 : ℝ)^4223 := by
    have hnat : (2627818169 : ℕ)^5247*25000000000000^4223 ≤ 11241443430079^4223*5000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627818169 5000000000 11241443430079 25000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470783329/10000000000 : ℝ)^5247 ≤ (47264093140159/100000000000000 : ℝ)^4223 := by
    have hnat : (5470783329 : ℕ)^5247*100000000000000^4223 ≤ 47264093140159^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470783329 10000000000 47264093140159 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1279297307/10000000000 : ℝ)^5247 ≤ (1942533281729/25000000000000 : ℝ)^4223 := by
    have hnat : (1279297307 : ℕ)^5247*25000000000000^4223 ≤ 1942533281729^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279297307 10000000000 1942533281729 25000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627818169/5000000000 : ℝ), (5470783329/10000000000 : ℝ), (-1279297307/10000000000 : ℝ)] ![(11241443430079/25000000000000 : ℝ), (47264093140159/100000000000000 : ℝ), (1942533281729/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627818169/5000000000 : ℝ)|^5247 ≤ (11241443430079/25000000000000 : ℝ)^4223
        have hw : |(2627818169/5000000000 : ℝ)|=(2627818169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470783329/10000000000 : ℝ)|^5247 ≤ (47264093140159/100000000000000 : ℝ)^4223
        have hw : |(5470783329/10000000000 : ℝ)|=(5470783329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1279297307/10000000000 : ℝ)|^5247 ≤ (1942533281729/25000000000000 : ℝ)^4223
        have hw : |(-1279297307/10000000000 : ℝ)|=(1279297307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_s3_7 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (205711837/500000000 : ℝ)*x 0 + (460231529/1000000000 : ℝ)*x 1 + (1830836809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205711837/500000000 : ℝ)^5247 ≤ (8292806181703/25000000000000 : ℝ)^4223 := by
    have hnat : (205711837 : ℕ)^5247*25000000000000^4223 ≤ 8292806181703^4223*500000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205711837 500000000 8292806181703 25000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (460231529/1000000000 : ℝ)^5247 ≤ (38128903981373/100000000000000 : ℝ)^4223 := by
    have hnat : (460231529 : ℕ)^5247*100000000000000^4223 ≤ 38128903981373^4223*1000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460231529 1000000000 38128903981373 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1830836809/5000000000 : ℝ)^5247 ≤ (28699871274119/100000000000000 : ℝ)^4223 := by
    have hnat : (1830836809 : ℕ)^5247*100000000000000^4223 ≤ 28699871274119^4223*5000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1830836809 5000000000 28699871274119 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(205711837/500000000 : ℝ), (460231529/1000000000 : ℝ), (1830836809/5000000000 : ℝ)] ![(8292806181703/25000000000000 : ℝ), (38128903981373/100000000000000 : ℝ), (28699871274119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(205711837/500000000 : ℝ)|^5247 ≤ (8292806181703/25000000000000 : ℝ)^4223
        have hw : |(205711837/500000000 : ℝ)|=(205711837/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(460231529/1000000000 : ℝ)|^5247 ≤ (38128903981373/100000000000000 : ℝ)^4223
        have hw : |(460231529/1000000000 : ℝ)|=(460231529/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1830836809/5000000000 : ℝ)|^5247 ≤ (28699871274119/100000000000000 : ℝ)^4223
        have hw : |(1830836809/5000000000 : ℝ)|=(1830836809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1703_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (192648977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17157/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (497/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (311/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17143/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17157/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (497/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17157/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (497/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17157/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (497/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17157/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (497/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17157/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (497/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17157/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (497/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (497/5000 : ℝ) ^ (5239/1024 : ℝ) ≤ (742022806484513/100000000000000000000 : ℝ) := by
    have hpowers : (497/5000 : ℝ)^5239 ≤ (742022806484513/100000000000000000000 : ℝ)^1024 := by
      have hnat : (497 : ℕ)^5239*100000000000000000000^1024 ≤ 742022806484513^1024*5000^5239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        497 5000 742022806484513 100000000000000000000 5239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (497/5000 : ℝ)) (X := (742022806484513/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5239 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17157/100000 : ℝ) ^ (5239/1024 : ℝ) ≤ (12112686251050261/100000000000000000000 : ℝ) := by
    have hpowers : (17157/100000 : ℝ)^5239 ≤ (12112686251050261/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17157 : ℕ)^5239*100000000000000000000^1024 ≤ 12112686251050261^1024*100000^5239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17157 100000 12112686251050261 100000000000000000000 5239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17157/100000 : ℝ)) (X := (12112686251050261/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5239 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000742022806484513/50000000000000000000 : ℝ) ≤ (5000014503279591/5000000000000000 : ℝ) ^ (5239/1024 : ℝ) := by
    have hpowers : (50000742022806484513/50000000000000000000 : ℝ)^1024 ≤ (5000014503279591/5000000000000000 : ℝ)^5239 := by
      have hnat : (50000742022806484513 : ℕ)^1024*5000000000000000^5239 ≤ 5000014503279591^5239*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000742022806484513 50000000000000000000 5000014503279591 5000000000000000 1024 5239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000014503279591/5000000000000000 : ℝ)) (X := (50000742022806484513/50000000000000000000 : ℝ)) (by norm_num) 5239 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50006427354528767387/50000000000000000000 : ℝ) ≤ (2000050248297181/2000000000000000 : ℝ) ^ (5239/1024 : ℝ) := by
    have hpowers : (50006427354528767387/50000000000000000000 : ℝ)^1024 ≤ (2000050248297181/2000000000000000 : ℝ)^5239 := by
      have hnat : (50006427354528767387 : ℕ)^1024*2000000000000000^5239 ≤ 2000050248297181^5239*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006427354528767387 50000000000000000000 2000050248297181 2000000000000000 1024 5239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000050248297181/2000000000000000 : ℝ)) (X := (50006427354528767387/50000000000000000000 : ℝ)) (by norm_num) 5239 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50012112686251050261/50000000000000000000 : ℝ) ≤ (2500118369103157/2500000000000000 : ℝ) ^ (5239/1024 : ℝ) := by
    have hpowers : (50012112686251050261/50000000000000000000 : ℝ)^1024 ≤ (2500118369103157/2500000000000000 : ℝ)^5239 := by
      have hnat : (50012112686251050261 : ℕ)^1024*2500000000000000^5239 ≤ 2500118369103157^5239*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012112686251050261 50000000000000000000 2500118369103157 2500000000000000 1024 5239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500118369103157/2500000000000000 : ℝ)) (X := (50012112686251050261/50000000000000000000 : ℝ)) (by norm_num) 5239 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(742022806484513/100000000000000000000 : ℝ) ≤ ((5154699379285311661/5155000000000000000 : ℝ)+2*(222234926723/721700000000000 : ℝ)*(497/5000 : ℝ))^(5239/1024 : ℝ) := by
    rw [show (5154699379285311661/5155000000000000000 : ℝ)+2*(222234926723/721700000000000 : ℝ)*(497/5000 : ℝ)=(5000014503279591/5000000000000000 : ℝ) by norm_num, show 1+2*(742022806484513/100000000000000000000 : ℝ)=(50000742022806484513/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12112686251050261/100000000000000000000 : ℝ)+(742022806484513/100000000000000000000 : ℝ) ≤ ((5154699379285311661/5155000000000000000 : ℝ)+(222234926723/721700000000000 : ℝ)*((17157/100000 : ℝ)+(497/5000 : ℝ)))^(5239/1024 : ℝ) := by
    rw [show (5154699379285311661/5155000000000000000 : ℝ)+(222234926723/721700000000000 : ℝ)*((17157/100000 : ℝ)+(497/5000 : ℝ))=(2000050248297181/2000000000000000 : ℝ) by norm_num, show 1+(12112686251050261/100000000000000000000 : ℝ)+(742022806484513/100000000000000000000 : ℝ)=(50006427354528767387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12112686251050261/100000000000000000000 : ℝ) ≤ ((5154699379285311661/5155000000000000000 : ℝ)+2*(222234926723/721700000000000 : ℝ)*(17157/100000 : ℝ))^(5239/1024 : ℝ) := by
    rw [show (5154699379285311661/5155000000000000000 : ℝ)+2*(222234926723/721700000000000 : ℝ)*(17157/100000 : ℝ)=(2500118369103157/2500000000000000 : ℝ) by norm_num, show 1+2*(12112686251050261/100000000000000000000 : ℝ)=(50012112686251050261/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5154699379285311661/5155000000000000000 : ℝ)*(X 1 0+X 2 0)+(222234926723/721700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5239/1024 : ℝ)) (lo := (497/5000 : ℝ)) (hi := (17157/100000 : ℝ)) (c := (5154699379285311661/5155000000000000000 : ℝ)) (alpha := (222234926723/721700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5154699379285311661/5155000000000000000 : ℝ)*(X 0 1+X 2 1)+(222234926723/721700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5239/1024 : ℝ)) (lo := (497/5000 : ℝ)) (hi := (17157/100000 : ℝ)) (c := (5154699379285311661/5155000000000000000 : ℝ)) (alpha := (222234926723/721700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5154699379285311661/5155000000000000000 : ℝ)*(X 0 2+X 1 2)+(222234926723/721700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5239/1024 : ℝ)) (lo := (497/5000 : ℝ)) (hi := (17157/100000 : ℝ)) (c := (5154699379285311661/5155000000000000000 : ℝ)) (alpha := (222234926723/721700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1437771371/10000000000 : ℝ)*X 0 0+(1368637511/2500000000 : ℝ)*X 0 1+(2568683473/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672933943/5000000000 : ℝ)*X 1 0+(-806356841/5000000000 : ℝ)*X 1 1+(160542717/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672933943/5000000000 : ℝ)*X 2 0+(5137366973/10000000000 : ℝ)*X 2 1+(-1612713641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4113796781/10000000000 : ℝ)*X 0 0+(456365909/1250000000 : ℝ)*X 0 1+(4612903647/10000000000 : ℝ)*X 0 2+(4113796781/10000000000 : ℝ)*X 1 0+(456365909/1250000000 : ℝ)*X 1 1+(4612903647/10000000000 : ℝ)*X 1 2+(4113796781/10000000000 : ℝ)*X 2 0+(456365909/1250000000 : ℝ)*X 2 1+(4612903647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-179740693/1250000000 : ℝ)*X 0 0+(5141078309/10000000000 : ℝ)*X 0 1+(1367695833/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1313909083/2500000000 : ℝ)*X 1 0+(-639648657/5000000000 : ℝ)*X 1 1+(547078333/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2627818169/5000000000 : ℝ)*X 2 0+(5470783329/10000000000 : ℝ)*X 2 1+(-1279297307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((205711837/500000000 : ℝ)*X 0 0+(460231529/1000000000 : ℝ)*X 0 1+(1830836809/5000000000 : ℝ)*X 0 2+(205711837/500000000 : ℝ)*X 1 0+(460231529/1000000000 : ℝ)*X 1 1+(1830836809/5000000000 : ℝ)*X 1 2+(205711837/500000000 : ℝ)*X 2 0+(460231529/1000000000 : ℝ)*X 2 1+(1830836809/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (363098792312920970469/51550000000000000000000000 : ℝ) := by norm_num
    linear_combination (107936567/10000000000000 : ℝ)*(base19) + (1036072057/100000000000000 : ℝ)*(base23) + (11572097/50000000000000 : ℝ)*(lower2) + (78827197/50000000000000 : ℝ)*(upper3) + (18956403/12500000000000 : ℝ)*(upper5) + (400530359152259/20000000000000 : ℝ)*(major0) + (400530359152259/20000000000000 : ℝ)*(major1) + (400530359152259/20000000000000 : ℝ)*(major2) + (1482879134103871/50000000000000 : ℝ)*(sp0) + (593153636870719/20000000000000 : ℝ)*(sp1) + (370721028455901/12500000000000 : ℝ)*(sp2) + (1039530229762117/100000000000000 : ℝ)*(sp3) + (10995511523/100000000000000 : ℝ)*(sp4) + (3090603/80000000000 : ℝ)*(sp7) + (1039534093015867/100000000000000 : ℝ)*(f.failure) + (1482884631859633/50000000000000 : ℝ)*(f.sum) + (526985383161/515500000000000000000000000 : ℝ)*base66 + (50279769990157801/103100000000000000000000000000000 : ℝ)*base68 + (32654947472957801/103100000000000000000000000000000 : ℝ)*base70 + (133520953990957801/103100000000000000000000000000000 : ℝ)*base72 + (478834511197/1031000000000000000000000000 : ℝ)*base73 + (616242728679842199/103100000000000000000000000000000 : ℝ)*base75 + (340160436643242199/103100000000000000000000000000000 : ℝ)*base77 + (274200042109942199/103100000000000000000000000000000 : ℝ)*base79 + (26824563657/4124000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (122318059/10000000000000000000000 : ℝ)*base89 + (122318059/10000000000000000000000 : ℝ)*base91 + (122318059/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4194270767014639766578746741/451062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1290601489/100000000000000 : ℝ)*(base19) + (348896843/25000000000000 : ℝ)*(base23) + (192777287/50000000000000 : ℝ)*(lower1) + (198380209/100000000000000 : ℝ)*(upper3) + (45046377/100000000000000 : ℝ)*(lower4) + (194645711/100000000000000 : ℝ)*(upper5) + (1024025502839061/50000000000000 : ℝ)*(major0) + (1024025502839061/50000000000000 : ℝ)*(major1) + (1024025502839061/50000000000000 : ℝ)*(major2) + (921027893/100000000000000 : ℝ)*(sp2) + (303300184093433/10000000000000 : ℝ)*(sp4) + (1516500275166421/50000000000000 : ℝ)*(sp5) + (1516499762159533/50000000000000 : ℝ)*(sp6) + (106309986046701/10000000000000 : ℝ)*(sp7) + (106309986046701/10000000000000 : ℝ)*(f.failure) + (303300184093433/10000000000000 : ℝ)*(f.sum) + (84117869642797/18042500000000000000000000000 : ℝ)*base66 + (5405313873875217753/1804250000000000000000000000000000 : ℝ)*base68 + (1045341710072717753/1804250000000000000000000000000000 : ℝ)*base70 + (145099788843389717753/1804250000000000000000000000000000 : ℝ)*base72 + (61655162559343/18042500000000000000000000000 : ℝ)*base73 + (88996591170652282247/1804250000000000000000000000000000 : ℝ)*base75 + (8277645658078217753/1804250000000000000000000000000000 : ℝ)*base78 + (28505452530965467753/1804250000000000000000000000000000 : ℝ)*base80 + (27172596201281/36085000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1874877/1000000000000000000000 : ℝ)*base89 + (1874877/1000000000000000000000 : ℝ)*base91 + (1874877/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1703_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (192648977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17157/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (497/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (311/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17143/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1703_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1703_s4_0 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1437778859/10000000000 : ℝ)*x 0 + (2737261893/5000000000 : ℝ)*x 1 + (5137388113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1437778859/10000000000 : ℝ)^5247 ≤ (898354782351/10000000000000 : ℝ)^4223 := by
    have hnat : (1437778859 : ℕ)^5247*10000000000000^4223 ≤ 898354782351^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1437778859 10000000000 898354782351 10000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2737261893/5000000000 : ℝ)^5247 ≤ (23652123738447/50000000000000 : ℝ)^4223 := by
    have hnat : (2737261893 : ℕ)^5247*50000000000000^4223 ≤ 23652123738447^4223*5000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737261893 5000000000 23652123738447 50000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5137388113/10000000000 : ℝ)^5247 ≤ (8742440935919/20000000000000 : ℝ)^4223 := by
    have hnat : (5137388113 : ℕ)^5247*20000000000000^4223 ≤ 8742440935919^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137388113 10000000000 8742440935919 20000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1437778859/10000000000 : ℝ), (2737261893/5000000000 : ℝ), (5137388113/10000000000 : ℝ)] ![(898354782351/10000000000000 : ℝ), (23652123738447/50000000000000 : ℝ), (8742440935919/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1437778859/10000000000 : ℝ)|^5247 ≤ (898354782351/10000000000000 : ℝ)^4223
        have hw : |(-1437778859/10000000000 : ℝ)|=(1437778859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2737261893/5000000000 : ℝ)|^5247 ≤ (23652123738447/50000000000000 : ℝ)^4223
        have hw : |(2737261893/5000000000 : ℝ)|=(2737261893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5137388113/10000000000 : ℝ)|^5247 ≤ (8742440935919/20000000000000 : ℝ)^4223
        have hw : |(5137388113/10000000000 : ℝ)|=(5137388113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_s4_1 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336464753/2500000000 : ℝ)*x 0 + (205495597/400000000 : ℝ)*x 1 + (-201586889/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336464753/2500000000 : ℝ)^5247 ≤ (5740857264937/12500000000000 : ℝ)^4223 := by
    have hnat : (1336464753 : ℕ)^5247*12500000000000^4223 ≤ 5740857264937^4223*2500000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336464753 2500000000 5740857264937 12500000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205495597/400000000 : ℝ)^5247 ≤ (21856111917879/50000000000000 : ℝ)^4223 := by
    have hnat : (205495597 : ℕ)^5247*50000000000000^4223 ≤ 21856111917879^4223*400000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205495597 400000000 21856111917879 50000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201586889/1250000000 : ℝ)^5247 ≤ (10360918032513/100000000000000 : ℝ)^4223 := by
    have hnat : (201586889 : ℕ)^5247*100000000000000^4223 ≤ 10360918032513^4223*1250000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201586889 1250000000 10360918032513 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336464753/2500000000 : ℝ), (205495597/400000000 : ℝ), (-201586889/1250000000 : ℝ)] ![(5740857264937/12500000000000 : ℝ), (21856111917879/50000000000000 : ℝ), (10360918032513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336464753/2500000000 : ℝ)|^5247 ≤ (5740857264937/12500000000000 : ℝ)^4223
        have hw : |(1336464753/2500000000 : ℝ)|=(1336464753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205495597/400000000 : ℝ)|^5247 ≤ (21856111917879/50000000000000 : ℝ)^4223
        have hw : |(205495597/400000000 : ℝ)|=(205495597/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-201586889/1250000000 : ℝ)|^5247 ≤ (10360918032513/100000000000000 : ℝ)^4223
        have hw : |(-201586889/1250000000 : ℝ)|=(201586889/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_s4_2 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1437931759/10000000000 : ℝ)*x 0 + (5141097733/10000000000 : ℝ)*x 1 + (683844963/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1437931759/10000000000 : ℝ)^5247 ≤ (1796946969151/20000000000000 : ℝ)^4223 := by
    have hnat : (1437931759 : ℕ)^5247*20000000000000^4223 ≤ 1796946969151^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1437931759 10000000000 1796946969151 20000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5141097733/10000000000 : ℝ)^5247 ≤ (21875712798773/50000000000000 : ℝ)^4223 := by
    have hnat : (5141097733 : ℕ)^5247*50000000000000^4223 ≤ 21875712798773^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5141097733 10000000000 21875712798773 50000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683844963/1250000000 : ℝ)^5247 ≤ (23631919771791/50000000000000 : ℝ)^4223 := by
    have hnat : (683844963 : ℕ)^5247*50000000000000^4223 ≤ 23631919771791^4223*1250000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683844963 1250000000 23631919771791 50000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1437931759/10000000000 : ℝ), (5141097733/10000000000 : ℝ), (683844963/1250000000 : ℝ)] ![(1796946969151/20000000000000 : ℝ), (21875712798773/50000000000000 : ℝ), (23631919771791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1437931759/10000000000 : ℝ)|^5247 ≤ (1796946969151/20000000000000 : ℝ)^4223
        have hw : |(-1437931759/10000000000 : ℝ)|=(1437931759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5141097733/10000000000 : ℝ)|^5247 ≤ (21875712798773/50000000000000 : ℝ)^4223
        have hw : |(5141097733/10000000000 : ℝ)|=(5141097733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683844963/1250000000 : ℝ)|^5247 ≤ (23631919771791/50000000000000 : ℝ)^4223
        have hw : |(683844963/1250000000 : ℝ)|=(683844963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_s4_3 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255641311/10000000000 : ℝ)*x 0 + (-79957917/625000000 : ℝ)*x 1 + (8548059/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255641311/10000000000 : ℝ)^5247 ≤ (44965826584953/100000000000000 : ℝ)^4223 := by
    have hnat : (5255641311 : ℕ)^5247*100000000000000^4223 ≤ 44965826584953^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255641311 10000000000 44965826584953 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79957917/625000000 : ℝ)^5247 ≤ (777035473121/10000000000000 : ℝ)^4223 := by
    have hnat : (79957917 : ℕ)^5247*10000000000000^4223 ≤ 777035473121^4223*625000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79957917 625000000 777035473121 10000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8548059/15625000 : ℝ)^5247 ≤ (23631909338109/50000000000000 : ℝ)^4223 := by
    have hnat : (8548059 : ℕ)^5247*50000000000000^4223 ≤ 23631909338109^4223*15625000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8548059 15625000 23631909338109 50000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255641311/10000000000 : ℝ), (-79957917/625000000 : ℝ), (8548059/15625000 : ℝ)] ![(44965826584953/100000000000000 : ℝ), (777035473121/10000000000000 : ℝ), (23631909338109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255641311/10000000000 : ℝ)|^5247 ≤ (44965826584953/100000000000000 : ℝ)^4223
        have hw : |(5255641311/10000000000 : ℝ)|=(5255641311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-79957917/625000000 : ℝ)|^5247 ≤ (777035473121/10000000000000 : ℝ)^4223
        have hw : |(-79957917/625000000 : ℝ)|=(79957917/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8548059/15625000 : ℝ)|^5247 ≤ (23631909338109/50000000000000 : ℝ)^4223
        have hw : |(8548059/15625000 : ℝ)|=(8548059/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_s4_4 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210225697/400000000 : ℝ)*x 0 + (5470759211/10000000000 : ℝ)*x 1 + (-1279323039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210225697/400000000 : ℝ)^5247 ≤ (5620729803393/12500000000000 : ℝ)^4223 := by
    have hnat : (210225697 : ℕ)^5247*12500000000000^4223 ≤ 5620729803393^4223*400000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210225697 400000000 5620729803393 12500000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470759211/10000000000 : ℝ)^5247 ≤ (47263834251601/100000000000000 : ℝ)^4223 := by
    have hnat : (5470759211 : ℕ)^5247*100000000000000^4223 ≤ 47263834251601^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470759211 10000000000 47263834251601 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1279323039/10000000000 : ℝ)^5247 ≤ (1554065462909/20000000000000 : ℝ)^4223 := by
    have hnat : (1279323039 : ℕ)^5247*20000000000000^4223 ≤ 1554065462909^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279323039 10000000000 1554065462909 20000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210225697/400000000 : ℝ), (5470759211/10000000000 : ℝ), (-1279323039/10000000000 : ℝ)] ![(5620729803393/12500000000000 : ℝ), (47263834251601/100000000000000 : ℝ), (1554065462909/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210225697/400000000 : ℝ)|^5247 ≤ (5620729803393/12500000000000 : ℝ)^4223
        have hw : |(210225697/400000000 : ℝ)|=(210225697/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470759211/10000000000 : ℝ)|^5247 ≤ (47263834251601/100000000000000 : ℝ)^4223
        have hw : |(5470759211/10000000000 : ℝ)|=(5470759211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1279323039/10000000000 : ℝ)|^5247 ≤ (1554065462909/20000000000000 : ℝ)^4223
        have hw : |(-1279323039/10000000000 : ℝ)|=(1279323039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_s4_5 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2057121079/5000000000 : ℝ)*x 0 + (4602248019/10000000000 : ℝ)*x 1 + (3661739151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2057121079/5000000000 : ℝ)^5247 ≤ (33171279001993/100000000000000 : ℝ)^4223 := by
    have hnat : (2057121079 : ℕ)^5247*100000000000000^4223 ≤ 33171279001993^4223*5000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057121079 5000000000 33171279001993 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4602248019/10000000000 : ℝ)^5247 ≤ (47660264401/125000000000 : ℝ)^4223 := by
    have hnat : (4602248019 : ℕ)^5247*125000000000^4223 ≤ 47660264401^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4602248019 10000000000 47660264401 125000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3661739151/10000000000 : ℝ)^5247 ≤ (14350254733013/50000000000000 : ℝ)^4223 := by
    have hnat : (3661739151 : ℕ)^5247*50000000000000^4223 ≤ 14350254733013^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3661739151 10000000000 14350254733013 50000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2057121079/5000000000 : ℝ), (4602248019/10000000000 : ℝ), (3661739151/10000000000 : ℝ)] ![(33171279001993/100000000000000 : ℝ), (47660264401/125000000000 : ℝ), (14350254733013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2057121079/5000000000 : ℝ)|^5247 ≤ (33171279001993/100000000000000 : ℝ)^4223
        have hw : |(2057121079/5000000000 : ℝ)|=(2057121079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4602248019/10000000000 : ℝ)|^5247 ≤ (47660264401/125000000000 : ℝ)^4223
        have hw : |(4602248019/10000000000 : ℝ)|=(4602248019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3661739151/10000000000 : ℝ)|^5247 ≤ (14350254733013/50000000000000 : ℝ)^4223
        have hw : |(3661739151/10000000000 : ℝ)|=(3661739151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1703_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (192648977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17143/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (311/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (311/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8571/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17143/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (311/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17143/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (311/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17143/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (311/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17143/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (311/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17143/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (311/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17143/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (311/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (311/3125 : ℝ) ^ (5239/1024 : ℝ) ≤ (746617321048933/100000000000000000000 : ℝ) := by
    have hpowers : (311/3125 : ℝ)^5239 ≤ (746617321048933/100000000000000000000 : ℝ)^1024 := by
      have hnat : (311 : ℕ)^5239*100000000000000000000^1024 ≤ 746617321048933^1024*3125^5239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        311 3125 746617321048933 100000000000000000000 5239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (311/3125 : ℝ)) (X := (746617321048933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5239 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17143/100000 : ℝ) ^ (5239/1024 : ℝ) ≤ (12062203124308387/100000000000000000000 : ℝ) := by
    have hpowers : (17143/100000 : ℝ)^5239 ≤ (12062203124308387/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17143 : ℕ)^5239*100000000000000000000^1024 ≤ 12062203124308387^1024*100000^5239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17143 100000 12062203124308387 100000000000000000000 5239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17143/100000 : ℝ)) (X := (12062203124308387/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5239 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000746617321048933/50000000000000000000 : ℝ) ≤ (5000014593081587/5000000000000000 : ℝ) ^ (5239/1024 : ℝ) := by
    have hpowers : (50000746617321048933/50000000000000000000 : ℝ)^1024 ≤ (5000014593081587/5000000000000000 : ℝ)^5239 := by
      have hnat : (50000746617321048933 : ℕ)^1024*5000000000000000^5239 ≤ 5000014593081587^5239*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000746617321048933 50000000000000000000 5000014593081587 5000000000000000 1024 5239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000014593081587/5000000000000000 : ℝ)) (X := (50000746617321048933/50000000000000000000 : ℝ)) (by norm_num) 5239 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2500320220511133933/2500000000000000000 : ℝ) ≤ (5000125172326381/5000000000000000 : ℝ) ^ (5239/1024 : ℝ) := by
    have hpowers : (2500320220511133933/2500000000000000000 : ℝ)^1024 ≤ (5000125172326381/5000000000000000 : ℝ)^5239 := by
      have hnat : (2500320220511133933 : ℕ)^1024*5000000000000000^5239 ≤ 5000125172326381^5239*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500320220511133933 2500000000000000000 5000125172326381 5000000000000000 1024 5239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000125172326381/5000000000000000 : ℝ)) (X := (2500320220511133933/2500000000000000000 : ℝ)) (by norm_num) 5239 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50012062203124308387/50000000000000000000 : ℝ) ≤ (200009430062847/200000000000000 : ℝ) ^ (5239/1024 : ℝ) := by
    have hpowers : (50012062203124308387/50000000000000000000 : ℝ)^1024 ≤ (200009430062847/200000000000000 : ℝ)^5239 := by
      have hnat : (50012062203124308387 : ℕ)^1024*200000000000000^5239 ≤ 200009430062847^5239*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012062203124308387 50000000000000000000 200009430062847 200000000000000 1024 5239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200009430062847/200000000000000 : ℝ)) (X := (50012062203124308387/50000000000000000000 : ℝ)) (by norm_num) 5239 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(746617321048933/100000000000000000000 : ℝ) ≤ ((35952903969561312341/35955000000000000000 : ℝ)+2*(55289622397/179775000000000 : ℝ)*(311/3125 : ℝ))^(5239/1024 : ℝ) := by
    rw [show (35952903969561312341/35955000000000000000 : ℝ)+2*(55289622397/179775000000000 : ℝ)*(311/3125 : ℝ)=(5000014593081587/5000000000000000 : ℝ) by norm_num, show 1+2*(746617321048933/100000000000000000000 : ℝ)=(50000746617321048933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12062203124308387/100000000000000000000 : ℝ)+(746617321048933/100000000000000000000 : ℝ) ≤ ((35952903969561312341/35955000000000000000 : ℝ)+(55289622397/179775000000000 : ℝ)*((17143/100000 : ℝ)+(311/3125 : ℝ)))^(5239/1024 : ℝ) := by
    rw [show (35952903969561312341/35955000000000000000 : ℝ)+(55289622397/179775000000000 : ℝ)*((17143/100000 : ℝ)+(311/3125 : ℝ))=(5000125172326381/5000000000000000 : ℝ) by norm_num, show 1+(12062203124308387/100000000000000000000 : ℝ)+(746617321048933/100000000000000000000 : ℝ)=(2500320220511133933/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12062203124308387/100000000000000000000 : ℝ) ≤ ((35952903969561312341/35955000000000000000 : ℝ)+2*(55289622397/179775000000000 : ℝ)*(17143/100000 : ℝ))^(5239/1024 : ℝ) := by
    rw [show (35952903969561312341/35955000000000000000 : ℝ)+2*(55289622397/179775000000000 : ℝ)*(17143/100000 : ℝ)=(200009430062847/200000000000000 : ℝ) by norm_num, show 1+2*(12062203124308387/100000000000000000000 : ℝ)=(50012062203124308387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35952903969561312341/35955000000000000000 : ℝ)*(X 1 0+X 2 0)+(55289622397/179775000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5239/1024 : ℝ)) (lo := (311/3125 : ℝ)) (hi := (17143/100000 : ℝ)) (c := (35952903969561312341/35955000000000000000 : ℝ)) (alpha := (55289622397/179775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35952903969561312341/35955000000000000000 : ℝ)*(X 0 1+X 2 1)+(55289622397/179775000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5239/1024 : ℝ)) (lo := (311/3125 : ℝ)) (hi := (17143/100000 : ℝ)) (c := (35952903969561312341/35955000000000000000 : ℝ)) (alpha := (55289622397/179775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35952903969561312341/35955000000000000000 : ℝ)*(X 0 2+X 1 2)+(55289622397/179775000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5239/1024 : ℝ)) (lo := (311/3125 : ℝ)) (hi := (17143/100000 : ℝ)) (c := (35952903969561312341/35955000000000000000 : ℝ)) (alpha := (55289622397/179775000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1437778859/10000000000 : ℝ)*X 0 0+(2737261893/5000000000 : ℝ)*X 0 1+(5137388113/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336464753/2500000000 : ℝ)*X 2 0+(205495597/400000000 : ℝ)*X 2 1+(-201586889/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_s4_1 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-1437931759/10000000000 : ℝ)*X 0 0+(5141097733/10000000000 : ℝ)*X 0 1+(683844963/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_s4_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5255641311/10000000000 : ℝ)*X 1 0+(-79957917/625000000 : ℝ)*X 1 1+(8548059/15625000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_s4_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((210225697/400000000 : ℝ)*X 2 0+(5470759211/10000000000 : ℝ)*X 2 1+(-1279323039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_s4_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2057121079/5000000000 : ℝ)*X 0 0+(4602248019/10000000000 : ℝ)*X 0 1+(3661739151/10000000000 : ℝ)*X 0 2+(2057121079/5000000000 : ℝ)*X 1 0+(4602248019/10000000000 : ℝ)*X 1 1+(3661739151/10000000000 : ℝ)*X 1 2+(2057121079/5000000000 : ℝ)*X 2 0+(4602248019/10000000000 : ℝ)*X 2 1+(3661739151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_s4_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (305231641732113140076763/79687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (26378117/20000000000000 : ℝ)*(base19) + (177450161/25000000000000 : ℝ)*(base23) + (14435537/20000000000000 : ℝ)*(upper1) + (5622627/2000000000000 : ℝ)*(lower2) + (48826981/50000000000000 : ℝ)*(upper5) + (6401103770609/312500000000 : ℝ)*(major0) + (6401103770609/312500000000 : ℝ)*(major1) + (6401103770609/312500000000 : ℝ)*(major2) + (13732077987/100000000000000 : ℝ)*(sp0) + (13685617817/50000000000000 : ℝ)*(sp1) + (1516717913438307/50000000000000 : ℝ)*(sp2) + (189590589191501/6250000000000 : ℝ)*(sp3) + (758355369479581/25000000000000 : ℝ)*(sp4) + (1063256726556549/100000000000000 : ℝ)*(sp5) + (1063256726556549/100000000000000 : ℝ)*(f.failure) + (1516724779477301/50000000000000 : ℝ)*(f.sum) + (86861866601/30600000000000000000000000 : ℝ)*base65 + (3129264694141079/478125000000000000000000000000 : ℝ)*base67 + (6093351966071/466918945312500000000000000 : ℝ)*base69 + (569790580603963/59765625000000000000000000000 : ℝ)*base71 + (305072315783/153000000000000000000000000 : ℝ)*base74 + (5142375206791079/478125000000000000000000000000 : ℝ)*base75 + (665930893398551/119531250000000000000000000000 : ℝ)*base77 + (6334301536609829/478125000000000000000000000000 : ℝ)*base79 + (439218213911/153000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (102499627/10000000000000000000000 : ℝ)*base90 + (102499627/10000000000000000000000 : ℝ)*base92 + (102499627/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1703_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (192648977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17143/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (311/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (311/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8571/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1703_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1703_box_0 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-13920439/125000000 : ℝ)*x 0 + (1084191943/2000000000 : ℝ)*x 1 + (5420959717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13920439/125000000 : ℝ)^5247 ≤ (6540268385889/100000000000000 : ℝ)^4223 := by
    have hnat : (13920439 : ℕ)^5247*100000000000000^4223 ≤ 6540268385889^4223*125000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13920439 125000000 6540268385889 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084191943/2000000000 : ℝ)^5247 ≤ (46729865791703/100000000000000 : ℝ)^4223 := by
    have hnat : (1084191943 : ℕ)^5247*100000000000000^4223 ≤ 46729865791703^4223*2000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084191943 2000000000 46729865791703 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420959717/10000000000 : ℝ)^5247 ≤ (11682466453281/25000000000000 : ℝ)^4223 := by
    have hnat : (5420959717 : ℕ)^5247*25000000000000^4223 ≤ 11682466453281^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420959717 10000000000 11682466453281 25000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13920439/125000000 : ℝ), (1084191943/2000000000 : ℝ), (5420959717/10000000000 : ℝ)] ![(6540268385889/100000000000000 : ℝ), (46729865791703/100000000000000 : ℝ), (11682466453281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13920439/125000000 : ℝ)|^5247 ≤ (6540268385889/100000000000000 : ℝ)^4223
        have hw : |(-13920439/125000000 : ℝ)|=(13920439/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084191943/2000000000 : ℝ)|^5247 ≤ (46729865791703/100000000000000 : ℝ)^4223
        have hw : |(1084191943/2000000000 : ℝ)|=(1084191943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420959717/10000000000 : ℝ)|^5247 ≤ (11682466453281/25000000000000 : ℝ)^4223
        have hw : |(5420959717/10000000000 : ℝ)|=(5420959717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_box_1 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045140473/2000000000 : ℝ)*x 0 + (-347766659/2500000000 : ℝ)*x 1 + (5420959787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045140473/2000000000 : ℝ)^5247 ≤ (22323892880391/50000000000000 : ℝ)^4223 := by
    have hnat : (1045140473 : ℕ)^5247*50000000000000^4223 ≤ 22323892880391^4223*2000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045140473 2000000000 22323892880391 50000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (347766659/2500000000 : ℝ)^5247 ≤ (2155586913591/25000000000000 : ℝ)^4223 := by
    have hnat : (347766659 : ℕ)^5247*25000000000000^4223 ≤ 2155586913591^4223*2500000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347766659 2500000000 2155586913591 25000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5420959787/10000000000 : ℝ)^5247 ≤ (46729866562857/100000000000000 : ℝ)^4223 := by
    have hnat : (5420959787 : ℕ)^5247*100000000000000^4223 ≤ 46729866562857^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420959787 10000000000 46729866562857 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045140473/2000000000 : ℝ), (-347766659/2500000000 : ℝ), (5420959787/10000000000 : ℝ)] ![(22323892880391/50000000000000 : ℝ), (2155586913591/25000000000000 : ℝ), (46729866562857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045140473/2000000000 : ℝ)|^5247 ≤ (22323892880391/50000000000000 : ℝ)^4223
        have hw : |(1045140473/2000000000 : ℝ)|=(1045140473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-347766659/2500000000 : ℝ)|^5247 ≤ (2155586913591/25000000000000 : ℝ)^4223
        have hw : |(-347766659/2500000000 : ℝ)|=(347766659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5420959787/10000000000 : ℝ)|^5247 ≤ (46729866562857/100000000000000 : ℝ)^4223
        have hw : |(5420959787/10000000000 : ℝ)|=(5420959787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_box_2 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225702499/10000000000 : ℝ)*x 0 + (5420959669/10000000000 : ℝ)*x 1 + (-173883327/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225702499/10000000000 : ℝ)^5247 ≤ (1785911487331/4000000000000 : ℝ)^4223 := by
    have hnat : (5225702499 : ℕ)^5247*4000000000000^4223 ≤ 1785911487331^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225702499 10000000000 1785911487331 4000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420959669/10000000000 : ℝ)^5247 ≤ (23364932649511/50000000000000 : ℝ)^4223 := by
    have hnat : (5420959669 : ℕ)^5247*50000000000000^4223 ≤ 23364932649511^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420959669 10000000000 23364932649511 50000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173883327/1250000000 : ℝ)^5247 ≤ (538896718771/6250000000000 : ℝ)^4223 := by
    have hnat : (173883327 : ℕ)^5247*6250000000000^4223 ≤ 538896718771^4223*1250000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173883327 1250000000 538896718771 6250000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225702499/10000000000 : ℝ), (5420959669/10000000000 : ℝ), (-173883327/1250000000 : ℝ)] ![(1785911487331/4000000000000 : ℝ), (23364932649511/50000000000000 : ℝ), (538896718771/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225702499/10000000000 : ℝ)|^5247 ≤ (1785911487331/4000000000000 : ℝ)^4223
        have hw : |(5225702499/10000000000 : ℝ)|=(5225702499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420959669/10000000000 : ℝ)|^5247 ≤ (23364932649511/50000000000000 : ℝ)^4223
        have hw : |(5420959669/10000000000 : ℝ)|=(5420959669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-173883327/1250000000 : ℝ)|^5247 ≤ (538896718771/6250000000000 : ℝ)^4223
        have hw : |(-173883327/1250000000 : ℝ)|=(173883327/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_box_3 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1124110927/2500000000 : ℝ)*x 0 + (493055549/1250000000 : ℝ)*x 1 + (1972222241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1124110927/2500000000 : ℝ)^5247 ≤ (37042159952193/100000000000000 : ℝ)^4223 := by
    have hnat : (1124110927 : ℕ)^5247*100000000000000^4223 ≤ 37042159952193^4223*2500000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124110927 2500000000 37042159952193 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (493055549/1250000000 : ℝ)^5247 ≤ (6295783913943/20000000000000 : ℝ)^4223 := by
    have hnat : (493055549 : ℕ)^5247*20000000000000^4223 ≤ 6295783913943^4223*1250000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493055549 1250000000 6295783913943 20000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1972222241/5000000000 : ℝ)^5247 ≤ (31478920462129/100000000000000 : ℝ)^4223 := by
    have hnat : (1972222241 : ℕ)^5247*100000000000000^4223 ≤ 31478920462129^4223*5000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972222241 5000000000 31478920462129 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1124110927/2500000000 : ℝ), (493055549/1250000000 : ℝ), (1972222241/5000000000 : ℝ)] ![(37042159952193/100000000000000 : ℝ), (6295783913943/20000000000000 : ℝ), (31478920462129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1124110927/2500000000 : ℝ)|^5247 ≤ (37042159952193/100000000000000 : ℝ)^4223
        have hw : |(1124110927/2500000000 : ℝ)|=(1124110927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(493055549/1250000000 : ℝ)|^5247 ≤ (6295783913943/20000000000000 : ℝ)^4223
        have hw : |(493055549/1250000000 : ℝ)|=(493055549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1972222241/5000000000 : ℝ)|^5247 ≤ (31478920462129/100000000000000 : ℝ)^4223
        have hw : |(1972222241/5000000000 : ℝ)|=(1972222241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_box_4 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-891333111/5000000000 : ℝ)*x 0 + (5177126283/10000000000 : ℝ)*x 1 + (323570359/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (891333111/5000000000 : ℝ)^5247 ≤ (183353113661/1562500000000 : ℝ)^4223 := by
    have hnat : (891333111 : ℕ)^5247*1562500000000^4223 ≤ 183353113661^4223*5000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891333111 5000000000 183353113661 1562500000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177126283/10000000000 : ℝ)^5247 ≤ (2206635160541/5000000000000 : ℝ)^4223 := by
    have hnat : (5177126283 : ℕ)^5247*5000000000000^4223 ≤ 2206635160541^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177126283 10000000000 2206635160541 5000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323570359/625000000 : ℝ)^5247 ≤ (22066348750973/50000000000000 : ℝ)^4223 := by
    have hnat : (323570359 : ℕ)^5247*50000000000000^4223 ≤ 22066348750973^4223*625000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323570359 625000000 22066348750973 50000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-891333111/5000000000 : ℝ), (5177126283/10000000000 : ℝ), (323570359/625000000 : ℝ)] ![(183353113661/1562500000000 : ℝ), (2206635160541/5000000000000 : ℝ), (22066348750973/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-891333111/5000000000 : ℝ)|^5247 ≤ (183353113661/1562500000000 : ℝ)^4223
        have hw : |(-891333111/5000000000 : ℝ)|=(891333111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177126283/10000000000 : ℝ)|^5247 ≤ (2206635160541/5000000000000 : ℝ)^4223
        have hw : |(5177126283/10000000000 : ℝ)|=(5177126283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323570359/625000000 : ℝ)|^5247 ≤ (22066348750973/50000000000000 : ℝ)^4223
        have hw : |(323570359/625000000 : ℝ)|=(323570359/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_box_5 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078268961/2000000000 : ℝ)*x 0 + (-374532123/2500000000 : ℝ)*x 1 + (5177125447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078268961/2000000000 : ℝ)^5247 ≤ (9282577341197/20000000000000 : ℝ)^4223 := by
    have hnat : (1078268961 : ℕ)^5247*20000000000000^4223 ≤ 9282577341197^4223*2000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078268961 2000000000 9282577341197 20000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (374532123/2500000000 : ℝ)^5247 ≤ (9454418922403/100000000000000 : ℝ)^4223 := by
    have hnat : (374532123 : ℕ)^5247*100000000000000^4223 ≤ 9454418922403^4223*2500000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374532123 2500000000 9454418922403 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177125447/10000000000 : ℝ)^5247 ≤ (44132694356239/100000000000000 : ℝ)^4223 := by
    have hnat : (5177125447 : ℕ)^5247*100000000000000^4223 ≤ 44132694356239^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177125447 10000000000 44132694356239 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078268961/2000000000 : ℝ), (-374532123/2500000000 : ℝ), (5177125447/10000000000 : ℝ)] ![(9282577341197/20000000000000 : ℝ), (9454418922403/100000000000000 : ℝ), (44132694356239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078268961/2000000000 : ℝ)|^5247 ≤ (9282577341197/20000000000000 : ℝ)^4223
        have hw : |(1078268961/2000000000 : ℝ)|=(1078268961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-374532123/2500000000 : ℝ)|^5247 ≤ (9454418922403/100000000000000 : ℝ)^4223
        have hw : |(-374532123/2500000000 : ℝ)|=(374532123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177125447/10000000000 : ℝ)|^5247 ≤ (44132694356239/100000000000000 : ℝ)^4223
        have hw : |(5177125447/10000000000 : ℝ)|=(5177125447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_box_6 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391345601/10000000000 : ℝ)*x 0 + (647140611/1250000000 : ℝ)*x 1 + (-749064081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391345601/10000000000 : ℝ)^5247 ≤ (23206447610099/50000000000000 : ℝ)^4223 := by
    have hnat : (5391345601 : ℕ)^5247*50000000000000^4223 ≤ 23206447610099^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391345601 10000000000 23206447610099 50000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647140611/1250000000 : ℝ)^5247 ≤ (44132688435533/100000000000000 : ℝ)^4223 := by
    have hnat : (647140611 : ℕ)^5247*100000000000000^4223 ≤ 44132688435533^4223*1250000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647140611 1250000000 44132688435533 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (749064081/5000000000 : ℝ)^5247 ≤ (9454416334847/100000000000000 : ℝ)^4223 := by
    have hnat : (749064081 : ℕ)^5247*100000000000000^4223 ≤ 9454416334847^4223*5000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749064081 5000000000 9454416334847 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391345601/10000000000 : ℝ), (647140611/1250000000 : ℝ), (-749064081/5000000000 : ℝ)] ![(23206447610099/50000000000000 : ℝ), (44132688435533/100000000000000 : ℝ), (9454416334847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391345601/10000000000 : ℝ)|^5247 ≤ (23206447610099/50000000000000 : ℝ)^4223
        have hw : |(5391345601/10000000000 : ℝ)|=(5391345601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647140611/1250000000 : ℝ)|^5247 ≤ (44132688435533/100000000000000 : ℝ)^4223
        have hw : |(647140611/1250000000 : ℝ)|=(647140611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-749064081/5000000000 : ℝ)|^5247 ≤ (9454416334847/100000000000000 : ℝ)^4223
        have hw : |(-749064081/5000000000 : ℝ)|=(749064081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_box_7 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3715876957/10000000000 : ℝ)*x 0 + (866777811/2000000000 : ℝ)*x 1 + (86677791/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3715876957/10000000000 : ℝ)^5247 ≤ (29228672176439/100000000000000 : ℝ)^4223 := by
    have hnat : (3715876957 : ℕ)^5247*100000000000000^4223 ≤ 29228672176439^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3715876957 10000000000 29228672176439 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (866777811/2000000000 : ℝ)^5247 ≤ (17692830694453/50000000000000 : ℝ)^4223 := by
    have hnat : (866777811 : ℕ)^5247*50000000000000^4223 ≤ 17692830694453^4223*2000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866777811 2000000000 17692830694453 50000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86677791/200000000 : ℝ)^5247 ≤ (4423208301317/12500000000000 : ℝ)^4223 := by
    have hnat : (86677791 : ℕ)^5247*12500000000000^4223 ≤ 4423208301317^4223*200000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86677791 200000000 4423208301317 12500000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3715876957/10000000000 : ℝ), (866777811/2000000000 : ℝ), (86677791/200000000 : ℝ)] ![(29228672176439/100000000000000 : ℝ), (17692830694453/50000000000000 : ℝ), (4423208301317/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3715876957/10000000000 : ℝ)|^5247 ≤ (29228672176439/100000000000000 : ℝ)^4223
        have hw : |(3715876957/10000000000 : ℝ)|=(3715876957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(866777811/2000000000 : ℝ)|^5247 ≤ (17692830694453/50000000000000 : ℝ)^4223
        have hw : |(866777811/2000000000 : ℝ)|=(866777811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(86677791/200000000 : ℝ)|^5247 ≤ (4423208301317/12500000000000 : ℝ)^4223
        have hw : |(86677791/200000000 : ℝ)|=(86677791/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_box_8 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-327776097/2000000000 : ℝ)*x 0 + (4997517991/10000000000 : ℝ)*x 1 + (5463992801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327776097/2000000000 : ℝ)^5247 ≤ (2642587786561/25000000000000 : ℝ)^4223 := by
    have hnat : (327776097 : ℕ)^5247*25000000000000^4223 ≤ 2642587786561^4223*2000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327776097 2000000000 2642587786561 25000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4997517991/10000000000 : ℝ)^5247 ≤ (42238435967919/100000000000000 : ℝ)^4223 := by
    have hnat : (4997517991 : ℕ)^5247*100000000000000^4223 ≤ 42238435967919^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4997517991 10000000000 42238435967919 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5463992801/10000000000 : ℝ)^5247 ≤ (11797803218079/25000000000000 : ℝ)^4223 := by
    have hnat : (5463992801 : ℕ)^5247*25000000000000^4223 ≤ 11797803218079^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463992801 10000000000 11797803218079 25000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-327776097/2000000000 : ℝ), (4997517991/10000000000 : ℝ), (5463992801/10000000000 : ℝ)] ![(2642587786561/25000000000000 : ℝ), (42238435967919/100000000000000 : ℝ), (11797803218079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-327776097/2000000000 : ℝ)|^5247 ≤ (2642587786561/25000000000000 : ℝ)^4223
        have hw : |(-327776097/2000000000 : ℝ)|=(327776097/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4997517991/10000000000 : ℝ)|^5247 ≤ (42238435967919/100000000000000 : ℝ)^4223
        have hw : |(4997517991/10000000000 : ℝ)|=(4997517991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5463992801/10000000000 : ℝ)|^5247 ≤ (11797803218079/25000000000000 : ℝ)^4223
        have hw : |(5463992801/10000000000 : ℝ)|=(5463992801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_box_9 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649560707/1250000000 : ℝ)*x 0 + (-342843327/2500000000 : ℝ)*x 1 + (682999109/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649560707/1250000000 : ℝ)^5247 ≤ (2771115181647/6250000000000 : ℝ)^4223 := by
    have hnat : (649560707 : ℕ)^5247*6250000000000^4223 ≤ 2771115181647^4223*1250000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649560707 1250000000 2771115181647 6250000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342843327/2500000000 : ℝ)^5247 ≤ (8470943448311/100000000000000 : ℝ)^4223 := by
    have hnat : (342843327 : ℕ)^5247*100000000000000^4223 ≤ 8470943448311^4223*2500000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342843327 2500000000 8470943448311 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682999109/1250000000 : ℝ)^5247 ≤ (47191213634219/100000000000000 : ℝ)^4223 := by
    have hnat : (682999109 : ℕ)^5247*100000000000000^4223 ≤ 47191213634219^4223*1250000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682999109 1250000000 47191213634219 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649560707/1250000000 : ℝ), (-342843327/2500000000 : ℝ), (682999109/1250000000 : ℝ)] ![(2771115181647/6250000000000 : ℝ), (8470943448311/100000000000000 : ℝ), (47191213634219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649560707/1250000000 : ℝ)|^5247 ≤ (2771115181647/6250000000000 : ℝ)^4223
        have hw : |(649560707/1250000000 : ℝ)|=(649560707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-342843327/2500000000 : ℝ)|^5247 ≤ (8470943448311/100000000000000 : ℝ)^4223
        have hw : |(-342843327/2500000000 : ℝ)|=(342843327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682999109/1250000000 : ℝ)|^5247 ≤ (47191213634219/100000000000000 : ℝ)^4223
        have hw : |(682999109/1250000000 : ℝ)|=(682999109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_box_10 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299121399/2500000000 : ℝ)*x 0 + (5463992991/10000000000 : ℝ)*x 1 + (-171421653/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299121399/2500000000 : ℝ)^5247 ≤ (44337842270281/100000000000000 : ℝ)^4223 := by
    have hnat : (1299121399 : ℕ)^5247*100000000000000^4223 ≤ 44337842270281^4223*2500000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299121399 2500000000 44337842270281 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5463992991/10000000000 : ℝ)^5247 ≤ (4719121491121/10000000000000 : ℝ)^4223 := by
    have hnat : (5463992991 : ℕ)^5247*10000000000000^4223 ≤ 4719121491121^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463992991 10000000000 4719121491121 10000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171421653/1250000000 : ℝ)^5247 ≤ (8470942803629/100000000000000 : ℝ)^4223 := by
    have hnat : (171421653 : ℕ)^5247*100000000000000^4223 ≤ 8470942803629^4223*1250000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171421653 1250000000 8470942803629 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299121399/2500000000 : ℝ), (5463992991/10000000000 : ℝ), (-171421653/1250000000 : ℝ)] ![(44337842270281/100000000000000 : ℝ), (4719121491121/10000000000000 : ℝ), (8470942803629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299121399/2500000000 : ℝ)|^5247 ≤ (44337842270281/100000000000000 : ℝ)^4223
        have hw : |(1299121399/2500000000 : ℝ)|=(1299121399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5463992991/10000000000 : ℝ)|^5247 ≤ (4719121491121/10000000000000 : ℝ)^4223
        have hw : |(5463992991/10000000000 : ℝ)|=(5463992991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-171421653/1250000000 : ℝ)|^5247 ≤ (8470942803629/100000000000000 : ℝ)^4223
        have hw : |(-171421653/1250000000 : ℝ)|=(171421653/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_box_11 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2314601407/5000000000 : ℝ)*x 0 + (3875532733/10000000000 : ℝ)*x 1 + (3875532757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2314601407/5000000000 : ℝ)^5247 ≤ (38405869562353/100000000000000 : ℝ)^4223 := by
    have hnat : (2314601407 : ℕ)^5247*100000000000000^4223 ≤ 38405869562353^4223*5000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2314601407 5000000000 38405869562353 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3875532733/10000000000 : ℝ)^5247 ≤ (481204142093/1562500000000 : ℝ)^4223 := by
    have hnat : (3875532733 : ℕ)^5247*1562500000000^4223 ≤ 481204142093^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3875532733 10000000000 481204142093 1562500000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3875532757/10000000000 : ℝ)^5247 ≤ (15398532665457/50000000000000 : ℝ)^4223 := by
    have hnat : (3875532757 : ℕ)^5247*50000000000000^4223 ≤ 15398532665457^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3875532757 10000000000 15398532665457 50000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2314601407/5000000000 : ℝ), (3875532733/10000000000 : ℝ), (3875532757/10000000000 : ℝ)] ![(38405869562353/100000000000000 : ℝ), (481204142093/1562500000000 : ℝ), (15398532665457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2314601407/5000000000 : ℝ)|^5247 ≤ (38405869562353/100000000000000 : ℝ)^4223
        have hw : |(2314601407/5000000000 : ℝ)|=(2314601407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3875532733/10000000000 : ℝ)|^5247 ≤ (481204142093/1562500000000 : ℝ)^4223
        have hw : |(3875532733/10000000000 : ℝ)|=(3875532733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3875532757/10000000000 : ℝ)|^5247 ≤ (15398532665457/50000000000000 : ℝ)^4223
        have hw : |(3875532757/10000000000 : ℝ)|=(3875532757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_box_12 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1252177299/10000000000 : ℝ)*x 0 + (5591929603/10000000000 : ℝ)*x 1 + (5151932663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1252177299/10000000000 : ℝ)^5247 ≤ (945750025049/12500000000000 : ℝ)^4223 := by
    have hnat : (1252177299 : ℕ)^5247*12500000000000^4223 ≤ 945750025049^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252177299 10000000000 945750025049 12500000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5591929603/10000000000 : ℝ)^5247 ≤ (24283989902517/50000000000000 : ℝ)^4223 := by
    have hnat : (5591929603 : ℕ)^5247*50000000000000^4223 ≤ 24283989902517^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5591929603 10000000000 24283989902517 50000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5151932663/10000000000 : ℝ)^5247 ≤ (27416262489/62500000000 : ℝ)^4223 := by
    have hnat : (5151932663 : ℕ)^5247*62500000000^4223 ≤ 27416262489^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151932663 10000000000 27416262489 62500000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1252177299/10000000000 : ℝ), (5591929603/10000000000 : ℝ), (5151932663/10000000000 : ℝ)] ![(945750025049/12500000000000 : ℝ), (24283989902517/50000000000000 : ℝ), (27416262489/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1252177299/10000000000 : ℝ)|^5247 ≤ (945750025049/12500000000000 : ℝ)^4223
        have hw : |(-1252177299/10000000000 : ℝ)|=(1252177299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5591929603/10000000000 : ℝ)|^5247 ≤ (24283989902517/50000000000000 : ℝ)^4223
        have hw : |(5591929603/10000000000 : ℝ)|=(5591929603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5151932663/10000000000 : ℝ)|^5247 ≤ (27416262489/62500000000 : ℝ)^4223
        have hw : |(5151932663/10000000000 : ℝ)|=(5151932663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_box_13 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5408488673/10000000000 : ℝ)*x 0 + (-754367/5000000 : ℝ)*x 1 + (5151932551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5408488673/10000000000 : ℝ)^5247 ≤ (1863853296261/4000000000000 : ℝ)^4223 := by
    have hnat : (5408488673 : ℕ)^5247*4000000000000^4223 ≤ 1863853296261^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408488673 10000000000 1863853296261 4000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (754367/5000000 : ℝ)^5247 ≤ (9537648781911/100000000000000 : ℝ)^4223 := by
    have hnat : (754367 : ℕ)^5247*100000000000000^4223 ≤ 9537648781911^4223*5000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754367 5000000 9537648781911 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5151932551/10000000000 : ℝ)^5247 ≤ (21933009398771/50000000000000 : ℝ)^4223 := by
    have hnat : (5151932551 : ℕ)^5247*50000000000000^4223 ≤ 21933009398771^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151932551 10000000000 21933009398771 50000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5408488673/10000000000 : ℝ), (-754367/5000000 : ℝ), (5151932551/10000000000 : ℝ)] ![(1863853296261/4000000000000 : ℝ), (9537648781911/100000000000000 : ℝ), (21933009398771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5408488673/10000000000 : ℝ)|^5247 ≤ (1863853296261/4000000000000 : ℝ)^4223
        have hw : |(5408488673/10000000000 : ℝ)|=(5408488673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-754367/5000000 : ℝ)|^5247 ≤ (9537648781911/100000000000000 : ℝ)^4223
        have hw : |(-754367/5000000 : ℝ)|=(754367/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5151932551/10000000000 : ℝ)|^5247 ≤ (21933009398771/50000000000000 : ℝ)^4223
        have hw : |(5151932551/10000000000 : ℝ)|=(5151932551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_box_14 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081697769/2000000000 : ℝ)*x 0 + (2575966187/5000000000 : ℝ)*x 1 + (-301746801/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081697769/2000000000 : ℝ)^5247 ≤ (2912270890481/6250000000000 : ℝ)^4223 := by
    have hnat : (1081697769 : ℕ)^5247*6250000000000^4223 ≤ 2912270890481^4223*2000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081697769 2000000000 2912270890481 6250000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2575966187/5000000000 : ℝ)^5247 ≤ (8773203385009/20000000000000 : ℝ)^4223 := by
    have hnat : (2575966187 : ℕ)^5247*20000000000000^4223 ≤ 8773203385009^4223*5000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575966187 5000000000 8773203385009 20000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (301746801/2000000000 : ℝ)^5247 ≤ (9537648821183/100000000000000 : ℝ)^4223 := by
    have hnat : (301746801 : ℕ)^5247*100000000000000^4223 ≤ 9537648821183^4223*2000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301746801 2000000000 9537648821183 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081697769/2000000000 : ℝ), (2575966187/5000000000 : ℝ), (-301746801/2000000000 : ℝ)] ![(2912270890481/6250000000000 : ℝ), (8773203385009/20000000000000 : ℝ), (9537648821183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081697769/2000000000 : ℝ)|^5247 ≤ (2912270890481/6250000000000 : ℝ)^4223
        have hw : |(1081697769/2000000000 : ℝ)|=(1081697769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2575966187/5000000000 : ℝ)|^5247 ≤ (8773203385009/20000000000000 : ℝ)^4223
        have hw : |(2575966187/5000000000 : ℝ)|=(2575966187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-301746801/2000000000 : ℝ)|^5247 ≤ (9537648821183/100000000000000 : ℝ)^4223
        have hw : |(-301746801/2000000000 : ℝ)|=(301746801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1703_box_15 (p : ℝ) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3632242989/10000000000 : ℝ)*x 0 + (1093504967/2500000000 : ℝ)*x 1 + (4374019123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3632242989/10000000000 : ℝ)^5247 ≤ (28413542121311/100000000000000 : ℝ)^4223 := by
    have hnat : (3632242989 : ℕ)^5247*100000000000000^4223 ≤ 28413542121311^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3632242989 10000000000 28413542121311 100000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093504967/2500000000 : ℝ)^5247 ≤ (7158646543877/20000000000000 : ℝ)^4223 := by
    have hnat : (1093504967 : ℕ)^5247*20000000000000^4223 ≤ 7158646543877^4223*2500000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093504967 2500000000 7158646543877 20000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4374019123/10000000000 : ℝ)^5247 ≤ (8948306286167/25000000000000 : ℝ)^4223 := by
    have hnat : (4374019123 : ℕ)^5247*25000000000000^4223 ≤ 8948306286167^4223*10000000000^5247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374019123 10000000000 8948306286167 25000000000000 5247 4223 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5247/1024 : ℝ)) 5247 4223 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3632242989/10000000000 : ℝ), (1093504967/2500000000 : ℝ), (4374019123/10000000000 : ℝ)] ![(28413542121311/100000000000000 : ℝ), (7158646543877/20000000000000 : ℝ), (8948306286167/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3632242989/10000000000 : ℝ)|^5247 ≤ (28413542121311/100000000000000 : ℝ)^4223
        have hw : |(3632242989/10000000000 : ℝ)|=(3632242989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093504967/2500000000 : ℝ)|^5247 ≤ (7158646543877/20000000000000 : ℝ)^4223
        have hw : |(1093504967/2500000000 : ℝ)|=(1093504967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4374019123/10000000000 : ℝ)|^5247 ≤ (8948306286167/25000000000000 : ℝ)^4223
        have hw : |(4374019123/10000000000 : ℝ)|=(4374019123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1703_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (192648977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8571/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (311/3125 : ℝ)*pair X i i ≤ pair X i h) :
    -(66683/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29119/50000 : ℝ) ∧ (81251/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (90323/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8571/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (311/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8571/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (311/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8571/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (311/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8571/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (311/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8571/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (311/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8571/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (311/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (311/3125 : ℝ) ^ (5239/1024 : ℝ) ≤ (746617321048933/100000000000000000000 : ℝ) := by
    have hpowers : (311/3125 : ℝ)^5239 ≤ (746617321048933/100000000000000000000 : ℝ)^1024 := by
      have hnat : (311 : ℕ)^5239*100000000000000000000^1024 ≤ 746617321048933^1024*3125^5239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        311 3125 746617321048933 100000000000000000000 5239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (311/3125 : ℝ)) (X := (746617321048933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5239 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8571/50000 : ℝ) ^ (5239/1024 : ℝ) ≤ (2411720734911643/20000000000000000000 : ℝ) := by
    have hpowers : (8571/50000 : ℝ)^5239 ≤ (2411720734911643/20000000000000000000 : ℝ)^1024 := by
      have hnat : (8571 : ℕ)^5239*20000000000000000000^1024 ≤ 2411720734911643^1024*50000^5239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8571 50000 2411720734911643 20000000000000000000 5239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8571/50000 : ℝ)) (X := (2411720734911643/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5239 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000746617321048933/50000000000000000000 : ℝ) ≤ (5000014593081587/5000000000000000 : ℝ) ^ (5239/1024 : ℝ) := by
    have hpowers : (50000746617321048933/50000000000000000000 : ℝ)^1024 ≤ (5000014593081587/5000000000000000 : ℝ)^5239 := by
      have hnat : (50000746617321048933 : ℕ)^1024*5000000000000000^5239 ≤ 5000014593081587^5239*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000746617321048933 50000000000000000000 5000014593081587 5000000000000000 1024 5239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000014593081587/5000000000000000 : ℝ)) (X := (50000746617321048933/50000000000000000000 : ℝ)) (by norm_num) 5239 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25003201305248901787/25000000000000000000 : ℝ) ≤ (625015642144137/625000000000000 : ℝ) ^ (5239/1024 : ℝ) := by
    have hpowers : (25003201305248901787/25000000000000000000 : ℝ)^1024 ≤ (625015642144137/625000000000000 : ℝ)^5239 := by
      have hnat : (25003201305248901787 : ℕ)^1024*625000000000000^5239 ≤ 625015642144137^5239*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003201305248901787 25000000000000000000 625015642144137 625000000000000 1024 5239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625015642144137/625000000000000 : ℝ)) (X := (25003201305248901787/25000000000000000000 : ℝ)) (by norm_num) 5239 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10002411720734911643/10000000000000000000 : ℝ) ≤ (1000047136244921/1000000000000000 : ℝ) ^ (5239/1024 : ℝ) := by
    have hpowers : (10002411720734911643/10000000000000000000 : ℝ)^1024 ≤ (1000047136244921/1000000000000000 : ℝ)^5239 := by
      have hnat : (10002411720734911643 : ℕ)^1024*1000000000000000^5239 ≤ 1000047136244921^5239*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002411720734911643 10000000000000000000 1000047136244921 1000000000000000 1024 5239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000047136244921/1000000000000000 : ℝ)) (X := (10002411720734911643/10000000000000000000 : ℝ)) (by norm_num) 5239 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(746617321048933/100000000000000000000 : ℝ) ≤ ((17973952327528647697/17975000000000000000 : ℝ)+2*(110544071509/359500000000000 : ℝ)*(311/3125 : ℝ))^(5239/1024 : ℝ) := by
    rw [show (17973952327528647697/17975000000000000000 : ℝ)+2*(110544071509/359500000000000 : ℝ)*(311/3125 : ℝ)=(5000014593081587/5000000000000000 : ℝ) by norm_num, show 1+2*(746617321048933/100000000000000000000 : ℝ)=(50000746617321048933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2411720734911643/20000000000000000000 : ℝ)+(746617321048933/100000000000000000000 : ℝ) ≤ ((17973952327528647697/17975000000000000000 : ℝ)+(110544071509/359500000000000 : ℝ)*((8571/50000 : ℝ)+(311/3125 : ℝ)))^(5239/1024 : ℝ) := by
    rw [show (17973952327528647697/17975000000000000000 : ℝ)+(110544071509/359500000000000 : ℝ)*((8571/50000 : ℝ)+(311/3125 : ℝ))=(625015642144137/625000000000000 : ℝ) by norm_num, show 1+(2411720734911643/20000000000000000000 : ℝ)+(746617321048933/100000000000000000000 : ℝ)=(25003201305248901787/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2411720734911643/20000000000000000000 : ℝ) ≤ ((17973952327528647697/17975000000000000000 : ℝ)+2*(110544071509/359500000000000 : ℝ)*(8571/50000 : ℝ))^(5239/1024 : ℝ) := by
    rw [show (17973952327528647697/17975000000000000000 : ℝ)+2*(110544071509/359500000000000 : ℝ)*(8571/50000 : ℝ)=(1000047136244921/1000000000000000 : ℝ) by norm_num, show 1+2*(2411720734911643/20000000000000000000 : ℝ)=(10002411720734911643/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17973952327528647697/17975000000000000000 : ℝ)*(X 1 0+X 2 0)+(110544071509/359500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5239/1024 : ℝ)) (lo := (311/3125 : ℝ)) (hi := (8571/50000 : ℝ)) (c := (17973952327528647697/17975000000000000000 : ℝ)) (alpha := (110544071509/359500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17973952327528647697/17975000000000000000 : ℝ)*(X 0 1+X 2 1)+(110544071509/359500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5239/1024 : ℝ)) (lo := (311/3125 : ℝ)) (hi := (8571/50000 : ℝ)) (c := (17973952327528647697/17975000000000000000 : ℝ)) (alpha := (110544071509/359500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17973952327528647697/17975000000000000000 : ℝ)*(X 0 2+X 1 2)+(110544071509/359500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5239/1024 : ℝ)) (lo := (311/3125 : ℝ)) (hi := (8571/50000 : ℝ)) (c := (17973952327528647697/17975000000000000000 : ℝ)) (alpha := (110544071509/359500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-13920439/125000000 : ℝ)*X 0 0+(1084191943/2000000000 : ℝ)*X 0 1+(5420959717/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1045140473/2000000000 : ℝ)*X 1 0+(-347766659/2500000000 : ℝ)*X 1 1+(5420959787/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5225702499/10000000000 : ℝ)*X 2 0+(5420959669/10000000000 : ℝ)*X 2 1+(-173883327/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1124110927/2500000000 : ℝ)*X 0 0+(493055549/1250000000 : ℝ)*X 0 1+(1972222241/5000000000 : ℝ)*X 0 2+(1124110927/2500000000 : ℝ)*X 1 0+(493055549/1250000000 : ℝ)*X 1 1+(1972222241/5000000000 : ℝ)*X 1 2+(1124110927/2500000000 : ℝ)*X 2 0+(493055549/1250000000 : ℝ)*X 2 1+(1972222241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-891333111/5000000000 : ℝ)*X 0 0+(5177126283/10000000000 : ℝ)*X 0 1+(323570359/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1078268961/2000000000 : ℝ)*X 1 0+(-374532123/2500000000 : ℝ)*X 1 1+(5177125447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5391345601/10000000000 : ℝ)*X 2 0+(647140611/1250000000 : ℝ)*X 2 1+(-749064081/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3715876957/10000000000 : ℝ)*X 0 0+(866777811/2000000000 : ℝ)*X 0 1+(86677791/200000000 : ℝ)*X 0 2+(3715876957/10000000000 : ℝ)*X 1 0+(866777811/2000000000 : ℝ)*X 1 1+(86677791/200000000 : ℝ)*X 1 2+(3715876957/10000000000 : ℝ)*X 2 0+(866777811/2000000000 : ℝ)*X 2 1+(86677791/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-327776097/2000000000 : ℝ)*X 0 0+(4997517991/10000000000 : ℝ)*X 0 1+(5463992801/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((649560707/1250000000 : ℝ)*X 1 0+(-342843327/2500000000 : ℝ)*X 1 1+(682999109/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1299121399/2500000000 : ℝ)*X 2 0+(5463992991/10000000000 : ℝ)*X 2 1+(-171421653/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2314601407/5000000000 : ℝ)*X 0 0+(3875532733/10000000000 : ℝ)*X 0 1+(3875532757/10000000000 : ℝ)*X 0 2+(2314601407/5000000000 : ℝ)*X 1 0+(3875532733/10000000000 : ℝ)*X 1 1+(3875532757/10000000000 : ℝ)*X 1 2+(2314601407/5000000000 : ℝ)*X 2 0+(3875532733/10000000000 : ℝ)*X 2 1+(3875532757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1252177299/10000000000 : ℝ)*X 0 0+(5591929603/10000000000 : ℝ)*X 0 1+(5151932663/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5408488673/10000000000 : ℝ)*X 1 0+(-754367/5000000 : ℝ)*X 1 1+(5151932551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1081697769/2000000000 : ℝ)*X 2 0+(2575966187/5000000000 : ℝ)*X 2 1+(-301746801/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3632242989/10000000000 : ℝ)*X 0 0+(1093504967/2500000000 : ℝ)*X 0 1+(4374019123/10000000000 : ℝ)*X 0 2+(3632242989/10000000000 : ℝ)*X 1 0+(1093504967/2500000000 : ℝ)*X 1 1+(4374019123/10000000000 : ℝ)*X 1 2+(3632242989/10000000000 : ℝ)*X 2 0+(1093504967/2500000000 : ℝ)*X 2 1+(4374019123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1703_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66683/100000 : ℝ) ≤ (-11985794285840495064369643011/17975000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18192841/20000000000000 : ℝ)*(upper0) + (132678571/100000000000000 : ℝ)*(lower2) + (26999563/100000000000000 : ℝ)*(lower3) + (669433688796009/50000000000000 : ℝ)*(major0) + (669433688796009/50000000000000 : ℝ)*(major1) + (669433688796009/50000000000000 : ℝ)*(major2) + (4274533221/100000000000000 : ℝ)*(sp1) + (2949792523/50000000000000 : ℝ)*(sp2) + (214989751/50000000000000 : ℝ)*(sp3) + (12531133557973/625000000000 : ℝ)*(sp4) + (200497959343793/10000000000000 : ℝ)*(sp5) + (400995593677221/20000000000000 : ℝ)*(sp6) + (339344356989/48828125000 : ℝ)*(sp7) + (249869547/10000000000000 : ℝ)*(sp8) + (347488836546487/50000000000000 : ℝ)*(f.failure) + (40099677359423/2000000000000 : ℝ)*(f.sum) + (10175679422603/4493750000000000000000000000 : ℝ)*base65 + (199523949582191273/898750000000000000000000000000000 : ℝ)*base67 + (1291540946667808727/898750000000000000000000000000000 : ℝ)*base70 + (14162383966558727/898750000000000000000000000000000 : ℝ)*base72 + (6020507725931/8987500000000000000000000000 : ℝ)*base73 + (1115157645090941273/898750000000000000000000000000000 : ℝ)*base75 + (5414033499863441273/898750000000000000000000000000000 : ℝ)*base77 + (11155726458012808727/898750000000000000000000000000000 : ℝ)*base80 + (24307821250847/4493750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (33493799/5000000000000000000000 : ℝ)*base89 + (33493799/5000000000000000000000 : ℝ)*base91 + (33493799/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29119/50000 : ℝ) ≤ (52343667363321132350007294681927/89875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13875203/100000000000000 : ℝ)*(upper0) + (8953173/50000000000000 : ℝ)*(upper2) + (6638263/100000000000000 : ℝ)*(upper3) + (36732299/100000000000000 : ℝ)*(upper4) + (1998793/20000000000000 : ℝ)*(upper5) + (144164996548197/10000000000000 : ℝ)*(major0) + (144164996548197/10000000000000 : ℝ)*(major1) + (144164996548197/10000000000000 : ℝ)*(major2) + (2115556488711109/100000000000000 : ℝ)*(sp0) + (211555615362163/10000000000000 : ℝ)*(sp1) + (1057777564612129/50000000000000 : ℝ)*(sp2) + (149665987116243/20000000000000 : ℝ)*(sp3) + (167544739/50000000000000 : ℝ)*(sp5) + (1359486851/100000000000000 : ℝ)*(sp10) + (149665987116243/20000000000000 : ℝ)*(f.failure) + (2115556488711109/100000000000000 : ℝ)*(f.sum) + (1172938839877/1797500000000000000000000000 : ℝ)*base66 + (1147034983889047691/179750000000000000000000000000000 : ℝ)*base68 + (100661983237047691/179750000000000000000000000000000 : ℝ)*base70 + (1014046824947202309/179750000000000000000000000000000 : ℝ)*base71 + (28768078462867/1797500000000000000000000000 : ℝ)*base74 + (424254154453702309/179750000000000000000000000000000 : ℝ)*base75 + (873921745143297691/179750000000000000000000000000000 : ℝ)*base78 + (4190766540827047691/179750000000000000000000000000000 : ℝ)*base80 + (280151729473/112343750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5966589/2000000000000000000000 : ℝ)*base90 + (5966589/2000000000000000000000 : ℝ)*base92 + (5966589/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (81251/100000 : ℝ) ≤ (365133385688375025279562136896389/449375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7521519/50000000000000 : ℝ)*(upper0) + (445451/20000000000000 : ℝ)*(upper1) + (6647139/50000000000000 : ℝ)*(upper2) + (1233487/12500000000000 : ℝ)*(upper3) + (25483259/100000000000000 : ℝ)*(upper4) + (732929872938093/50000000000000 : ℝ)*(major0) + (732929872938093/50000000000000 : ℝ)*(major1) + (732929872938093/50000000000000 : ℝ)*(major2) + (880706129/50000000000000 : ℝ)*(sp1) + (2067137451/20000000000000 : ℝ)*(sp2) + (1071869118761543/50000000000000 : ℝ)*(sp8) + (2143736476110827/100000000000000 : ℝ)*(sp9) + (214372790183583/10000000000000 : ℝ)*(sp10) + (380448359680671/50000000000000 : ℝ)*(sp11) + (380448359680671/50000000000000 : ℝ)*(f.failure) + (1071869118761543/50000000000000 : ℝ)*(f.sum) + (2808306189211/1123437500000000000000000000 : ℝ)*base66 + (9302218569805128179/898750000000000000000000000000000 : ℝ)*base68 + (3703128181170128179/898750000000000000000000000000000 : ℝ)*base70 + (6860455166807628179/898750000000000000000000000000000 : ℝ)*base72 + (17282433311069/4493750000000000000000000000 : ℝ)*base74 + (91582466890128179/898750000000000000000000000000000 : ℝ)*base76 + (5373264101453878179/898750000000000000000000000000000 : ℝ)*base78 + (7812222196531378179/898750000000000000000000000000000 : ℝ)*base80 + (4830343950939/1123437500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (14823567/5000000000000000000000 : ℝ)*base89 + (14823567/5000000000000000000000 : ℝ)*base91 + (14823567/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-90323/100000 : ℝ) ≤ (-81175280626620546863413195933059/89875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60996271/100000000000000 : ℝ)*(upper1) + (3243623/25000000000000 : ℝ)*(lower2) + (1282011/4000000000000 : ℝ)*(upper3) + (49506533/100000000000000 : ℝ)*(upper5) + (302870390037351/20000000000000 : ℝ)*(major0) + (302870390037351/20000000000000 : ℝ)*(major1) + (302870390037351/20000000000000 : ℝ)*(major2) + (692904409/50000000000000 : ℝ)*(sp4) + (1904298313/12500000000000 : ℝ)*(sp6) + (1080600089/12500000000000 : ℝ)*(sp7) + (284092656698647/12500000000000 : ℝ)*(sp12) + (1136371319698997/50000000000000 : ℝ)*(sp13) + (227272740501149/10000000000000 : ℝ)*(sp14) + (98257418729157/12500000000000 : ℝ)*(sp15) + (49129249664623/6250000000000 : ℝ)*(f.failure) + (1136371319698997/50000000000000 : ℝ)*(f.sum) + (724504151599/3595000000000000000000000000 : ℝ)*base65 + (895818676421919353/359500000000000000000000000000000 : ℝ)*base68 + (2060779281312919353/359500000000000000000000000000000 : ℝ)*base70 + (367166571051919353/359500000000000000000000000000000 : ℝ)*base72 + (6462501285301/3595000000000000000000000000 : ℝ)*base74 + (1323900127854080647/359500000000000000000000000000000 : ℝ)*base75 + (3583999890175919353/359500000000000000000000000000000 : ℝ)*base78 + (998976550726919353/359500000000000000000000000000000 : ℝ)*base80 + (22957793723609/3595000000000000000000000000 : ℝ)*base81 + (4709329/625000000000000000000 : ℝ)*base90 + (4709329/625000000000000000000 : ℝ)*base92 + (4709329/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1703_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (192648977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8571/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (311/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66683/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29119/50000 : ℝ) else (81251/100000 : ℝ) ≤ X j i ∧ X j i ≤ (90323/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1703_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1703_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (192648977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17157/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (497/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66683/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29119/50000 : ℝ) else (81251/100000 : ℝ) ≤ X j i ∧ X j i ≤ (90323/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1703_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1703_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1703_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5239/1024 : ℝ) ≤ p) (hpb : p ≤ (5247/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (192648977/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17157/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (497/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66683/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29119/50000 : ℝ) else (81251/100000 : ℝ) ≤ X j i ∧ X j i ≤ (90323/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1703_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

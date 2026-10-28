-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1208_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:05:42.802341+00:00
-- url     : https://prove2.me/submissions/bbd3ec0a-a937-4468-9188-4094ffc3348e

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
theorem support_rectangle_w1208_s3_0 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1066289189/5000000000 : ℝ)*x 0 + (5422727271/10000000000 : ℝ)*x 1 + (1047580461/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066289189/5000000000 : ℝ)^8401 ≤ (3239708014431/25000000000000 : ℝ)^6353 := by
    have hnat : (1066289189 : ℕ)^8401*25000000000000^6353 ≤ 3239708014431^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066289189 5000000000 3239708014431 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422727271/10000000000 : ℝ)^8401 ≤ (44518265761741/100000000000000 : ℝ)^6353 := by
    have hnat : (5422727271 : ℕ)^8401*100000000000000^6353 ≤ 44518265761741^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422727271 10000000000 44518265761741 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047580461/2000000000 : ℝ)^8401 ≤ (21261451083069/50000000000000 : ℝ)^6353 := by
    have hnat : (1047580461 : ℕ)^8401*50000000000000^6353 ≤ 21261451083069^6353*2000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047580461 2000000000 21261451083069 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1066289189/5000000000 : ℝ), (5422727271/10000000000 : ℝ), (1047580461/2000000000 : ℝ)] ![(3239708014431/25000000000000 : ℝ), (44518265761741/100000000000000 : ℝ), (21261451083069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1066289189/5000000000 : ℝ)|^8401 ≤ (3239708014431/25000000000000 : ℝ)^6353
        have hw : |(-1066289189/5000000000 : ℝ)|=(1066289189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422727271/10000000000 : ℝ)|^8401 ≤ (44518265761741/100000000000000 : ℝ)^6353
        have hw : |(5422727271/10000000000 : ℝ)|=(5422727271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047580461/2000000000 : ℝ)|^8401 ≤ (21261451083069/50000000000000 : ℝ)^6353
        have hw : |(1047580461/2000000000 : ℝ)|=(1047580461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s3_1 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (535225157/1000000000 : ℝ)*x 0 + (-2226925423/10000000000 : ℝ)*x 1 + (5237902561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535225157/1000000000 : ℝ)^8401 ≤ (43754784112227/100000000000000 : ℝ)^6353 := by
    have hnat : (535225157 : ℕ)^8401*100000000000000^6353 ≤ 43754784112227^6353*1000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535225157 1000000000 43754784112227 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2226925423/10000000000 : ℝ)^8401 ≤ (6861155480153/50000000000000 : ℝ)^6353 := by
    have hnat : (2226925423 : ℕ)^8401*50000000000000^6353 ≤ 6861155480153^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226925423 10000000000 6861155480153 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237902561/10000000000 : ℝ)^8401 ≤ (10630726228599/25000000000000 : ℝ)^6353 := by
    have hnat : (5237902561 : ℕ)^8401*25000000000000^6353 ≤ 10630726228599^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237902561 10000000000 10630726228599 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535225157/1000000000 : ℝ), (-2226925423/10000000000 : ℝ), (5237902561/10000000000 : ℝ)] ![(43754784112227/100000000000000 : ℝ), (6861155480153/50000000000000 : ℝ), (10630726228599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535225157/1000000000 : ℝ)|^8401 ≤ (43754784112227/100000000000000 : ℝ)^6353
        have hw : |(535225157/1000000000 : ℝ)|=(535225157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2226925423/10000000000 : ℝ)|^8401 ≤ (6861155480153/50000000000000 : ℝ)^6353
        have hw : |(-2226925423/10000000000 : ℝ)|=(2226925423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237902561/10000000000 : ℝ)|^8401 ≤ (10630726228599/25000000000000 : ℝ)^6353
        have hw : |(5237902561/10000000000 : ℝ)|=(5237902561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s3_2 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2676125707/5000000000 : ℝ)*x 0 + (81842233/156250000 : ℝ)*x 1 + (-2226925167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676125707/5000000000 : ℝ)^8401 ≤ (43754782425807/100000000000000 : ℝ)^6353 := by
    have hnat : (2676125707 : ℕ)^8401*100000000000000^6353 ≤ 43754782425807^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676125707 5000000000 43754782425807 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81842233/156250000 : ℝ)^8401 ≤ (42522908682517/100000000000000 : ℝ)^6353 := by
    have hnat : (81842233 : ℕ)^8401*100000000000000^6353 ≤ 42522908682517^6353*156250000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81842233 156250000 42522908682517 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2226925167/10000000000 : ℝ)^8401 ≤ (13722308874309/100000000000000 : ℝ)^6353 := by
    have hnat : (2226925167 : ℕ)^8401*100000000000000^6353 ≤ 13722308874309^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226925167 10000000000 13722308874309 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676125707/5000000000 : ℝ), (81842233/156250000 : ℝ), (-2226925167/10000000000 : ℝ)] ![(43754782425807/100000000000000 : ℝ), (42522908682517/100000000000000 : ℝ), (13722308874309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676125707/5000000000 : ℝ)|^8401 ≤ (43754782425807/100000000000000 : ℝ)^6353
        have hw : |(2676125707/5000000000 : ℝ)|=(2676125707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81842233/156250000 : ℝ)|^8401 ≤ (42522908682517/100000000000000 : ℝ)^6353
        have hw : |(81842233/156250000 : ℝ)|=(81842233/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2226925167/10000000000 : ℝ)|^8401 ≤ (13722308874309/100000000000000 : ℝ)^6353
        have hw : |(-2226925167/10000000000 : ℝ)|=(2226925167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s3_3 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088396401/2500000000 : ℝ)*x 0 + (4171249787/10000000000 : ℝ)*x 1 + (4543719467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088396401/2500000000 : ℝ)^8401 ≤ (4162298106827/12500000000000 : ℝ)^6353 := by
    have hnat : (1088396401 : ℕ)^8401*12500000000000^6353 ≤ 4162298106827^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088396401 2500000000 4162298106827 12500000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171249787/10000000000 : ℝ)^8401 ≤ (3933348411273/12500000000000 : ℝ)^6353 := by
    have hnat : (4171249787 : ℕ)^8401*12500000000000^6353 ≤ 3933348411273^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171249787 10000000000 3933348411273 12500000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4543719467/10000000000 : ℝ)^8401 ≤ (35234827849141/100000000000000 : ℝ)^6353 := by
    have hnat : (4543719467 : ℕ)^8401*100000000000000^6353 ≤ 35234827849141^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4543719467 10000000000 35234827849141 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088396401/2500000000 : ℝ), (4171249787/10000000000 : ℝ), (4543719467/10000000000 : ℝ)] ![(4162298106827/12500000000000 : ℝ), (3933348411273/12500000000000 : ℝ), (35234827849141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088396401/2500000000 : ℝ)|^8401 ≤ (4162298106827/12500000000000 : ℝ)^6353
        have hw : |(1088396401/2500000000 : ℝ)|=(1088396401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171249787/10000000000 : ℝ)|^8401 ≤ (3933348411273/12500000000000 : ℝ)^6353
        have hw : |(4171249787/10000000000 : ℝ)|=(4171249787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4543719467/10000000000 : ℝ)|^8401 ≤ (35234827849141/100000000000000 : ℝ)^6353
        have hw : |(4543719467/10000000000 : ℝ)|=(4543719467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s3_4 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2132593707/10000000000 : ℝ)*x 0 + (40926473/78125000 : ℝ)*x 1 + (2711018643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132593707/10000000000 : ℝ)^8401 ≤ (1295895523407/10000000000000 : ℝ)^6353 := by
    have hnat : (2132593707 : ℕ)^8401*10000000000000^6353 ≤ 1295895523407^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132593707 10000000000 1295895523407 10000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40926473/78125000 : ℝ)^8401 ≤ (1063256734043/2500000000000 : ℝ)^6353 := by
    have hnat : (40926473 : ℕ)^8401*2500000000000^6353 ≤ 1063256734043^6353*78125000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40926473 78125000 1063256734043 2500000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711018643/5000000000 : ℝ)^8401 ≤ (11127693847609/25000000000000 : ℝ)^6353 := by
    have hnat : (2711018643 : ℕ)^8401*25000000000000^6353 ≤ 11127693847609^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711018643 5000000000 11127693847609 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2132593707/10000000000 : ℝ), (40926473/78125000 : ℝ), (2711018643/5000000000 : ℝ)] ![(1295895523407/10000000000000 : ℝ), (1063256734043/2500000000000 : ℝ), (11127693847609/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2132593707/10000000000 : ℝ)|^8401 ≤ (1295895523407/10000000000000 : ℝ)^6353
        have hw : |(-2132593707/10000000000 : ℝ)|=(2132593707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40926473/78125000 : ℝ)|^8401 ≤ (1063256734043/2500000000000 : ℝ)^6353
        have hw : |(40926473/78125000 : ℝ)|=(40926473/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711018643/5000000000 : ℝ)|^8401 ≤ (11127693847609/25000000000000 : ℝ)^6353
        have hw : |(2711018643/5000000000 : ℝ)|=(2711018643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s3_5 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652603729/5000000000 : ℝ)*x 0 + (-408558147/2000000000 : ℝ)*x 1 + (677754621/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652603729/5000000000 : ℝ)^8401 ≤ (43246941094559/100000000000000 : ℝ)^6353 := by
    have hnat : (2652603729 : ℕ)^8401*100000000000000^6353 ≤ 43246941094559^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652603729 5000000000 43246941094559 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (408558147/2000000000 : ℝ)^8401 ≤ (12242286952647/100000000000000 : ℝ)^6353 := by
    have hnat : (408558147 : ℕ)^8401*100000000000000^6353 ≤ 12242286952647^6353*2000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408558147 2000000000 12242286952647 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677754621/1250000000 : ℝ)^8401 ≤ (11127692984587/25000000000000 : ℝ)^6353 := by
    have hnat : (677754621 : ℕ)^8401*25000000000000^6353 ≤ 11127692984587^6353*1250000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677754621 1250000000 11127692984587 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652603729/5000000000 : ℝ), (-408558147/2000000000 : ℝ), (677754621/1250000000 : ℝ)] ![(43246941094559/100000000000000 : ℝ), (12242286952647/100000000000000 : ℝ), (11127692984587/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652603729/5000000000 : ℝ)|^8401 ≤ (43246941094559/100000000000000 : ℝ)^6353
        have hw : |(2652603729/5000000000 : ℝ)|=(2652603729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-408558147/2000000000 : ℝ)|^8401 ≤ (12242286952647/100000000000000 : ℝ)^6353
        have hw : |(-408558147/2000000000 : ℝ)|=(408558147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677754621/1250000000 : ℝ)|^8401 ≤ (11127692984587/25000000000000 : ℝ)^6353
        have hw : |(677754621/1250000000 : ℝ)|=(677754621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s3_6 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305207329/10000000000 : ℝ)*x 0 + (2711018479/5000000000 : ℝ)*x 1 + (-510697731/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305207329/10000000000 : ℝ)^8401 ≤ (43246939703983/100000000000000 : ℝ)^6353 := by
    have hnat : (5305207329 : ℕ)^8401*100000000000000^6353 ≤ 43246939703983^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305207329 10000000000 43246939703983 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711018479/5000000000 : ℝ)^8401 ≤ (1390961619681/3125000000000 : ℝ)^6353 := by
    have hnat : (2711018479 : ℕ)^8401*3125000000000^6353 ≤ 1390961619681^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711018479 5000000000 1390961619681 3125000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (510697731/2500000000 : ℝ)^8401 ≤ (6121144225221/50000000000000 : ℝ)^6353 := by
    have hnat : (510697731 : ℕ)^8401*50000000000000^6353 ≤ 6121144225221^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510697731 2500000000 6121144225221 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305207329/10000000000 : ℝ), (2711018479/5000000000 : ℝ), (-510697731/2500000000 : ℝ)] ![(43246939703983/100000000000000 : ℝ), (1390961619681/3125000000000 : ℝ), (6121144225221/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305207329/10000000000 : ℝ)|^8401 ≤ (43246939703983/100000000000000 : ℝ)^6353
        have hw : |(5305207329/10000000000 : ℝ)|=(5305207329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711018479/5000000000 : ℝ)|^8401 ≤ (1390961619681/3125000000000 : ℝ)^6353
        have hw : |(2711018479/5000000000 : ℝ)|=(2711018479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-510697731/2500000000 : ℝ)|^8401 ≤ (6121144225221/50000000000000 : ℝ)^6353
        have hw : |(-510697731/2500000000 : ℝ)|=(510697731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s3_7 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353616591/10000000000 : ℝ)*x 0 + (567792021/1250000000 : ℝ)*x 1 + (834528039/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353616591/10000000000 : ℝ)^8401 ≤ (3329869826129/10000000000000 : ℝ)^6353 := by
    have hnat : (4353616591 : ℕ)^8401*10000000000000^6353 ≤ 3329869826129^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353616591 10000000000 3329869826129 10000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (567792021/1250000000 : ℝ)^8401 ≤ (35220643561711/100000000000000 : ℝ)^6353 := by
    have hnat : (567792021 : ℕ)^8401*100000000000000^6353 ≤ 35220643561711^6353*1250000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567792021 1250000000 35220643561711 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834528039/2000000000 : ℝ)^8401 ≤ (3935082270917/12500000000000 : ℝ)^6353 := by
    have hnat : (834528039 : ℕ)^8401*12500000000000^6353 ≤ 3935082270917^6353*2000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834528039 2000000000 3935082270917 12500000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353616591/10000000000 : ℝ), (567792021/1250000000 : ℝ), (834528039/2000000000 : ℝ)] ![(3329869826129/10000000000000 : ℝ), (35220643561711/100000000000000 : ℝ), (3935082270917/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353616591/10000000000 : ℝ)|^8401 ≤ (3329869826129/10000000000000 : ℝ)^6353
        have hw : |(4353616591/10000000000 : ℝ)|=(4353616591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(567792021/1250000000 : ℝ)|^8401 ≤ (35220643561711/100000000000000 : ℝ)^6353
        have hw : |(567792021/1250000000 : ℝ)|=(567792021/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(834528039/2000000000 : ℝ)|^8401 ≤ (3935082270917/12500000000000 : ℝ)^6353
        have hw : |(834528039/2000000000 : ℝ)|=(834528039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1208_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8157/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4679/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5411/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14733/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8157/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4679/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8157/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4679/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8157/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4679/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8157/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4679/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8157/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4679/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8157/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4679/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4679/50000 : ℝ) ^ (525/128 : ℝ) ≤ (753620934490373/12500000000000000000 : ℝ) := by
    have hpowers : (4679/50000 : ℝ)^525 ≤ (753620934490373/12500000000000000000 : ℝ)^128 := by
      have hnat : (4679 : ℕ)^525*12500000000000000000^128 ≤ 753620934490373^128*50000^525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4679 50000 753620934490373 12500000000000000000 525 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4679/50000 : ℝ)) (X := (753620934490373/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hpowhi : (8157/50000 : ℝ) ^ (525/128 : ℝ) ≤ (58920646493814201/100000000000000000000 : ℝ) := by
    have hpowers : (8157/50000 : ℝ)^525 ≤ (58920646493814201/100000000000000000000 : ℝ)^128 := by
      have hnat : (8157 : ℕ)^525*100000000000000000000^128 ≤ 58920646493814201^128*50000^525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8157 50000 58920646493814201 100000000000000000000 525 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8157/50000 : ℝ)) (X := (58920646493814201/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250753620934490373/6250000000000000000 : ℝ) ≤ (625018373158497/625000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (6250753620934490373/6250000000000000000 : ℝ)^128 ≤ (625018373158497/625000000000000 : ℝ)^525 := by
      have hnat : (6250753620934490373 : ℕ)^128*625000000000000^525 ≤ 625018373158497^525*6250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250753620934490373 6250000000000000000 625018373158497 625000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625018373158497/625000000000000 : ℝ)) (X := (6250753620934490373/6250000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (20012989922793947437/20000000000000000000 : ℝ) ≤ (156274736636291/156250000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (20012989922793947437/20000000000000000000 : ℝ)^128 ≤ (156274736636291/156250000000000 : ℝ)^525 := by
      have hnat : (20012989922793947437 : ℕ)^128*156250000000000^525 ≤ 156274736636291^525*20000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20012989922793947437 20000000000000000000 156274736636291 156250000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156274736636291/156250000000000 : ℝ)) (X := (20012989922793947437/20000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50058920646493814201/50000000000000000000 : ℝ) ≤ (625179519931831/625000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (50058920646493814201/50000000000000000000 : ℝ)^128 ≤ (625179519931831/625000000000000 : ℝ)^525 := by
      have hnat : (50058920646493814201 : ℕ)^128*625000000000000^525 ≤ 625179519931831^525*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50058920646493814201 50000000000000000000 625179519931831 625000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625179519931831/625000000000000 : ℝ)) (X := (50058920646493814201/50000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(753620934490373/12500000000000000000 : ℝ) ≤ ((108652994804641139/108687500000000000 : ℝ)+2*(80573386667/43475000000000 : ℝ)*(4679/50000 : ℝ))^(525/128 : ℝ) := by
    rw [show (108652994804641139/108687500000000000 : ℝ)+2*(80573386667/43475000000000 : ℝ)*(4679/50000 : ℝ)=(625018373158497/625000000000000 : ℝ) by norm_num, show 1+2*(753620934490373/12500000000000000000 : ℝ)=(6250753620934490373/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(58920646493814201/100000000000000000000 : ℝ)+(753620934490373/12500000000000000000 : ℝ) ≤ ((108652994804641139/108687500000000000 : ℝ)+(80573386667/43475000000000 : ℝ)*((8157/50000 : ℝ)+(4679/50000 : ℝ)))^(525/128 : ℝ) := by
    rw [show (108652994804641139/108687500000000000 : ℝ)+(80573386667/43475000000000 : ℝ)*((8157/50000 : ℝ)+(4679/50000 : ℝ))=(156274736636291/156250000000000 : ℝ) by norm_num, show 1+(58920646493814201/100000000000000000000 : ℝ)+(753620934490373/12500000000000000000 : ℝ)=(20012989922793947437/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(58920646493814201/100000000000000000000 : ℝ) ≤ ((108652994804641139/108687500000000000 : ℝ)+2*(80573386667/43475000000000 : ℝ)*(8157/50000 : ℝ))^(525/128 : ℝ) := by
    rw [show (108652994804641139/108687500000000000 : ℝ)+2*(80573386667/43475000000000 : ℝ)*(8157/50000 : ℝ)=(625179519931831/625000000000000 : ℝ) by norm_num, show 1+2*(58920646493814201/100000000000000000000 : ℝ)=(50058920646493814201/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (108652994804641139/108687500000000000 : ℝ)*(X 1 0+X 2 0)+(80573386667/43475000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (4679/50000 : ℝ)) (hi := (8157/50000 : ℝ)) (c := (108652994804641139/108687500000000000 : ℝ)) (alpha := (80573386667/43475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (108652994804641139/108687500000000000 : ℝ)*(X 0 1+X 2 1)+(80573386667/43475000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (4679/50000 : ℝ)) (hi := (8157/50000 : ℝ)) (c := (108652994804641139/108687500000000000 : ℝ)) (alpha := (80573386667/43475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (108652994804641139/108687500000000000 : ℝ)*(X 0 2+X 1 2)+(80573386667/43475000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (4679/50000 : ℝ)) (hi := (8157/50000 : ℝ)) (c := (108652994804641139/108687500000000000 : ℝ)) (alpha := (80573386667/43475000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1066289189/5000000000 : ℝ)*X 0 0+(5422727271/10000000000 : ℝ)*X 0 1+(1047580461/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535225157/1000000000 : ℝ)*X 1 0+(-2226925423/10000000000 : ℝ)*X 1 1+(5237902561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676125707/5000000000 : ℝ)*X 2 0+(81842233/156250000 : ℝ)*X 2 1+(-2226925167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088396401/2500000000 : ℝ)*X 0 0+(4171249787/10000000000 : ℝ)*X 0 1+(4543719467/10000000000 : ℝ)*X 0 2+(1088396401/2500000000 : ℝ)*X 1 0+(4171249787/10000000000 : ℝ)*X 1 1+(4543719467/10000000000 : ℝ)*X 1 2+(1088396401/2500000000 : ℝ)*X 2 0+(4171249787/10000000000 : ℝ)*X 2 1+(4543719467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2132593707/10000000000 : ℝ)*X 0 0+(40926473/78125000 : ℝ)*X 0 1+(2711018643/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652603729/5000000000 : ℝ)*X 1 0+(-408558147/2000000000 : ℝ)*X 1 1+(677754621/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305207329/10000000000 : ℝ)*X 2 0+(2711018479/5000000000 : ℝ)*X 2 1+(-510697731/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353616591/10000000000 : ℝ)*X 0 0+(567792021/1250000000 : ℝ)*X 0 1+(834528039/2000000000 : ℝ)*X 0 2+(4353616591/10000000000 : ℝ)*X 1 0+(567792021/1250000000 : ℝ)*X 1 1+(834528039/2000000000 : ℝ)*X 1 2+(4353616591/10000000000 : ℝ)*X 2 0+(567792021/1250000000 : ℝ)*X 2 1+(834528039/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23974081956921672117683427/5434375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (179654557/50000000000000 : ℝ)*(base19) + (275211/390625000000 : ℝ)*(base23) + (20924823/25000000000000 : ℝ)*(lower2) + (17135427/50000000000000 : ℝ)*(upper5) + (4047678075032203/100000000000000 : ℝ)*(major0) + (4047678075032203/100000000000000 : ℝ)*(major1) + (4047678075032203/100000000000000 : ℝ)*(major2) + (5410542120716389/100000000000000 : ℝ)*(sp0) + (5410558576067687/100000000000000 : ℝ)*(sp1) + (541056173489703/10000000000000 : ℝ)*(sp2) + (268478839525933/10000000000000 : ℝ)*(sp3) + (19684634657/100000000000000 : ℝ)*(sp4) + (717493561/25000000000000 : ℝ)*(sp5) + (5802401961/100000000000000 : ℝ)*(sp7) + (268479419766129/10000000000000 : ℝ)*(f.failure) + (1082112361070209/20000000000000 : ℝ)*(f.sum) + (217396951373/4347500000000000000000000000 : ℝ)*base66 + (2606443197367033/10868750000000000000000000000000 : ℝ)*base68 + (9918757918176717/10868750000000000000000000000000 : ℝ)*base69 + (108915302347942033/10868750000000000000000000000000 : ℝ)*base72 + (7525717822789/8695000000000000000000000000 : ℝ)*base73 + (49710476640748283/10868750000000000000000000000000 : ℝ)*base76 + (68191944633204533/10868750000000000000000000000000 : ℝ)*base78 + (22003222384160783/10868750000000000000000000000000 : ℝ)*base80 + (45283306229421/8695000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (757643/1000000000000000000000 : ℝ)*base89 + (757643/1000000000000000000000 : ℝ)*base91 + (757643/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12913739316405328355781/4625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (181370143/25000000000000 : ℝ)*(base19) + (72936053/10000000000000 : ℝ)*(base23) + (49156853/50000000000000 : ℝ)*(lower4) + (105061149/100000000000000 : ℝ)*(upper5) + (40780240666417/1000000000000 : ℝ)*(major0) + (40780240666417/1000000000000 : ℝ)*(major1) + (40780240666417/1000000000000 : ℝ)*(major2) + (5586161669/100000000000000 : ℝ)*(sp0) + (1420903959/10000000000000 : ℝ)*(sp1) + (8695964193/100000000000000 : ℝ)*(sp2) + (5451119990087317/100000000000000 : ℝ)*(sp4) + (681388830216103/12500000000000 : ℝ)*(sp5) + (5451116150924263/100000000000000 : ℝ)*(sp6) + (270492246396241/10000000000000 : ℝ)*(sp7) + (270492246396241/10000000000000 : ℝ)*(f.failure) + (2725562788124493/50000000000000 : ℝ)*(f.sum) + (1043280109231/1739000000000000000000000000 : ℝ)*base66 + (2515054796758801/217375000000000000000000000000 : ℝ)*base67 + (944259130487551/217375000000000000000000000000 : ℝ)*base69 + (48342385585511/13585937500000000000000000000 : ℝ)*base71 + (893603162799/173900000000000000000000000 : ℝ)*base73 + (510919382419713/108687500000000000000000000000 : ℝ)*base75 + (468910418662801/217375000000000000000000000000 : ℝ)*base77 + (26016559484909/3396484375000000000000000000 : ℝ)*base79 + (2947901576647/1739000000000000000000000000 : ℝ)*base81 + (9568853/1000000000000000000000 : ℝ)*base90 + (9568853/1000000000000000000000 : ℝ)*base92 + (9568853/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1208_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8157/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4679/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5411/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1208_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1208_s4_0 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1067545423/5000000000 : ℝ)*x 0 + (5398902151/10000000000 : ℝ)*x 1 + (5260082103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067545423/5000000000 : ℝ)^8401 ≤ (519160993241/4000000000000 : ℝ)^6353 := by
    have hnat : (1067545423 : ℕ)^8401*4000000000000^6353 ≤ 519160993241^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067545423 5000000000 519160993241 4000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398902151/10000000000 : ℝ)^8401 ≤ (8851960391623/20000000000000 : ℝ)^6353 := by
    have hnat : (5398902151 : ℕ)^8401*20000000000000^6353 ≤ 8851960391623^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398902151 10000000000 8851960391623 20000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260082103/10000000000 : ℝ)^8401 ≤ (42761173202629/100000000000000 : ℝ)^6353 := by
    have hnat : (5260082103 : ℕ)^8401*100000000000000^6353 ≤ 42761173202629^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260082103 10000000000 42761173202629 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1067545423/5000000000 : ℝ), (5398902151/10000000000 : ℝ), (5260082103/10000000000 : ℝ)] ![(519160993241/4000000000000 : ℝ), (8851960391623/20000000000000 : ℝ), (42761173202629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1067545423/5000000000 : ℝ)|^8401 ≤ (519160993241/4000000000000 : ℝ)^6353
        have hw : |(-1067545423/5000000000 : ℝ)|=(1067545423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398902151/10000000000 : ℝ)|^8401 ≤ (8851960391623/20000000000000 : ℝ)^6353
        have hw : |(5398902151/10000000000 : ℝ)|=(5398902151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260082103/10000000000 : ℝ)|^8401 ≤ (42761173202629/100000000000000 : ℝ)^6353
        have hw : |(5260082103/10000000000 : ℝ)|=(5260082103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s4_1 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673132259/5000000000 : ℝ)*x 0 + (-1102796417/5000000000 : ℝ)*x 1 + (2630041071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673132259/5000000000 : ℝ)^8401 ≤ (43690073448223/100000000000000 : ℝ)^6353 := by
    have hnat : (2673132259 : ℕ)^8401*100000000000000^6353 ≤ 43690073448223^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673132259 5000000000 43690073448223 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102796417/5000000000 : ℝ)^8401 ≤ (423398528811/3125000000000 : ℝ)^6353 := by
    have hnat : (1102796417 : ℕ)^8401*3125000000000^6353 ≤ 423398528811^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102796417 5000000000 423398528811 3125000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630041071/5000000000 : ℝ)^8401 ≤ (1069029340547/2500000000000 : ℝ)^6353 := by
    have hnat : (2630041071 : ℕ)^8401*2500000000000^6353 ≤ 1069029340547^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630041071 5000000000 1069029340547 2500000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673132259/5000000000 : ℝ), (-1102796417/5000000000 : ℝ), (2630041071/5000000000 : ℝ)] ![(43690073448223/100000000000000 : ℝ), (423398528811/3125000000000 : ℝ), (1069029340547/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673132259/5000000000 : ℝ)|^8401 ≤ (43690073448223/100000000000000 : ℝ)^6353
        have hw : |(2673132259/5000000000 : ℝ)|=(2673132259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1102796417/5000000000 : ℝ)|^8401 ≤ (423398528811/3125000000000 : ℝ)^6353
        have hw : |(-1102796417/5000000000 : ℝ)|=(1102796417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630041071/5000000000 : ℝ)|^8401 ≤ (1069029340547/2500000000000 : ℝ)^6353
        have hw : |(2630041071/5000000000 : ℝ)|=(2630041071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s4_2 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346264539/10000000000 : ℝ)*x 0 + (5260082119/10000000000 : ℝ)*x 1 + (-551398209/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346264539/10000000000 : ℝ)^8401 ≤ (43690073675159/100000000000000 : ℝ)^6353 := by
    have hnat : (5346264539 : ℕ)^8401*100000000000000^6353 ≤ 43690073675159^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346264539 10000000000 43690073675159 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260082119/10000000000 : ℝ)^8401 ≤ (42761173374629/100000000000000 : ℝ)^6353 := by
    have hnat : (5260082119 : ℕ)^8401*100000000000000^6353 ≤ 42761173374629^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260082119 10000000000 42761173374629 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (551398209/2500000000 : ℝ)^8401 ≤ (6774376469099/50000000000000 : ℝ)^6353 := by
    have hnat : (551398209 : ℕ)^8401*50000000000000^6353 ≤ 6774376469099^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551398209 2500000000 6774376469099 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346264539/10000000000 : ℝ), (5260082119/10000000000 : ℝ), (-551398209/2500000000 : ℝ)] ![(43690073675159/100000000000000 : ℝ), (42761173374629/100000000000000 : ℝ), (6774376469099/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346264539/10000000000 : ℝ)|^8401 ≤ (43690073675159/100000000000000 : ℝ)^6353
        have hw : |(5346264539/10000000000 : ℝ)|=(5346264539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260082119/10000000000 : ℝ)|^8401 ≤ (42761173374629/100000000000000 : ℝ)^6353
        have hw : |(5260082119/10000000000 : ℝ)|=(5260082119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-551398209/2500000000 : ℝ)|^8401 ≤ (6774376469099/50000000000000 : ℝ)^6353
        have hw : |(-551398209/2500000000 : ℝ)|=(551398209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s4_3 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (34024147/78125000 : ℝ)*x 0 + (210870611/500000000 : ℝ)*x 1 + (4497170801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34024147/78125000 : ℝ)^8401 ≤ (33313609601503/100000000000000 : ℝ)^6353 := by
    have hnat : (34024147 : ℕ)^8401*100000000000000^6353 ≤ 33313609601503^6353*78125000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34024147 78125000 33313609601503 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210870611/500000000 : ℝ)^8401 ≤ (31928103911123/100000000000000 : ℝ)^6353 := by
    have hnat : (210870611 : ℕ)^8401*100000000000000^6353 ≤ 31928103911123^6353*500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210870611 500000000 31928103911123 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497170801/10000000000 : ℝ)^8401 ≤ (34758286472159/100000000000000 : ℝ)^6353 := by
    have hnat : (4497170801 : ℕ)^8401*100000000000000^6353 ≤ 34758286472159^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497170801 10000000000 34758286472159 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34024147/78125000 : ℝ), (210870611/500000000 : ℝ), (4497170801/10000000000 : ℝ)] ![(33313609601503/100000000000000 : ℝ), (31928103911123/100000000000000 : ℝ), (34758286472159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34024147/78125000 : ℝ)|^8401 ≤ (33313609601503/100000000000000 : ℝ)^6353
        have hw : |(34024147/78125000 : ℝ)|=(34024147/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210870611/500000000 : ℝ)|^8401 ≤ (31928103911123/100000000000000 : ℝ)^6353
        have hw : |(210870611/500000000 : ℝ)|=(210870611/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497170801/10000000000 : ℝ)|^8401 ≤ (34758286472159/100000000000000 : ℝ)^6353
        have hw : |(4497170801/10000000000 : ℝ)|=(4497170801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s4_4 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-427019547/2000000000 : ℝ)*x 0 + (5260470243/10000000000 : ℝ)*x 1 + (5398512139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427019547/2000000000 : ℝ)^8401 ≤ (10139906413/78125000000 : ℝ)^6353 := by
    have hnat : (427019547 : ℕ)^8401*78125000000^6353 ≤ 10139906413^6353*2000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427019547 2000000000 10139906413 78125000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260470243/10000000000 : ℝ)^8401 ≤ (42765345764501/100000000000000 : ℝ)^6353 := by
    have hnat : (5260470243 : ℕ)^8401*100000000000000^6353 ≤ 42765345764501^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260470243 10000000000 42765345764501 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398512139/10000000000 : ℝ)^8401 ≤ (11063893503953/25000000000000 : ℝ)^6353 := by
    have hnat : (5398512139 : ℕ)^8401*25000000000000^6353 ≤ 11063893503953^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398512139 10000000000 11063893503953 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-427019547/2000000000 : ℝ), (5260470243/10000000000 : ℝ), (5398512139/10000000000 : ℝ)] ![(10139906413/78125000000 : ℝ), (42765345764501/100000000000000 : ℝ), (11063893503953/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-427019547/2000000000 : ℝ)|^8401 ≤ (10139906413/78125000000 : ℝ)^6353
        have hw : |(-427019547/2000000000 : ℝ)|=(427019547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260470243/10000000000 : ℝ)|^8401 ≤ (42765345764501/100000000000000 : ℝ)^6353
        have hw : |(5260470243/10000000000 : ℝ)|=(5260470243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398512139/10000000000 : ℝ)|^8401 ≤ (11063893503953/25000000000000 : ℝ)^6353
        have hw : |(5398512139/10000000000 : ℝ)|=(5398512139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s4_5 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310928433/10000000000 : ℝ)*x 0 + (-103358121/500000000 : ℝ)*x 1 + (2699256289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310928433/10000000000 : ℝ)^8401 ≤ (43308621989281/100000000000000 : ℝ)^6353 := by
    have hnat : (5310928433 : ℕ)^8401*100000000000000^6353 ≤ 43308621989281^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310928433 10000000000 43308621989281 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103358121/500000000 : ℝ)^8401 ≤ (3108949802493/25000000000000 : ℝ)^6353 := by
    have hnat : (103358121 : ℕ)^8401*25000000000000^6353 ≤ 3108949802493^6353*500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103358121 500000000 3108949802493 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699256289/5000000000 : ℝ)^8401 ≤ (11063894693689/25000000000000 : ℝ)^6353 := by
    have hnat : (2699256289 : ℕ)^8401*25000000000000^6353 ≤ 11063894693689^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699256289 5000000000 11063894693689 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310928433/10000000000 : ℝ), (-103358121/500000000 : ℝ), (2699256289/5000000000 : ℝ)] ![(43308621989281/100000000000000 : ℝ), (3108949802493/25000000000000 : ℝ), (11063894693689/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310928433/10000000000 : ℝ)|^8401 ≤ (43308621989281/100000000000000 : ℝ)^6353
        have hw : |(5310928433/10000000000 : ℝ)|=(5310928433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103358121/500000000 : ℝ)|^8401 ≤ (3108949802493/25000000000000 : ℝ)^6353
        have hw : |(-103358121/500000000 : ℝ)|=(103358121/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699256289/5000000000 : ℝ)|^8401 ≤ (11063894693689/25000000000000 : ℝ)^6353
        have hw : |(2699256289/5000000000 : ℝ)|=(2699256289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s4_6 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310928121/10000000000 : ℝ)*x 0 + (5398513209/10000000000 : ℝ)*x 1 + (-16149703/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310928121/10000000000 : ℝ)^8401 ≤ (21654309312429/50000000000000 : ℝ)^6353 := by
    have hnat : (5310928121 : ℕ)^8401*50000000000000^6353 ≤ 21654309312429^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310928121 10000000000 21654309312429 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398513209/10000000000 : ℝ)^8401 ≤ (2212779280753/5000000000000 : ℝ)^6353 := by
    have hnat : (5398513209 : ℕ)^8401*5000000000000^6353 ≤ 2212779280753^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398513209 10000000000 2212779280753 5000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16149703/78125000 : ℝ)^8401 ≤ (194309308461/1562500000000 : ℝ)^6353 := by
    have hnat : (16149703 : ℕ)^8401*1562500000000^6353 ≤ 194309308461^6353*78125000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16149703 78125000 194309308461 1562500000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310928121/10000000000 : ℝ), (5398513209/10000000000 : ℝ), (-16149703/78125000 : ℝ)] ![(21654309312429/50000000000000 : ℝ), (2212779280753/5000000000000 : ℝ), (194309308461/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310928121/10000000000 : ℝ)|^8401 ≤ (21654309312429/50000000000000 : ℝ)^6353
        have hw : |(5310928121/10000000000 : ℝ)|=(5310928121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398513209/10000000000 : ℝ)|^8401 ≤ (2212779280753/5000000000000 : ℝ)^6353
        have hw : |(5398513209/10000000000 : ℝ)|=(5398513209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16149703/78125000 : ℝ)|^8401 ≤ (194309308461/1562500000000 : ℝ)^6353
        have hw : |(-16149703/78125000 : ℝ)|=(16149703/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s4_7 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4355103693/10000000000 : ℝ)*x 0 + (1124097373/2500000000 : ℝ)*x 1 + (4218196817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355103693/10000000000 : ℝ)^8401 ≤ (6662747971127/20000000000000 : ℝ)^6353 := by
    have hnat : (4355103693 : ℕ)^8401*20000000000000^6353 ≤ 6662747971127^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355103693 10000000000 6662747971127 20000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124097373/2500000000 : ℝ)^8401 ≤ (34750301346217/100000000000000 : ℝ)^6353 := by
    have hnat : (1124097373 : ℕ)^8401*100000000000000^6353 ≤ 34750301346217^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124097373 2500000000 34750301346217 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4218196817/10000000000 : ℝ)^8401 ≤ (6387191755751/20000000000000 : ℝ)^6353 := by
    have hnat : (4218196817 : ℕ)^8401*20000000000000^6353 ≤ 6387191755751^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218196817 10000000000 6387191755751 20000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355103693/10000000000 : ℝ), (1124097373/2500000000 : ℝ), (4218196817/10000000000 : ℝ)] ![(6662747971127/20000000000000 : ℝ), (34750301346217/100000000000000 : ℝ), (6387191755751/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355103693/10000000000 : ℝ)|^8401 ≤ (6662747971127/20000000000000 : ℝ)^6353
        have hw : |(4355103693/10000000000 : ℝ)|=(4355103693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124097373/2500000000 : ℝ)|^8401 ≤ (34750301346217/100000000000000 : ℝ)^6353
        have hw : |(1124097373/2500000000 : ℝ)|=(1124097373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4218196817/10000000000 : ℝ)|^8401 ≤ (6387191755751/20000000000000 : ℝ)^6353
        have hw : |(4218196817/10000000000 : ℝ)|=(4218196817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1208_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5411/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2259/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14733/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5411/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14733/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5411/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14733/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5411/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14733/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5411/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14733/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5411/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14733/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5411/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5411/50000 : ℝ) ^ (525/128 : ℝ) ≤ (10943392519743677/100000000000000000000 : ℝ) := by
    have hpowers : (5411/50000 : ℝ)^525 ≤ (10943392519743677/100000000000000000000 : ℝ)^128 := by
      have hnat : (5411 : ℕ)^525*100000000000000000000^128 ≤ 10943392519743677^128*50000^525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5411 50000 10943392519743677 100000000000000000000 525 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5411/50000 : ℝ)) (X := (10943392519743677/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14733/100000 : ℝ) ^ (525/128 : ℝ) ≤ (9696931728175921/25000000000000000000 : ℝ) := by
    have hpowers : (14733/100000 : ℝ)^525 ≤ (9696931728175921/25000000000000000000 : ℝ)^128 := by
      have hnat : (14733 : ℕ)^525*25000000000000000000^128 ≤ 9696931728175921^128*100000^525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14733 100000 9696931728175921 25000000000000000000 525 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14733/100000 : ℝ)) (X := (9696931728175921/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010943392519743677/50000000000000000000 : ℝ) ≤ (1250066697063853/1250000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (50010943392519743677/50000000000000000000 : ℝ)^128 ≤ (1250066697063853/1250000000000000 : ℝ)^525 := by
      have hnat : (50010943392519743677 : ℕ)^128*1250000000000000^525 ≤ 1250066697063853^525*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010943392519743677 50000000000000000000 1250066697063853 1250000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250066697063853/1250000000000000 : ℝ)) (X := (50010943392519743677/50000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049731119432447361/100000000000000000000 : ℝ) ≤ (10001212264134997/10000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (100049731119432447361/100000000000000000000 : ℝ)^128 ≤ (10001212264134997/10000000000000000 : ℝ)^525 := by
      have hnat : (100049731119432447361 : ℕ)^128*10000000000000000^525 ≤ 10001212264134997^525*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049731119432447361 100000000000000000000 10001212264134997 10000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001212264134997/10000000000000000 : ℝ)) (X := (100049731119432447361/100000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509696931728175921/12500000000000000000 : ℝ) ≤ (1000189095175917/1000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (12509696931728175921/12500000000000000000 : ℝ)^128 ≤ (1000189095175917/1000000000000000 : ℝ)^525 := by
      have hnat : (12509696931728175921 : ℕ)^128*1000000000000000^525 ≤ 1000189095175917^525*12500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509696931728175921 12500000000000000000 1000189095175917 1000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000189095175917/1000000000000000 : ℝ)) (X := (12509696931728175921/12500000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10943392519743677/100000000000000000000 : ℝ) ≤ ((9774349325699058063/9777500000000000000 : ℝ)+2*(678687624173/391100000000000 : ℝ)*(5411/50000 : ℝ))^(525/128 : ℝ) := by
    rw [show (9774349325699058063/9777500000000000000 : ℝ)+2*(678687624173/391100000000000 : ℝ)*(5411/50000 : ℝ)=(1250066697063853/1250000000000000 : ℝ) by norm_num, show 1+2*(10943392519743677/100000000000000000000 : ℝ)=(50010943392519743677/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9696931728175921/25000000000000000000 : ℝ)+(10943392519743677/100000000000000000000 : ℝ) ≤ ((9774349325699058063/9777500000000000000 : ℝ)+(678687624173/391100000000000 : ℝ)*((14733/100000 : ℝ)+(5411/50000 : ℝ)))^(525/128 : ℝ) := by
    rw [show (9774349325699058063/9777500000000000000 : ℝ)+(678687624173/391100000000000 : ℝ)*((14733/100000 : ℝ)+(5411/50000 : ℝ))=(10001212264134997/10000000000000000 : ℝ) by norm_num, show 1+(9696931728175921/25000000000000000000 : ℝ)+(10943392519743677/100000000000000000000 : ℝ)=(100049731119432447361/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9696931728175921/25000000000000000000 : ℝ) ≤ ((9774349325699058063/9777500000000000000 : ℝ)+2*(678687624173/391100000000000 : ℝ)*(14733/100000 : ℝ))^(525/128 : ℝ) := by
    rw [show (9774349325699058063/9777500000000000000 : ℝ)+2*(678687624173/391100000000000 : ℝ)*(14733/100000 : ℝ)=(1000189095175917/1000000000000000 : ℝ) by norm_num, show 1+2*(9696931728175921/25000000000000000000 : ℝ)=(12509696931728175921/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9774349325699058063/9777500000000000000 : ℝ)*(X 1 0+X 2 0)+(678687624173/391100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (5411/50000 : ℝ)) (hi := (14733/100000 : ℝ)) (c := (9774349325699058063/9777500000000000000 : ℝ)) (alpha := (678687624173/391100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9774349325699058063/9777500000000000000 : ℝ)*(X 0 1+X 2 1)+(678687624173/391100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (5411/50000 : ℝ)) (hi := (14733/100000 : ℝ)) (c := (9774349325699058063/9777500000000000000 : ℝ)) (alpha := (678687624173/391100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9774349325699058063/9777500000000000000 : ℝ)*(X 0 2+X 1 2)+(678687624173/391100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (5411/50000 : ℝ)) (hi := (14733/100000 : ℝ)) (c := (9774349325699058063/9777500000000000000 : ℝ)) (alpha := (678687624173/391100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1067545423/5000000000 : ℝ)*X 0 0+(5398902151/10000000000 : ℝ)*X 0 1+(5260082103/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673132259/5000000000 : ℝ)*X 1 0+(-1102796417/5000000000 : ℝ)*X 1 1+(2630041071/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346264539/10000000000 : ℝ)*X 2 0+(5260082119/10000000000 : ℝ)*X 2 1+(-551398209/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34024147/78125000 : ℝ)*X 0 0+(210870611/500000000 : ℝ)*X 0 1+(4497170801/10000000000 : ℝ)*X 0 2+(34024147/78125000 : ℝ)*X 1 0+(210870611/500000000 : ℝ)*X 1 1+(4497170801/10000000000 : ℝ)*X 1 2+(34024147/78125000 : ℝ)*X 2 0+(210870611/500000000 : ℝ)*X 2 1+(4497170801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-427019547/2000000000 : ℝ)*X 0 0+(5260470243/10000000000 : ℝ)*X 0 1+(5398512139/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310928433/10000000000 : ℝ)*X 1 0+(-103358121/500000000 : ℝ)*X 1 1+(2699256289/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310928121/10000000000 : ℝ)*X 2 0+(5398513209/10000000000 : ℝ)*X 2 1+(-16149703/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4355103693/10000000000 : ℝ)*X 0 0+(1124097373/2500000000 : ℝ)*X 0 1+(4218196817/10000000000 : ℝ)*X 0 2+(4355103693/10000000000 : ℝ)*X 1 0+(1124097373/2500000000 : ℝ)*X 1 1+(4218196817/10000000000 : ℝ)*X 1 2+(4355103693/10000000000 : ℝ)*X 2 0+(1124097373/2500000000 : ℝ)*X 2 1+(4218196817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (89964507765838537133373/19555000000000000000000000000 : ℝ) := by norm_num
    linear_combination (224201559/25000000000000 : ℝ)*(base19) + (209723341/25000000000000 : ℝ)*(base23) + (9217871/20000000000000 : ℝ)*(lower2) + (13779319/12500000000000 : ℝ)*(upper3) + (11947467/25000000000000 : ℝ)*(upper5) + (5389077980598807/100000000000000 : ℝ)*(major0) + (5389077980598807/100000000000000 : ℝ)*(major1) + (5389077980598807/100000000000000 : ℝ)*(major2) + (7203596443284411/100000000000000 : ℝ)*(sp0) + (1440724063977/20000000000 : ℝ)*(sp1) + (7203620377797873/100000000000000 : ℝ)*(sp2) + (1787260836890761/50000000000000 : ℝ)*(sp3) + (12386703413/50000000000000 : ℝ)*(sp4) + (12917371899/100000000000000 : ℝ)*(sp7) + (178726729557671/5000000000000 : ℝ)*(f.failure) + (1800905304172809/25000000000000 : ℝ)*(f.sum) + (56044336627377/9777500000000000000000000000 : ℝ)*base66 + (6817763606232444159/977750000000000000000000000000000 : ℝ)*base68 + (1659318309623805841/977750000000000000000000000000000 : ℝ)*base69 + (3847900996479555841/977750000000000000000000000000000 : ℝ)*base71 + (32749149597471/19555000000000000000000000000 : ℝ)*base73 + (4976615942603055841/977750000000000000000000000000000 : ℝ)*base75 + (11785437174599694159/977750000000000000000000000000000 : ℝ)*base78 + (1347043223329444159/977750000000000000000000000000000 : ℝ)*base80 + (507594408207/611093750000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1663043/500000000000000000000 : ℝ)*base90 + (1663043/500000000000000000000 : ℝ)*base92 + (1663043/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (863803313356867577348294643/122218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1411182151/100000000000000 : ℝ)*(base19) + (381712993/20000000000000 : ℝ)*(base23) + (297949771/100000000000000 : ℝ)*(upper2) + (104456681/20000000000000 : ℝ)*(upper3) + (1354848454561871/25000000000000 : ℝ)*(major0) + (1354848454561871/25000000000000 : ℝ)*(major1) + (1354848454561871/25000000000000 : ℝ)*(major2) + (16076241849/50000000000000 : ℝ)*(sp1) + (17310086253/20000000000000 : ℝ)*(sp2) + (2568061791/100000000000000 : ℝ)*(sp3) + (226379517010773/3125000000000 : ℝ)*(sp4) + (7244110980678887/100000000000000 : ℝ)*(sp5) + (1448811217069701/20000000000000 : ℝ)*(sp6) + (449330036062377/12500000000000 : ℝ)*(sp7) + (449330357070101/12500000000000 : ℝ)*(f.failure) + (226379517010773/3125000000000 : ℝ)*(f.sum) + (7011640327347/4888750000000000000000000000 : ℝ)*base66 + (1637024072113240873/244437500000000000000000000000000 : ℝ)*base67 + (1341149533500928373/244437500000000000000000000000000 : ℝ)*base69 + (859497120930178373/244437500000000000000000000000000 : ℝ)*base71 + (5398751073977/1222187500000000000000000000 : ℝ)*base73 + (4727168304208553373/244437500000000000000000000000000 : ℝ)*base75 + (2395958084564240873/244437500000000000000000000000000 : ℝ)*base77 + (2440181597778740873/244437500000000000000000000000000 : ℝ)*base79 + (71569725386067/19555000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (10759767/1250000000000000000000 : ℝ)*base89 + (10759767/1250000000000000000000 : ℝ)*base91 + (10759767/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1208_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5411/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1208_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1208_s5_0 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2135595579/10000000000 : ℝ)*x 0 + (26966179/50000000 : ℝ)*x 1 + (2632708479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2135595579/10000000000 : ℝ)^8401 ≤ (12983082308163/100000000000000 : ℝ)^6353 := by
    have hnat : (2135595579 : ℕ)^8401*100000000000000^6353 ≤ 12983082308163^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135595579 10000000000 12983082308163 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26966179/50000000 : ℝ)^8401 ≤ (1104959632717/2500000000000 : ℝ)^6353 := by
    have hnat : (26966179 : ℕ)^8401*2500000000000^6353 ≤ 1104959632717^6353*50000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26966179 50000000 1104959632717 2500000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632708479/5000000000 : ℝ)^8401 ≤ (42818532366583/100000000000000 : ℝ)^6353 := by
    have hnat : (2632708479 : ℕ)^8401*100000000000000^6353 ≤ 42818532366583^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632708479 5000000000 42818532366583 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2135595579/10000000000 : ℝ), (26966179/50000000 : ℝ), (2632708479/5000000000 : ℝ)] ![(12983082308163/100000000000000 : ℝ), (1104959632717/2500000000000 : ℝ), (42818532366583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2135595579/10000000000 : ℝ)|^8401 ≤ (12983082308163/100000000000000 : ℝ)^6353
        have hw : |(-2135595579/10000000000 : ℝ)|=(2135595579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26966179/50000000 : ℝ)|^8401 ≤ (1104959632717/2500000000000 : ℝ)^6353
        have hw : |(26966179/50000000 : ℝ)|=(26966179/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632708479/5000000000 : ℝ)|^8401 ≤ (42818532366583/100000000000000 : ℝ)^6353
        have hw : |(2632708479/5000000000 : ℝ)|=(2632708479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s5_1 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344835437/10000000000 : ℝ)*x 0 + (-2200430811/10000000000 : ℝ)*x 1 + (5265416971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344835437/10000000000 : ℝ)^8401 ≤ (43674630771017/100000000000000 : ℝ)^6353 := by
    have hnat : (5344835437 : ℕ)^8401*100000000000000^6353 ≤ 43674630771017^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344835437 10000000000 43674630771017 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2200430811/10000000000 : ℝ)^8401 ≤ (3376709175867/25000000000000 : ℝ)^6353 := by
    have hnat : (2200430811 : ℕ)^8401*25000000000000^6353 ≤ 3376709175867^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200430811 10000000000 3376709175867 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265416971/10000000000 : ℝ)^8401 ≤ (42818532506379/100000000000000 : ℝ)^6353 := by
    have hnat : (5265416971 : ℕ)^8401*100000000000000^6353 ≤ 42818532506379^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265416971 10000000000 42818532506379 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344835437/10000000000 : ℝ), (-2200430811/10000000000 : ℝ), (5265416971/10000000000 : ℝ)] ![(43674630771017/100000000000000 : ℝ), (3376709175867/25000000000000 : ℝ), (42818532506379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344835437/10000000000 : ℝ)|^8401 ≤ (43674630771017/100000000000000 : ℝ)^6353
        have hw : |(5344835437/10000000000 : ℝ)|=(5344835437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2200430811/10000000000 : ℝ)|^8401 ≤ (3376709175867/25000000000000 : ℝ)^6353
        have hw : |(-2200430811/10000000000 : ℝ)|=(2200430811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265416971/10000000000 : ℝ)|^8401 ≤ (42818532506379/100000000000000 : ℝ)^6353
        have hw : |(5265416971/10000000000 : ℝ)|=(5265416971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s5_2 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344835387/10000000000 : ℝ)*x 0 + (5265417069/10000000000 : ℝ)*x 1 + (-550107687/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344835387/10000000000 : ℝ)^8401 ≤ (43674630230739/100000000000000 : ℝ)^6353 := by
    have hnat : (5344835387 : ℕ)^8401*100000000000000^6353 ≤ 43674630230739^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344835387 10000000000 43674630230739 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265417069/10000000000 : ℝ)^8401 ≤ (1712741342409/4000000000000 : ℝ)^6353 := by
    have hnat : (5265417069 : ℕ)^8401*4000000000000^6353 ≤ 1712741342409^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265417069 10000000000 1712741342409 4000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550107687/2500000000 : ℝ)^8401 ≤ (6753418096047/50000000000000 : ℝ)^6353 := by
    have hnat : (550107687 : ℕ)^8401*50000000000000^6353 ≤ 6753418096047^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550107687 2500000000 6753418096047 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344835387/10000000000 : ℝ), (5265417069/10000000000 : ℝ), (-550107687/2500000000 : ℝ)] ![(43674630230739/100000000000000 : ℝ), (1712741342409/4000000000000 : ℝ), (6753418096047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344835387/10000000000 : ℝ)|^8401 ≤ (43674630230739/100000000000000 : ℝ)^6353
        have hw : |(5344835387/10000000000 : ℝ)|=(5344835387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265417069/10000000000 : ℝ)|^8401 ≤ (1712741342409/4000000000000 : ℝ)^6353
        have hw : |(5265417069/10000000000 : ℝ)|=(5265417069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-550107687/2500000000 : ℝ)|^8401 ≤ (6753418096047/50000000000000 : ℝ)^6353
        have hw : |(-550107687/2500000000 : ℝ)|=(550107687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s5_3 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4355387401/10000000000 : ℝ)*x 0 + (2114229757/5000000000 : ℝ)*x 1 + (1121511837/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355387401/10000000000 : ℝ)^8401 ≤ (33316609665749/100000000000000 : ℝ)^6353 := by
    have hnat : (4355387401 : ℕ)^8401*100000000000000^6353 ≤ 33316609665749^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355387401 10000000000 33316609665749 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114229757/5000000000 : ℝ)^8401 ≤ (6407749096489/20000000000000 : ℝ)^6353 := by
    have hnat : (2114229757 : ℕ)^8401*20000000000000^6353 ≤ 6407749096489^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114229757 5000000000 6407749096489 20000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121511837/2500000000 : ℝ)^8401 ≤ (1732232242101/5000000000000 : ℝ)^6353 := by
    have hnat : (1121511837 : ℕ)^8401*5000000000000^6353 ≤ 1732232242101^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121511837 2500000000 1732232242101 5000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355387401/10000000000 : ℝ), (2114229757/5000000000 : ℝ), (1121511837/2500000000 : ℝ)] ![(33316609665749/100000000000000 : ℝ), (6407749096489/20000000000000 : ℝ), (1732232242101/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355387401/10000000000 : ℝ)|^8401 ≤ (33316609665749/100000000000000 : ℝ)^6353
        have hw : |(4355387401/10000000000 : ℝ)|=(4355387401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2114229757/5000000000 : ℝ)|^8401 ≤ (6407749096489/20000000000000 : ℝ)^6353
        have hw : |(2114229757/5000000000 : ℝ)|=(2114229757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121511837/2500000000 : ℝ)|^8401 ≤ (1732232242101/5000000000000 : ℝ)^6353
        have hw : |(1121511837/2500000000 : ℝ)|=(1121511837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s5_4 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-53390003/250000000 : ℝ)*x 0 + (5265746483/10000000000 : ℝ)*x 1 + (2696452719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53390003/250000000 : ℝ)^8401 ≤ (12983118814023/100000000000000 : ℝ)^6353 := by
    have hnat : (53390003 : ℕ)^8401*100000000000000^6353 ≤ 12983118814023^6353*250000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53390003 250000000 12983118814023 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265746483/10000000000 : ℝ)^8401 ≤ (42822075960019/100000000000000 : ℝ)^6353 := by
    have hnat : (5265746483 : ℕ)^8401*100000000000000^6353 ≤ 42822075960019^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265746483 10000000000 42822075960019 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696452719/5000000000 : ℝ)^8401 ≤ (22097402605307/50000000000000 : ℝ)^6353 := by
    have hnat : (2696452719 : ℕ)^8401*50000000000000^6353 ≤ 22097402605307^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696452719 5000000000 22097402605307 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53390003/250000000 : ℝ), (5265746483/10000000000 : ℝ), (2696452719/5000000000 : ℝ)] ![(12983118814023/100000000000000 : ℝ), (42822075960019/100000000000000 : ℝ), (22097402605307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53390003/250000000 : ℝ)|^8401 ≤ (12983118814023/100000000000000 : ℝ)^6353
        have hw : |(-53390003/250000000 : ℝ)|=(53390003/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265746483/10000000000 : ℝ)|^8401 ≤ (42822075960019/100000000000000 : ℝ)^6353
        have hw : |(5265746483/10000000000 : ℝ)|=(5265746483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696452719/5000000000 : ℝ)|^8401 ≤ (22097402605307/50000000000000 : ℝ)^6353
        have hw : |(2696452719/5000000000 : ℝ)|=(2696452719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s5_5 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312298539/10000000000 : ℝ)*x 0 + (-207294209/1000000000 : ℝ)*x 1 + (2696452691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312298539/10000000000 : ℝ)^8401 ≤ (43323397015873/100000000000000 : ℝ)^6353 := by
    have hnat : (5312298539 : ℕ)^8401*100000000000000^6353 ≤ 43323397015873^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312298539 10000000000 43323397015873 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207294209/1000000000 : ℝ)^8401 ≤ (12481798361789/100000000000000 : ℝ)^6353 := by
    have hnat : (207294209 : ℕ)^8401*100000000000000^6353 ≤ 12481798361789^6353*1000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207294209 1000000000 12481798361789 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696452691/5000000000 : ℝ)^8401 ≤ (22097402301877/50000000000000 : ℝ)^6353 := by
    have hnat : (2696452691 : ℕ)^8401*50000000000000^6353 ≤ 22097402301877^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696452691 5000000000 22097402301877 50000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312298539/10000000000 : ℝ), (-207294209/1000000000 : ℝ), (2696452691/5000000000 : ℝ)] ![(43323397015873/100000000000000 : ℝ), (12481798361789/100000000000000 : ℝ), (22097402301877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312298539/10000000000 : ℝ)|^8401 ≤ (43323397015873/100000000000000 : ℝ)^6353
        have hw : |(5312298539/10000000000 : ℝ)|=(5312298539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-207294209/1000000000 : ℝ)|^8401 ≤ (12481798361789/100000000000000 : ℝ)^6353
        have hw : |(-207294209/1000000000 : ℝ)|=(207294209/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696452691/5000000000 : ℝ)|^8401 ≤ (22097402301877/50000000000000 : ℝ)^6353
        have hw : |(2696452691/5000000000 : ℝ)|=(2696452691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s5_6 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (166009319/312500000 : ℝ)*x 0 + (269645291/500000000 : ℝ)*x 1 + (-2072941943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166009319/312500000 : ℝ)^8401 ≤ (10830848361567/25000000000000 : ℝ)^6353 := by
    have hnat : (166009319 : ℕ)^8401*25000000000000^6353 ≤ 10830848361567^6353*312500000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166009319 312500000 10830848361567 25000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269645291/500000000 : ℝ)^8401 ≤ (44194809350267/100000000000000 : ℝ)^6353 := by
    have hnat : (269645291 : ℕ)^8401*100000000000000^6353 ≤ 44194809350267^6353*500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269645291 500000000 44194809350267 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072941943/10000000000 : ℝ)^8401 ≤ (12481797191321/100000000000000 : ℝ)^6353 := by
    have hnat : (2072941943 : ℕ)^8401*100000000000000^6353 ≤ 12481797191321^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072941943 10000000000 12481797191321 100000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166009319/312500000 : ℝ), (269645291/500000000 : ℝ), (-2072941943/10000000000 : ℝ)] ![(10830848361567/25000000000000 : ℝ), (44194809350267/100000000000000 : ℝ), (12481797191321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166009319/312500000 : ℝ)|^8401 ≤ (10830848361567/25000000000000 : ℝ)^6353
        have hw : |(166009319/312500000 : ℝ)|=(166009319/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269645291/500000000 : ℝ)|^8401 ≤ (44194809350267/100000000000000 : ℝ)^6353
        have hw : |(269645291/500000000 : ℝ)|=(269645291/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2072941943/10000000000 : ℝ)|^8401 ≤ (12481797191321/100000000000000 : ℝ)^6353
        have hw : |(-2072941943/10000000000 : ℝ)|=(2072941943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1208_s5_7 (p : ℝ) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177698927/5000000000 : ℝ)*x 0 + (1121346083/2500000000 : ℝ)*x 1 + (4229124703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177698927/5000000000 : ℝ)^8401 ≤ (520573678169/1562500000000 : ℝ)^6353 := by
    have hnat : (2177698927 : ℕ)^8401*1562500000000^6353 ≤ 520573678169^6353*5000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177698927 5000000000 520573678169 1562500000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121346083/2500000000 : ℝ)^8401 ≤ (6927574814431/20000000000000 : ℝ)^6353 := by
    have hnat : (1121346083 : ℕ)^8401*20000000000000^6353 ≤ 6927574814431^6353*2500000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121346083 2500000000 6927574814431 20000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229124703/10000000000 : ℝ)^8401 ≤ (6409082100699/20000000000000 : ℝ)^6353 := by
    have hnat : (4229124703 : ℕ)^8401*20000000000000^6353 ≤ 6409082100699^6353*10000000000^8401 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229124703 10000000000 6409082100699 20000000000000 8401 6353 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8401/2048 : ℝ)) 8401 6353 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177698927/5000000000 : ℝ), (1121346083/2500000000 : ℝ), (4229124703/10000000000 : ℝ)] ![(520573678169/1562500000000 : ℝ), (6927574814431/20000000000000 : ℝ), (6409082100699/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177698927/5000000000 : ℝ)|^8401 ≤ (520573678169/1562500000000 : ℝ)^6353
        have hw : |(2177698927/5000000000 : ℝ)|=(2177698927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121346083/2500000000 : ℝ)|^8401 ≤ (6927574814431/20000000000000 : ℝ)^6353
        have hw : |(1121346083/2500000000 : ℝ)|=(1121346083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229124703/10000000000 : ℝ)|^8401 ≤ (6409082100699/20000000000000 : ℝ)^6353
        have hw : |(4229124703/10000000000 : ℝ)|=(4229124703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1208_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (713/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3529/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2259/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2259/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2259/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2259/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2259/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2259/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2259/20000 : ℝ) ^ (525/128 : ℝ) ≤ (13042285393886113/100000000000000000000 : ℝ) := by
    have hpowers : (2259/20000 : ℝ)^525 ≤ (13042285393886113/100000000000000000000 : ℝ)^128 := by
      have hnat : (2259 : ℕ)^525*100000000000000000000^128 ≤ 13042285393886113^128*20000^525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2259 20000 13042285393886113 100000000000000000000 525 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2259/20000 : ℝ)) (X := (13042285393886113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (525/128 : ℝ) ≤ (33685481080730281/100000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^525 ≤ (33685481080730281/100000000000000000000 : ℝ)^128 := by
      have hnat : (2847 : ℕ)^525*100000000000000000000^128 ≤ 33685481080730281^128*20000^525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 33685481080730281 100000000000000000000 525 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (33685481080730281/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013042285393886113/50000000000000000000 : ℝ) ≤ (5000317951982961/5000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (50013042285393886113/50000000000000000000 : ℝ)^128 ≤ (5000317951982961/5000000000000000 : ℝ)^525 := by
      have hnat : (50013042285393886113 : ℕ)^128*5000000000000000^525 ≤ 5000317951982961^525*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013042285393886113 50000000000000000000 5000317951982961 5000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000317951982961/5000000000000000 : ℝ)) (X := (50013042285393886113/50000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023363883237308197/50000000000000000000 : ℝ) ≤ (10001139066223727/10000000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (50023363883237308197/50000000000000000000 : ℝ)^128 ≤ (10001139066223727/10000000000000000 : ℝ)^525 := by
      have hnat : (50023363883237308197 : ℕ)^128*10000000000000000^525 ≤ 10001139066223727^525*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023363883237308197 50000000000000000000 10001139066223727 10000000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001139066223727/10000000000000000 : ℝ)) (X := (50023363883237308197/50000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033685481080730281/50000000000000000000 : ℝ) ≤ (2500410557120383/2500000000000000 : ℝ) ^ (525/128 : ℝ) := by
    have hpowers : (50033685481080730281/50000000000000000000 : ℝ)^128 ≤ (2500410557120383/2500000000000000 : ℝ)^525 := by
      have hnat : (50033685481080730281 : ℕ)^128*2500000000000000^525 ≤ 2500410557120383^525*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033685481080730281 50000000000000000000 2500410557120383 2500000000000000 128 525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500410557120383/2500000000000000 : ℝ)) (X := (50033685481080730281/50000000000000000000 : ℝ)) (by norm_num) 525 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13042285393886113/100000000000000000000 : ℝ) ≤ ((979683437408533191/980000000000000000 : ℝ)+2*(100632451561/58800000000000 : ℝ)*(2259/20000 : ℝ))^(525/128 : ℝ) := by
    rw [show (979683437408533191/980000000000000000 : ℝ)+2*(100632451561/58800000000000 : ℝ)*(2259/20000 : ℝ)=(5000317951982961/5000000000000000 : ℝ) by norm_num, show 1+2*(13042285393886113/100000000000000000000 : ℝ)=(50013042285393886113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33685481080730281/100000000000000000000 : ℝ)+(13042285393886113/100000000000000000000 : ℝ) ≤ ((979683437408533191/980000000000000000 : ℝ)+(100632451561/58800000000000 : ℝ)*((2847/20000 : ℝ)+(2259/20000 : ℝ)))^(525/128 : ℝ) := by
    rw [show (979683437408533191/980000000000000000 : ℝ)+(100632451561/58800000000000 : ℝ)*((2847/20000 : ℝ)+(2259/20000 : ℝ))=(10001139066223727/10000000000000000 : ℝ) by norm_num, show 1+(33685481080730281/100000000000000000000 : ℝ)+(13042285393886113/100000000000000000000 : ℝ)=(50023363883237308197/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33685481080730281/100000000000000000000 : ℝ) ≤ ((979683437408533191/980000000000000000 : ℝ)+2*(100632451561/58800000000000 : ℝ)*(2847/20000 : ℝ))^(525/128 : ℝ) := by
    rw [show (979683437408533191/980000000000000000 : ℝ)+2*(100632451561/58800000000000 : ℝ)*(2847/20000 : ℝ)=(2500410557120383/2500000000000000 : ℝ) by norm_num, show 1+2*(33685481080730281/100000000000000000000 : ℝ)=(50033685481080730281/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (979683437408533191/980000000000000000 : ℝ)*(X 1 0+X 2 0)+(100632451561/58800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (2259/20000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (979683437408533191/980000000000000000 : ℝ)) (alpha := (100632451561/58800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (979683437408533191/980000000000000000 : ℝ)*(X 0 1+X 2 1)+(100632451561/58800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (2259/20000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (979683437408533191/980000000000000000 : ℝ)) (alpha := (100632451561/58800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (979683437408533191/980000000000000000 : ℝ)*(X 0 2+X 1 2)+(100632451561/58800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (525/128 : ℝ)) (lo := (2259/20000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (979683437408533191/980000000000000000 : ℝ)) (alpha := (100632451561/58800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2135595579/10000000000 : ℝ)*X 0 0+(26966179/50000000 : ℝ)*X 0 1+(2632708479/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344835437/10000000000 : ℝ)*X 1 0+(-2200430811/10000000000 : ℝ)*X 1 1+(5265416971/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344835387/10000000000 : ℝ)*X 2 0+(5265417069/10000000000 : ℝ)*X 2 1+(-550107687/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355387401/10000000000 : ℝ)*X 0 0+(2114229757/5000000000 : ℝ)*X 0 1+(1121511837/2500000000 : ℝ)*X 0 2+(4355387401/10000000000 : ℝ)*X 1 0+(2114229757/5000000000 : ℝ)*X 1 1+(1121511837/2500000000 : ℝ)*X 1 2+(4355387401/10000000000 : ℝ)*X 2 0+(2114229757/5000000000 : ℝ)*X 2 1+(1121511837/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-53390003/250000000 : ℝ)*X 0 0+(5265746483/10000000000 : ℝ)*X 0 1+(2696452719/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312298539/10000000000 : ℝ)*X 1 0+(-207294209/1000000000 : ℝ)*X 1 1+(2696452691/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((166009319/312500000 : ℝ)*X 2 0+(269645291/500000000 : ℝ)*X 2 1+(-2072941943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177698927/5000000000 : ℝ)*X 0 0+(1121346083/2500000000 : ℝ)*X 0 1+(4229124703/10000000000 : ℝ)*X 0 2+(2177698927/5000000000 : ℝ)*X 1 0+(1121346083/2500000000 : ℝ)*X 1 1+(4229124703/10000000000 : ℝ)*X 1 2+(2177698927/5000000000 : ℝ)*X 2 0+(1121346083/2500000000 : ℝ)*X 2 1+(4229124703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1208_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9309836623950635763113791/875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2271862789/100000000000000 : ℝ)*(base19) + (2117157823/100000000000000 : ℝ)*(base23) + (43568723/100000000000000 : ℝ)*(lower2) + (200301237/100000000000000 : ℝ)*(upper3) + (56953017/25000000000000 : ℝ)*(upper5) + (1463242566812069/25000000000000 : ℝ)*(major0) + (1463242566812069/25000000000000 : ℝ)*(major1) + (1463242566812069/25000000000000 : ℝ)*(major2) + (7823639892484631/100000000000000 : ℝ)*(sp0) + (3911853539012951/50000000000000 : ℝ)*(sp1) + (1955926808182717/25000000000000 : ℝ)*(sp2) + (97055025977963/2500000000000 : ℝ)*(sp3) + (3472870203/5000000000000 : ℝ)*(sp4) + (14895414447/50000000000000 : ℝ)*(sp7) + (1941115414973707/50000000000000 : ℝ)*(f.failure) + (7823709349888691/100000000000000 : ℝ)*(f.sum) + (307949562791/183750000000000000000000000 : ℝ)*base65 + (44928027574903463/73500000000000000000000000000000 : ℝ)*base68 + (452507970946903463/73500000000000000000000000000000 : ℝ)*base70 + (529664224771903463/73500000000000000000000000000000 : ℝ)*base72 + (1641784838699/735000000000000000000000000 : ℝ)*base73 + (414106122349096537/73500000000000000000000000000000 : ℝ)*base75 + (9294275308903463/73500000000000000000000000000000 : ℝ)*base78 + (613558948306903463/73500000000000000000000000000000 : ℝ)*base80 + (1113979418879/735000000000000000000000000 : ℝ)*base81 + (8320631/5000000000000000000000 : ℝ)*base90 + (8320631/5000000000000000000000 : ℝ)*base92 + (8320631/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41288472000770020288804233/7000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (761411341/100000000000000 : ℝ)*(base19) + (11453159/781250000000 : ℝ)*(base23) + (258802609/50000000000000 : ℝ)*(lower4) + (50277109/100000000000000 : ℝ)*(lower5) + (5883225808680351/100000000000000 : ℝ)*(major0) + (5883225808680351/100000000000000 : ℝ)*(major1) + (5883225808680351/100000000000000 : ℝ)*(major2) + (6015255699/25000000000000 : ℝ)*(sp1) + (15004844187/25000000000000 : ℝ)*(sp2) + (6198068937/100000000000000 : ℝ)*(sp3) + (3932076159708861/50000000000000 : ℝ)*(sp4) + (1572825499396717/20000000000000 : ℝ)*(sp5) + (3932045417018311/50000000000000 : ℝ)*(sp6) + (195114645163113/5000000000000 : ℝ)*(sp7) + (1951149550665599/50000000000000 : ℝ)*(f.failure) + (3932076159708861/50000000000000 : ℝ)*(f.sum) + (815163621623/980000000000000000000000000 : ℝ)*base66 + (829060856852880041/98000000000000000000000000000000 : ℝ)*base67 + (1327713136908880041/98000000000000000000000000000000 : ℝ)*base69 + (675714545412880041/98000000000000000000000000000000 : ℝ)*base71 + (7230694595277/980000000000000000000000000 : ℝ)*base73 + (1521649928208880041/98000000000000000000000000000000 : ℝ)*base75 + (2162937978282880041/98000000000000000000000000000000 : ℝ)*base77 + (798829824104880041/98000000000000000000000000000000 : ℝ)*base79 + (3419246737243/980000000000000000000000000 : ℝ)*base82 + (46632133/5000000000000000000000 : ℝ)*base89 + (46632133/5000000000000000000000 : ℝ)*base91 + (46632133/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1208_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2259/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (713/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1208_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1208_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8157/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4679/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (713/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1208_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1208_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1208_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (525/128 : ℝ) ≤ p) (hpb : p ≤ (8401/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150763067/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8157/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4679/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (713/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3529/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1208_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1234_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:16:25.626972+00:00
-- url     : https://prove2.me/submissions/1012c283-6448-41a5-8612-f773be497b4e

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
theorem support_rectangle_w1234_s3_0 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-212073893/1000000000 : ℝ)*x 0 + (1084072353/2000000000 : ℝ)*x 1 + (5240000919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212073893/1000000000 : ℝ)^8427 ≤ (6445010115337/50000000000000 : ℝ)^6379 := by
    have hnat : (212073893 : ℕ)^8427*50000000000000^6379 ≤ 6445010115337^6379*1000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212073893 1000000000 6445010115337 50000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084072353/2000000000 : ℝ)^8427 ≤ (5566050519717/12500000000000 : ℝ)^6379 := by
    have hnat : (1084072353 : ℕ)^8427*12500000000000^6379 ≤ 5566050519717^6379*2000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084072353 2000000000 5566050519717 12500000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240000919/10000000000 : ℝ)^8427 ≤ (42581575598761/100000000000000 : ℝ)^6379 := by
    have hnat : (5240000919 : ℕ)^8427*100000000000000^6379 ≤ 42581575598761^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240000919 10000000000 42581575598761 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-212073893/1000000000 : ℝ), (1084072353/2000000000 : ℝ), (5240000919/10000000000 : ℝ)] ![(6445010115337/50000000000000 : ℝ), (5566050519717/12500000000000 : ℝ), (42581575598761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-212073893/1000000000 : ℝ)|^8427 ≤ (6445010115337/50000000000000 : ℝ)^6379
        have hw : |(-212073893/1000000000 : ℝ)|=(212073893/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084072353/2000000000 : ℝ)|^8427 ≤ (5566050519717/12500000000000 : ℝ)^6379
        have hw : |(1084072353/2000000000 : ℝ)|=(1084072353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240000919/10000000000 : ℝ)|^8427 ≤ (42581575598761/100000000000000 : ℝ)^6379
        have hw : |(5240000919/10000000000 : ℝ)|=(5240000919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s3_1 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (53516667/100000000 : ℝ)*x 0 + (-2212761513/10000000000 : ℝ)*x 1 + (327500067/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53516667/100000000 : ℝ)^8427 ≤ (10946103243241/25000000000000 : ℝ)^6379 := by
    have hnat : (53516667 : ℕ)^8427*25000000000000^6379 ≤ 10946103243241^6379*100000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53516667 100000000 10946103243241 25000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2212761513/10000000000 : ℝ)^8427 ≤ (213031402701/1562500000000 : ℝ)^6379 := by
    have hnat : (2212761513 : ℕ)^8427*1562500000000^6379 ≤ 213031402701^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212761513 10000000000 213031402701 1562500000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327500067/625000000 : ℝ)^8427 ≤ (42581577241249/100000000000000 : ℝ)^6379 := by
    have hnat : (327500067 : ℕ)^8427*100000000000000^6379 ≤ 42581577241249^6379*625000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327500067 625000000 42581577241249 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53516667/100000000 : ℝ), (-2212761513/10000000000 : ℝ), (327500067/625000000 : ℝ)] ![(10946103243241/25000000000000 : ℝ), (213031402701/1562500000000 : ℝ), (42581577241249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53516667/100000000 : ℝ)|^8427 ≤ (10946103243241/25000000000000 : ℝ)^6379
        have hw : |(53516667/100000000 : ℝ)|=(53516667/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2212761513/10000000000 : ℝ)|^8427 ≤ (213031402701/1562500000000 : ℝ)^6379
        have hw : |(-2212761513/10000000000 : ℝ)|=(2212761513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327500067/625000000 : ℝ)|^8427 ≤ (42581577241249/100000000000000 : ℝ)^6379
        have hw : |(327500067/625000000 : ℝ)|=(327500067/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s3_2 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5351666597/10000000000 : ℝ)*x 0 + (2620000743/5000000000 : ℝ)*x 1 + (-138297569/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351666597/10000000000 : ℝ)^8427 ≤ (1751376474389/4000000000000 : ℝ)^6379 := by
    have hnat : (5351666597 : ℕ)^8427*4000000000000^6379 ≤ 1751376474389^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351666597 10000000000 1751376474389 4000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620000743/5000000000 : ℝ)^8427 ≤ (10645395421407/25000000000000 : ℝ)^6379 := by
    have hnat : (2620000743 : ℕ)^8427*25000000000000^6379 ≤ 10645395421407^6379*5000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620000743 5000000000 10645395421407 25000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138297569/625000000 : ℝ)^8427 ≤ (13634006443719/100000000000000 : ℝ)^6379 := by
    have hnat : (138297569 : ℕ)^8427*100000000000000^6379 ≤ 13634006443719^6379*625000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138297569 625000000 13634006443719 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351666597/10000000000 : ℝ), (2620000743/5000000000 : ℝ), (-138297569/625000000 : ℝ)] ![(1751376474389/4000000000000 : ℝ), (10645395421407/25000000000000 : ℝ), (13634006443719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351666597/10000000000 : ℝ)|^8427 ≤ (1751376474389/4000000000000 : ℝ)^6379
        have hw : |(5351666597/10000000000 : ℝ)|=(5351666597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620000743/5000000000 : ℝ)|^8427 ≤ (10645395421407/25000000000000 : ℝ)^6379
        have hw : |(2620000743/5000000000 : ℝ)|=(2620000743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-138297569/625000000 : ℝ)|^8427 ≤ (13634006443719/100000000000000 : ℝ)^6379
        have hw : |(-138297569/625000000 : ℝ)|=(138297569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s3_3 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174005357/400000000 : ℝ)*x 0 + (2085605511/5000000000 : ℝ)*x 1 + (567064921/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174005357/400000000 : ℝ)^8427 ≤ (16649939158317/50000000000000 : ℝ)^6379 := by
    have hnat : (174005357 : ℕ)^8427*50000000000000^6379 ≤ 16649939158317^6379*400000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174005357 400000000 16649939158317 50000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085605511/5000000000 : ℝ)^8427 ≤ (1575128610409/5000000000000 : ℝ)^6379 := by
    have hnat : (2085605511 : ℕ)^8427*5000000000000^6379 ≤ 1575128610409^6379*5000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085605511 5000000000 1575128610409 5000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567064921/1250000000 : ℝ)^8427 ≤ (4399693682599/12500000000000 : ℝ)^6379 := by
    have hnat : (567064921 : ℕ)^8427*12500000000000^6379 ≤ 4399693682599^6379*1250000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567064921 1250000000 4399693682599 12500000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174005357/400000000 : ℝ), (2085605511/5000000000 : ℝ), (567064921/1250000000 : ℝ)] ![(16649939158317/50000000000000 : ℝ), (1575128610409/5000000000000 : ℝ), (4399693682599/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174005357/400000000 : ℝ)|^8427 ≤ (16649939158317/50000000000000 : ℝ)^6379
        have hw : |(174005357/400000000 : ℝ)|=(174005357/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085605511/5000000000 : ℝ)|^8427 ≤ (1575128610409/5000000000000 : ℝ)^6379
        have hw : |(2085605511/5000000000 : ℝ)|=(2085605511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(567064921/1250000000 : ℝ)|^8427 ≤ (4399693682599/12500000000000 : ℝ)^6379
        have hw : |(567064921/1250000000 : ℝ)|=(567064921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s3_4 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2120753657/10000000000 : ℝ)*x 0 + (81885309/156250000 : ℝ)*x 1 + (1083939821/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2120753657/10000000000 : ℝ)^8427 ≤ (805633655049/6250000000000 : ℝ)^6379 := by
    have hnat : (2120753657 : ℕ)^8427*6250000000000^6379 ≤ 805633655049^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120753657 10000000000 805633655049 6250000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81885309/156250000 : ℝ)^8427 ≤ (21294324356607/50000000000000 : ℝ)^6379 := by
    have hnat : (81885309 : ℕ)^8427*50000000000000^6379 ≤ 21294324356607^6379*156250000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81885309 156250000 21294324356607 50000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083939821/2000000000 : ℝ)^8427 ≤ (44521212790249/100000000000000 : ℝ)^6379 := by
    have hnat : (1083939821 : ℕ)^8427*100000000000000^6379 ≤ 44521212790249^6379*2000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083939821 2000000000 44521212790249 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2120753657/10000000000 : ℝ), (81885309/156250000 : ℝ), (1083939821/2000000000 : ℝ)] ![(805633655049/6250000000000 : ℝ), (21294324356607/50000000000000 : ℝ), (44521212790249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2120753657/10000000000 : ℝ)|^8427 ≤ (805633655049/6250000000000 : ℝ)^6379
        have hw : |(-2120753657/10000000000 : ℝ)|=(2120753657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81885309/156250000 : ℝ)|^8427 ≤ (21294324356607/50000000000000 : ℝ)^6379
        have hw : |(81885309/156250000 : ℝ)|=(81885309/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083939821/2000000000 : ℝ)|^8427 ≤ (44521212790249/100000000000000 : ℝ)^6379
        have hw : |(1083939821/2000000000 : ℝ)|=(1083939821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s3_5 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5305677611/10000000000 : ℝ)*x 0 + (-2033062821/10000000000 : ℝ)*x 1 + (1083939809/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305677611/10000000000 : ℝ)^8427 ≤ (8657608716967/20000000000000 : ℝ)^6379 := by
    have hnat : (5305677611 : ℕ)^8427*20000000000000^6379 ≤ 8657608716967^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305677611 10000000000 8657608716967 20000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2033062821/10000000000 : ℝ)^8427 ≤ (6095372131551/50000000000000 : ℝ)^6379 := by
    have hnat : (2033062821 : ℕ)^8427*50000000000000^6379 ≤ 6095372131551^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033062821 10000000000 6095372131551 50000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083939809/2000000000 : ℝ)^8427 ≤ (356169697113/800000000000 : ℝ)^6379 := by
    have hnat : (1083939809 : ℕ)^8427*800000000000^6379 ≤ 356169697113^6379*2000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083939809 2000000000 356169697113 800000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305677611/10000000000 : ℝ), (-2033062821/10000000000 : ℝ), (1083939809/2000000000 : ℝ)] ![(8657608716967/20000000000000 : ℝ), (6095372131551/50000000000000 : ℝ), (356169697113/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305677611/10000000000 : ℝ)|^8427 ≤ (8657608716967/20000000000000 : ℝ)^6379
        have hw : |(5305677611/10000000000 : ℝ)|=(5305677611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2033062821/10000000000 : ℝ)|^8427 ≤ (6095372131551/50000000000000 : ℝ)^6379
        have hw : |(-2033062821/10000000000 : ℝ)|=(2033062821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083939809/2000000000 : ℝ)|^8427 ≤ (356169697113/800000000000 : ℝ)^6379
        have hw : |(1083939809/2000000000 : ℝ)|=(1083939809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s3_6 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1061135383/2000000000 : ℝ)*x 0 + (1354924863/2500000000 : ℝ)*x 1 + (-203306321/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061135383/2000000000 : ℝ)^8427 ≤ (43288036083187/100000000000000 : ℝ)^6379 := by
    have hnat : (1061135383 : ℕ)^8427*100000000000000^6379 ≤ 43288036083187^6379*2000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061135383 2000000000 43288036083187 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354924863/2500000000 : ℝ)^8427 ≤ (22260608277957/50000000000000 : ℝ)^6379 := by
    have hnat : (1354924863 : ℕ)^8427*50000000000000^6379 ≤ 22260608277957^6379*2500000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354924863 2500000000 22260608277957 50000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (203306321/1000000000 : ℝ)^8427 ≤ (12190747344511/100000000000000 : ℝ)^6379 := by
    have hnat : (203306321 : ℕ)^8427*100000000000000^6379 ≤ 12190747344511^6379*1000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203306321 1000000000 12190747344511 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061135383/2000000000 : ℝ), (1354924863/2500000000 : ℝ), (-203306321/1000000000 : ℝ)] ![(43288036083187/100000000000000 : ℝ), (22260608277957/50000000000000 : ℝ), (12190747344511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061135383/2000000000 : ℝ)|^8427 ≤ (43288036083187/100000000000000 : ℝ)^6379
        have hw : |(1061135383/2000000000 : ℝ)|=(1061135383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354924863/2500000000 : ℝ)|^8427 ≤ (22260608277957/50000000000000 : ℝ)^6379
        have hw : |(1354924863/2500000000 : ℝ)|=(1354924863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-203306321/1000000000 : ℝ)|^8427 ≤ (12190747344511/100000000000000 : ℝ)^6379
        have hw : |(-203306321/1000000000 : ℝ)|=(203306321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s3_7 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4350163057/10000000000 : ℝ)*x 0 + (2267592467/5000000000 : ℝ)*x 1 + (4172552251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350163057/10000000000 : ℝ)^8427 ≤ (33300172915573/100000000000000 : ℝ)^6379 := by
    have hnat : (4350163057 : ℕ)^8427*100000000000000^6379 ≤ 33300172915573^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350163057 10000000000 33300172915573 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2267592467/5000000000 : ℝ)^8427 ≤ (8795968148319/25000000000000 : ℝ)^6379 := by
    have hnat : (2267592467 : ℕ)^8427*25000000000000^6379 ≤ 8795968148319^6379*5000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267592467 5000000000 8795968148319 25000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172552251/10000000000 : ℝ)^8427 ≤ (15757977236129/50000000000000 : ℝ)^6379 := by
    have hnat : (4172552251 : ℕ)^8427*50000000000000^6379 ≤ 15757977236129^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172552251 10000000000 15757977236129 50000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350163057/10000000000 : ℝ), (2267592467/5000000000 : ℝ), (4172552251/10000000000 : ℝ)] ![(33300172915573/100000000000000 : ℝ), (8795968148319/25000000000000 : ℝ), (15757977236129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350163057/10000000000 : ℝ)|^8427 ≤ (33300172915573/100000000000000 : ℝ)^6379
        have hw : |(4350163057/10000000000 : ℝ)|=(4350163057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2267592467/5000000000 : ℝ)|^8427 ≤ (8795968148319/25000000000000 : ℝ)^6379
        have hw : |(2267592467/5000000000 : ℝ)|=(2267592467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172552251/10000000000 : ℝ)|^8427 ≤ (15757977236129/50000000000000 : ℝ)^6379
        have hw : |(4172552251/10000000000 : ℝ)|=(4172552251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1234_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151271873/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4061/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10891/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3677/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4061/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9467/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4061/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9467/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4061/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9467/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4061/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9467/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4061/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9467/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4061/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9467/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9467/100000 : ℝ) ^ (4213/1024 : ℝ) ≤ (1533959109630463/25000000000000000000 : ℝ) := by
    have hpowers : (9467/100000 : ℝ)^4213 ≤ (1533959109630463/25000000000000000000 : ℝ)^1024 := by
      have hnat : (9467 : ℕ)^4213*25000000000000000000^1024 ≤ 1533959109630463^1024*100000^4213 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9467 100000 1533959109630463 25000000000000000000 4213 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9467/100000 : ℝ)) (X := (1533959109630463/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4213 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4061/25000 : ℝ) ^ (4213/1024 : ℝ) ≤ (2262806518753519/4000000000000000000 : ℝ) := by
    have hpowers : (4061/25000 : ℝ)^4213 ≤ (2262806518753519/4000000000000000000 : ℝ)^1024 := by
      have hnat : (4061 : ℕ)^4213*4000000000000000000^1024 ≤ 2262806518753519^1024*25000^4213 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4061 25000 2262806518753519 4000000000000000000 4213 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4061/25000 : ℝ)) (X := (2262806518753519/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4213 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501533959109630463/12500000000000000000 : ℝ) ≤ (5000149128998743/5000000000000000 : ℝ) ^ (4213/1024 : ℝ) := by
    have hpowers : (12501533959109630463/12500000000000000000 : ℝ)^1024 ≤ (5000149128998743/5000000000000000 : ℝ)^4213 := by
      have hnat : (12501533959109630463 : ℕ)^1024*5000000000000000^4213 ≤ 5000149128998743^4213*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501533959109630463 12500000000000000000 5000149128998743 5000000000000000 1024 4213 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000149128998743/5000000000000000 : ℝ)) (X := (12501533959109630463/12500000000000000000 : ℝ)) (by norm_num) 4213 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100062705999407359827/100000000000000000000 : ℝ) ≤ (10001523752911739/10000000000000000 : ℝ) ^ (4213/1024 : ℝ) := by
    have hpowers : (100062705999407359827/100000000000000000000 : ℝ)^1024 ≤ (10001523752911739/10000000000000000 : ℝ)^4213 := by
      have hnat : (100062705999407359827 : ℕ)^1024*10000000000000000^4213 ≤ 10001523752911739^4213*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100062705999407359827 100000000000000000000 10001523752911739 10000000000000000 1024 4213 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001523752911739/10000000000000000 : ℝ)) (X := (100062705999407359827/100000000000000000000 : ℝ)) (by norm_num) 4213 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2002262806518753519/2000000000000000000 : ℝ) ≤ (1250343655978249/1250000000000000 : ℝ) ^ (4213/1024 : ℝ) := by
    have hpowers : (2002262806518753519/2000000000000000000 : ℝ)^1024 ≤ (1250343655978249/1250000000000000 : ℝ)^4213 := by
      have hnat : (2002262806518753519 : ℕ)^1024*1250000000000000^4213 ≤ 1250343655978249^4213*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2002262806518753519 2000000000000000000 1250343655978249 1250000000000000 1024 4213 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250343655978249/1250000000000000 : ℝ)) (X := (2002262806518753519/2000000000000000000 : ℝ)) (by norm_num) 4213 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1533959109630463/25000000000000000000 : ℝ) ≤ ((70571685180981767/70593750000000000 : ℝ)+2*(408498304751/225900000000000 : ℝ)*(9467/100000 : ℝ))^(4213/1024 : ℝ) := by
    rw [show (70571685180981767/70593750000000000 : ℝ)+2*(408498304751/225900000000000 : ℝ)*(9467/100000 : ℝ)=(5000149128998743/5000000000000000 : ℝ) by norm_num, show 1+2*(1533959109630463/25000000000000000000 : ℝ)=(12501533959109630463/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2262806518753519/4000000000000000000 : ℝ)+(1533959109630463/25000000000000000000 : ℝ) ≤ ((70571685180981767/70593750000000000 : ℝ)+(408498304751/225900000000000 : ℝ)*((4061/25000 : ℝ)+(9467/100000 : ℝ)))^(4213/1024 : ℝ) := by
    rw [show (70571685180981767/70593750000000000 : ℝ)+(408498304751/225900000000000 : ℝ)*((4061/25000 : ℝ)+(9467/100000 : ℝ))=(10001523752911739/10000000000000000 : ℝ) by norm_num, show 1+(2262806518753519/4000000000000000000 : ℝ)+(1533959109630463/25000000000000000000 : ℝ)=(100062705999407359827/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2262806518753519/4000000000000000000 : ℝ) ≤ ((70571685180981767/70593750000000000 : ℝ)+2*(408498304751/225900000000000 : ℝ)*(4061/25000 : ℝ))^(4213/1024 : ℝ) := by
    rw [show (70571685180981767/70593750000000000 : ℝ)+2*(408498304751/225900000000000 : ℝ)*(4061/25000 : ℝ)=(1250343655978249/1250000000000000 : ℝ) by norm_num, show 1+2*(2262806518753519/4000000000000000000 : ℝ)=(2002262806518753519/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (70571685180981767/70593750000000000 : ℝ)*(X 1 0+X 2 0)+(408498304751/225900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4213/1024 : ℝ)) (lo := (9467/100000 : ℝ)) (hi := (4061/25000 : ℝ)) (c := (70571685180981767/70593750000000000 : ℝ)) (alpha := (408498304751/225900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (70571685180981767/70593750000000000 : ℝ)*(X 0 1+X 2 1)+(408498304751/225900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4213/1024 : ℝ)) (lo := (9467/100000 : ℝ)) (hi := (4061/25000 : ℝ)) (c := (70571685180981767/70593750000000000 : ℝ)) (alpha := (408498304751/225900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (70571685180981767/70593750000000000 : ℝ)*(X 0 2+X 1 2)+(408498304751/225900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4213/1024 : ℝ)) (lo := (9467/100000 : ℝ)) (hi := (4061/25000 : ℝ)) (c := (70571685180981767/70593750000000000 : ℝ)) (alpha := (408498304751/225900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-212073893/1000000000 : ℝ)*X 0 0+(1084072353/2000000000 : ℝ)*X 0 1+(5240000919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53516667/100000000 : ℝ)*X 1 0+(-2212761513/10000000000 : ℝ)*X 1 1+(327500067/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351666597/10000000000 : ℝ)*X 2 0+(2620000743/5000000000 : ℝ)*X 2 1+(-138297569/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((174005357/400000000 : ℝ)*X 0 0+(2085605511/5000000000 : ℝ)*X 0 1+(567064921/1250000000 : ℝ)*X 0 2+(174005357/400000000 : ℝ)*X 1 0+(2085605511/5000000000 : ℝ)*X 1 1+(567064921/1250000000 : ℝ)*X 1 2+(174005357/400000000 : ℝ)*X 2 0+(2085605511/5000000000 : ℝ)*X 2 1+(567064921/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2120753657/10000000000 : ℝ)*X 0 0+(81885309/156250000 : ℝ)*X 0 1+(1083939821/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305677611/10000000000 : ℝ)*X 1 0+(-2033062821/10000000000 : ℝ)*X 1 1+(1083939809/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061135383/2000000000 : ℝ)*X 2 0+(1354924863/2500000000 : ℝ)*X 2 1+(-203306321/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4350163057/10000000000 : ℝ)*X 0 0+(2267592467/5000000000 : ℝ)*X 0 1+(4172552251/10000000000 : ℝ)*X 0 2+(4350163057/10000000000 : ℝ)*X 1 0+(2267592467/5000000000 : ℝ)*X 1 1+(4172552251/10000000000 : ℝ)*X 1 2+(4350163057/10000000000 : ℝ)*X 2 0+(2267592467/5000000000 : ℝ)*X 2 1+(4172552251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7381260305102068392979807/2353125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (749373/2500000000000 : ℝ)*(base19) + (7190057/10000000000000 : ℝ)*(lower2) + (36049913/50000000000000 : ℝ)*(lower3) + (13105327/20000000000000 : ℝ)*(lower4) + (1656380068741/40000000000 : ℝ)*(major0) + (1656380068741/40000000000 : ℝ)*(major1) + (2070475085926251/50000000000000 : ℝ)*(major2) + (2772228986565897/50000000000000 : ℝ)*(sp0) + (110889349402819/2000000000000 : ℝ)*(sp1) + (5544477815710049/100000000000000 : ℝ)*(sp2) + (2737418460922679/100000000000000 : ℝ)*(sp3) + (3968515651/20000000000000 : ℝ)*(sp4) + (10315594179/100000000000000 : ℝ)*(sp5) + (61914259/1562500000000 : ℝ)*(sp7) + (547484484687051/20000000000000 : ℝ)*(f.failure) + (5544477815710049/100000000000000 : ℝ)*(f.sum) + (37340044879411/11295000000000000000000000000 : ℝ)*base65 + (230151861769651/11295000000000000000000000000 : ℝ)*base68 + (40285977301327909/7059375000000000000000000000000 : ℝ)*base69 + (206813636512531/11295000000000000000000000000 : ℝ)*base72 + (1667693864177/1411875000000000000000000000 : ℝ)*base73 + (46350848771809159/7059375000000000000000000000000 : ℝ)*base75 + (25062290566177/1882500000000000000000000000 : ℝ)*base78 + (46504356327997/1882500000000000000000000000 : ℝ)*base80 + (1342255352833/564750000000000000000000000 : ℝ)*base81 + (23616523/2000000000000000000000 : ℝ)*base89 + (23616523/2000000000000000000000 : ℝ)*base91 + (16383477/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1622251552566597280583511/392187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2061715139/100000000000000 : ℝ)*(base19) + (255687303/20000000000000 : ℝ)*(base23) + (23369091/50000000000000 : ℝ)*(upper2) + (5387017/5000000000000 : ℝ)*(upper3) + (89376879/50000000000000 : ℝ)*(upper5) + (1042870913428753/25000000000000 : ℝ)*(major0) + (1042870913428753/25000000000000 : ℝ)*(major1) + (1042870913428753/25000000000000 : ℝ)*(major2) + (22345134647/50000000000000 : ℝ)*(sp1) + (28690542613/100000000000000 : ℝ)*(sp2) + (5585360239069337/100000000000000 : ℝ)*(sp4) + (698164185885613/12500000000000 : ℝ)*(sp5) + (5585330270090209/100000000000000 : ℝ)*(sp6) + (344700866310009/12500000000000 : ℝ)*(sp7) + (344700866310009/12500000000000 : ℝ)*(f.failure) + (5585360239069337/100000000000000 : ℝ)*(f.sum) + (11744438508013/11295000000000000000000000000 : ℝ)*base66 + (11748413925030841/1176562500000000000000000000000 : ℝ)*base68 + (17226130218314807/2353125000000000000000000000000 : ℝ)*base70 + (1011911735181659/1176562500000000000000000000000 : ℝ)*base71 + (10334955908189/5647500000000000000000000000 : ℝ)*base74 + (9553793260155841/1176562500000000000000000000000 : ℝ)*base76 + (299754321312091/1176562500000000000000000000000 : ℝ)*base78 + (3452429466516983/588281250000000000000000000000 : ℝ)*base80 + (35038291002419/5647500000000000000000000000 : ℝ)*base82 + (10076857/1250000000000000000000 : ℝ)*base89 + (10076857/1250000000000000000000 : ℝ)*base91 + (10076857/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1234_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151271873/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4061/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10891/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1234_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1234_s4_0 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1061540567/5000000000 : ℝ)*x 0 + (5397815951/10000000000 : ℝ)*x 1 + (2630506051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061540567/5000000000 : ℝ)^8427 ≤ (2581766043319/20000000000000 : ℝ)^6379 := by
    have hnat : (1061540567 : ℕ)^8427*20000000000000^6379 ≤ 2581766043319^6379*5000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061540567 5000000000 2581766043319 20000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397815951/10000000000 : ℝ)^8427 ≤ (44283889545383/100000000000000 : ℝ)^6379 := by
    have hnat : (5397815951 : ℕ)^8427*100000000000000^6379 ≤ 44283889545383^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397815951 10000000000 44283889545383 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630506051/5000000000 : ℝ)^8427 ≤ (21403640112917/50000000000000 : ℝ)^6379 := by
    have hnat : (2630506051 : ℕ)^8427*50000000000000^6379 ≤ 21403640112917^6379*5000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630506051 5000000000 21403640112917 50000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1061540567/5000000000 : ℝ), (5397815951/10000000000 : ℝ), (2630506051/5000000000 : ℝ)] ![(2581766043319/20000000000000 : ℝ), (44283889545383/100000000000000 : ℝ), (21403640112917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1061540567/5000000000 : ℝ)|^8427 ≤ (2581766043319/20000000000000 : ℝ)^6379
        have hw : |(-1061540567/5000000000 : ℝ)|=(1061540567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397815951/10000000000 : ℝ)|^8427 ≤ (44283889545383/100000000000000 : ℝ)^6379
        have hw : |(5397815951/10000000000 : ℝ)|=(5397815951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630506051/5000000000 : ℝ)|^8427 ≤ (21403640112917/50000000000000 : ℝ)^6379
        have hw : |(2630506051/5000000000 : ℝ)|=(2630506051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s4_1 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672993613/5000000000 : ℝ)*x 0 + (-438508657/2000000000 : ℝ)*x 1 + (5261012091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672993613/5000000000 : ℝ)^8427 ≤ (8744607779281/20000000000000 : ℝ)^6379 := by
    have hnat : (2672993613 : ℕ)^8427*20000000000000^6379 ≤ 8744607779281^6379*5000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672993613 5000000000 8744607779281 20000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438508657/2000000000 : ℝ)^8427 ≤ (1346968097413/10000000000000 : ℝ)^6379 := by
    have hnat : (438508657 : ℕ)^8427*10000000000000^6379 ≤ 1346968097413^6379*2000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438508657 2000000000 1346968097413 10000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261012091/10000000000 : ℝ)^8427 ≤ (8561456021519/20000000000000 : ℝ)^6379 := by
    have hnat : (5261012091 : ℕ)^8427*20000000000000^6379 ≤ 8561456021519^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261012091 10000000000 8561456021519 20000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672993613/5000000000 : ℝ), (-438508657/2000000000 : ℝ), (5261012091/10000000000 : ℝ)] ![(8744607779281/20000000000000 : ℝ), (1346968097413/10000000000000 : ℝ), (8561456021519/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672993613/5000000000 : ℝ)|^8427 ≤ (8744607779281/20000000000000 : ℝ)^6379
        have hw : |(2672993613/5000000000 : ℝ)|=(2672993613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-438508657/2000000000 : ℝ)|^8427 ≤ (1346968097413/10000000000000 : ℝ)^6379
        have hw : |(-438508657/2000000000 : ℝ)|=(438508657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261012091/10000000000 : ℝ)|^8427 ≤ (8561456021519/20000000000000 : ℝ)^6379
        have hw : |(5261012091/10000000000 : ℝ)|=(5261012091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s4_2 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672993611/5000000000 : ℝ)*x 0 + (2630506009/5000000000 : ℝ)*x 1 + (-2192543387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672993611/5000000000 : ℝ)^8427 ≤ (43723038853187/100000000000000 : ℝ)^6379 := by
    have hnat : (2672993611 : ℕ)^8427*100000000000000^6379 ≤ 43723038853187^6379*5000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672993611 5000000000 43723038853187 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630506009/5000000000 : ℝ)^8427 ≤ (42807279322917/100000000000000 : ℝ)^6379 := by
    have hnat : (2630506009 : ℕ)^8427*100000000000000^6379 ≤ 42807279322917^6379*5000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630506009 5000000000 42807279322917 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2192543387/10000000000 : ℝ)^8427 ≤ (6734840900969/50000000000000 : ℝ)^6379 := by
    have hnat : (2192543387 : ℕ)^8427*50000000000000^6379 ≤ 6734840900969^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192543387 10000000000 6734840900969 50000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672993611/5000000000 : ℝ), (2630506009/5000000000 : ℝ), (-2192543387/10000000000 : ℝ)] ![(43723038853187/100000000000000 : ℝ), (42807279322917/100000000000000 : ℝ), (6734840900969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672993611/5000000000 : ℝ)|^8427 ≤ (43723038853187/100000000000000 : ℝ)^6379
        have hw : |(2672993611/5000000000 : ℝ)|=(2672993611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630506009/5000000000 : ℝ)|^8427 ≤ (42807279322917/100000000000000 : ℝ)^6379
        have hw : |(2630506009/5000000000 : ℝ)|=(2630506009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2192543387/10000000000 : ℝ)|^8427 ≤ (6734840900969/50000000000000 : ℝ)^6379
        have hw : |(-2192543387/10000000000 : ℝ)|=(2192543387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s4_3 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (217576903/500000000 : ℝ)*x 0 + (526892741/1250000000 : ℝ)*x 1 + (4492229631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217576903/500000000 : ℝ)^8427 ≤ (16657039214423/50000000000000 : ℝ)^6379 := by
    have hnat : (217576903 : ℕ)^8427*50000000000000^6379 ≤ 16657039214423^6379*500000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217576903 500000000 16657039214423 50000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526892741/1250000000 : ℝ)^8427 ≤ (199635090199/625000000000 : ℝ)^6379 := by
    have hnat : (526892741 : ℕ)^8427*625000000000^6379 ≤ 199635090199^6379*1250000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526892741 1250000000 199635090199 625000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4492229631/10000000000 : ℝ)^8427 ≤ (34744307119903/100000000000000 : ℝ)^6379 := by
    have hnat : (4492229631 : ℕ)^8427*100000000000000^6379 ≤ 34744307119903^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492229631 10000000000 34744307119903 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217576903/500000000 : ℝ), (526892741/1250000000 : ℝ), (4492229631/10000000000 : ℝ)] ![(16657039214423/50000000000000 : ℝ), (199635090199/625000000000 : ℝ), (34744307119903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217576903/500000000 : ℝ)|^8427 ≤ (16657039214423/50000000000000 : ℝ)^6379
        have hw : |(217576903/500000000 : ℝ)|=(217576903/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526892741/1250000000 : ℝ)|^8427 ≤ (199635090199/625000000000 : ℝ)^6379
        have hw : |(526892741/1250000000 : ℝ)|=(526892741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4492229631/10000000000 : ℝ)|^8427 ≤ (34744307119903/100000000000000 : ℝ)^6379
        have hw : |(4492229631/10000000000 : ℝ)|=(4492229631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s4_4 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2123087311/10000000000 : ℝ)*x 0 + (5261391629/10000000000 : ℝ)*x 1 + (674679369/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123087311/10000000000 : ℝ)^8427 ≤ (12908879832223/100000000000000 : ℝ)^6379 := by
    have hnat : (2123087311 : ℕ)^8427*100000000000000^6379 ≤ 12908879832223^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123087311 10000000000 12908879832223 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261391629/10000000000 : ℝ)^8427 ≤ (21405679907517/50000000000000 : ℝ)^6379 := by
    have hnat : (5261391629 : ℕ)^8427*50000000000000^6379 ≤ 21405679907517^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261391629 10000000000 21405679907517 50000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674679369/1250000000 : ℝ)^8427 ≤ (44279760335167/100000000000000 : ℝ)^6379 := by
    have hnat : (674679369 : ℕ)^8427*100000000000000^6379 ≤ 44279760335167^6379*1250000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674679369 1250000000 44279760335167 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2123087311/10000000000 : ℝ), (5261391629/10000000000 : ℝ), (674679369/1250000000 : ℝ)] ![(12908879832223/100000000000000 : ℝ), (21405679907517/50000000000000 : ℝ), (44279760335167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2123087311/10000000000 : ℝ)|^8427 ≤ (12908879832223/100000000000000 : ℝ)^6379
        have hw : |(-2123087311/10000000000 : ℝ)|=(2123087311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261391629/10000000000 : ℝ)|^8427 ≤ (21405679907517/50000000000000 : ℝ)^6379
        have hw : |(5261391629/10000000000 : ℝ)|=(5261391629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674679369/1250000000 : ℝ)|^8427 ≤ (44279760335167/100000000000000 : ℝ)^6379
        have hw : |(674679369/1250000000 : ℝ)|=(674679369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s4_5 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655550853/5000000000 : ℝ)*x 0 + (-2056120451/10000000000 : ℝ)*x 1 + (1079487001/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655550853/5000000000 : ℝ)^8427 ≤ (43346515326411/100000000000000 : ℝ)^6379 := by
    have hnat : (2655550853 : ℕ)^8427*100000000000000^6379 ≤ 43346515326411^6379*5000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655550853 5000000000 43346515326411 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2056120451/10000000000 : ℝ)^8427 ≤ (12373723754229/100000000000000 : ℝ)^6379 := by
    have hnat : (2056120451 : ℕ)^8427*100000000000000^6379 ≤ 12373723754229^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056120451 10000000000 12373723754229 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079487001/2000000000 : ℝ)^8427 ≤ (22139880454783/50000000000000 : ℝ)^6379 := by
    have hnat : (1079487001 : ℕ)^8427*50000000000000^6379 ≤ 22139880454783^6379*2000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079487001 2000000000 22139880454783 50000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655550853/5000000000 : ℝ), (-2056120451/10000000000 : ℝ), (1079487001/2000000000 : ℝ)] ![(43346515326411/100000000000000 : ℝ), (12373723754229/100000000000000 : ℝ), (22139880454783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655550853/5000000000 : ℝ)|^8427 ≤ (43346515326411/100000000000000 : ℝ)^6379
        have hw : |(2655550853/5000000000 : ℝ)|=(2655550853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2056120451/10000000000 : ℝ)|^8427 ≤ (12373723754229/100000000000000 : ℝ)^6379
        have hw : |(-2056120451/10000000000 : ℝ)|=(2056120451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079487001/2000000000 : ℝ)|^8427 ≤ (22139880454783/50000000000000 : ℝ)^6379
        have hw : |(1079487001/2000000000 : ℝ)|=(1079487001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s4_6 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2655550893/5000000000 : ℝ)*x 0 + (674679361/1250000000 : ℝ)*x 1 + (-4112241/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655550893/5000000000 : ℝ)^8427 ≤ (5418314523619/12500000000000 : ℝ)^6379 := by
    have hnat : (2655550893 : ℕ)^8427*12500000000000^6379 ≤ 5418314523619^6379*5000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655550893 5000000000 5418314523619 12500000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674679361/1250000000 : ℝ)^8427 ≤ (2767484977597/6250000000000 : ℝ)^6379 := by
    have hnat : (674679361 : ℕ)^8427*6250000000000^6379 ≤ 2767484977597^6379*1250000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674679361 1250000000 2767484977597 6250000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4112241/20000000 : ℝ)^8427 ≤ (1546715517973/12500000000000 : ℝ)^6379 := by
    have hnat : (4112241 : ℕ)^8427*12500000000000^6379 ≤ 1546715517973^6379*20000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4112241 20000000 1546715517973 12500000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655550893/5000000000 : ℝ), (674679361/1250000000 : ℝ), (-4112241/20000000 : ℝ)] ![(5418314523619/12500000000000 : ℝ), (2767484977597/6250000000000 : ℝ), (1546715517973/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655550893/5000000000 : ℝ)|^8427 ≤ (5418314523619/12500000000000 : ℝ)^6379
        have hw : |(2655550893/5000000000 : ℝ)|=(2655550893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674679361/1250000000 : ℝ)|^8427 ≤ (2767484977597/6250000000000 : ℝ)^6379
        have hw : |(674679361/1250000000 : ℝ)|=(674679361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4112241/20000000 : ℝ)|^8427 ≤ (1546715517973/12500000000000 : ℝ)^6379
        have hw : |(-4112241/20000000 : ℝ)|=(4112241/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s4_7 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (271971919/625000000 : ℝ)*x 0 + (2245730411/5000000000 : ℝ)*x 1 + (1053978449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271971919/625000000 : ℝ)^8427 ≤ (33314206305157/100000000000000 : ℝ)^6379 := by
    have hnat : (271971919 : ℕ)^8427*100000000000000^6379 ≤ 33314206305157^6379*625000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271971919 625000000 33314206305157 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245730411/5000000000 : ℝ)^8427 ≤ (17368226037919/50000000000000 : ℝ)^6379 := by
    have hnat : (2245730411 : ℕ)^8427*50000000000000^6379 ≤ 17368226037919^6379*5000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245730411 5000000000 17368226037919 50000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053978449/2500000000 : ℝ)^8427 ≤ (31949341608733/100000000000000 : ℝ)^6379 := by
    have hnat : (1053978449 : ℕ)^8427*100000000000000^6379 ≤ 31949341608733^6379*2500000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053978449 2500000000 31949341608733 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271971919/625000000 : ℝ), (2245730411/5000000000 : ℝ), (1053978449/2500000000 : ℝ)] ![(33314206305157/100000000000000 : ℝ), (17368226037919/50000000000000 : ℝ), (31949341608733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271971919/625000000 : ℝ)|^8427 ≤ (33314206305157/100000000000000 : ℝ)^6379
        have hw : |(271971919/625000000 : ℝ)|=(271971919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245730411/5000000000 : ℝ)|^8427 ≤ (17368226037919/50000000000000 : ℝ)^6379
        have hw : |(2245730411/5000000000 : ℝ)|=(2245730411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053978449/2500000000 : ℝ)|^8427 ≤ (31949341608733/100000000000000 : ℝ)^6379
        have hw : |(1053978449/2500000000 : ℝ)|=(1053978449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1234_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151271873/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10891/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11339/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3677/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10891/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3677/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10891/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3677/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10891/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3677/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10891/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3677/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10891/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3677/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10891/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10891/100000 : ℝ) ^ (4213/1024 : ℝ) ≤ (10920650305698027/100000000000000000000 : ℝ) := by
    have hpowers : (10891/100000 : ℝ)^4213 ≤ (10920650305698027/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10891 : ℕ)^4213*100000000000000000000^1024 ≤ 10920650305698027^1024*100000^4213 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10891 100000 10920650305698027 100000000000000000000 4213 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10891/100000 : ℝ)) (X := (10920650305698027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4213 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3677/25000 : ℝ) ^ (4213/1024 : ℝ) ≤ (37592480448161161/100000000000000000000 : ℝ) := by
    have hpowers : (3677/25000 : ℝ)^4213 ≤ (37592480448161161/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3677 : ℕ)^4213*100000000000000000000^1024 ≤ 37592480448161161^1024*25000^4213 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3677 25000 37592480448161161 100000000000000000000 4213 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3677/25000 : ℝ)) (X := (37592480448161161/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4213 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010920650305698027/50000000000000000000 : ℝ) ≤ (2000106164933597/2000000000000000 : ℝ) ^ (4213/1024 : ℝ) := by
    have hpowers : (50010920650305698027/50000000000000000000 : ℝ)^1024 ≤ (2000106164933597/2000000000000000 : ℝ)^4213 := by
      have hnat : (50010920650305698027 : ℕ)^1024*2000000000000000^4213 ≤ 2000106164933597^4213*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010920650305698027 50000000000000000000 2000106164933597 2000000000000000 1024 4213 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000106164933597/2000000000000000 : ℝ)) (X := (50010920650305698027/50000000000000000000 : ℝ)) (by norm_num) 4213 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012128282688464797/25000000000000000000 : ℝ) ≤ (10001178930151673/10000000000000000 : ℝ) ^ (4213/1024 : ℝ) := by
    have hpowers : (25012128282688464797/25000000000000000000 : ℝ)^1024 ≤ (10001178930151673/10000000000000000 : ℝ)^4213 := by
      have hnat : (25012128282688464797 : ℕ)^1024*10000000000000000^4213 ≤ 10001178930151673^4213*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012128282688464797 25000000000000000000 10001178930151673 10000000000000000 1024 4213 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001178930151673/10000000000000000 : ℝ)) (X := (25012128282688464797/25000000000000000000 : ℝ)) (by norm_num) 4213 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037592480448161161/50000000000000000000 : ℝ) ≤ (10001827035635361/10000000000000000 : ℝ) ^ (4213/1024 : ℝ) := by
    have hpowers : (50037592480448161161/50000000000000000000 : ℝ)^1024 ≤ (10001827035635361/10000000000000000 : ℝ)^4213 := by
      have hnat : (50037592480448161161 : ℕ)^1024*10000000000000000^4213 ≤ 10001827035635361^4213*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037592480448161161 50000000000000000000 10001827035635361 10000000000000000 1024 4213 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001827035635361/10000000000000000 : ℝ)) (X := (50037592480448161161/50000000000000000000 : ℝ)) (by norm_num) 4213 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10920650305698027/100000000000000000000 : ℝ) ≤ ((38157909124112006729/38170000000000000000 : ℝ)+2*(81013185461/47712500000000 : ℝ)*(10891/100000 : ℝ))^(4213/1024 : ℝ) := by
    rw [show (38157909124112006729/38170000000000000000 : ℝ)+2*(81013185461/47712500000000 : ℝ)*(10891/100000 : ℝ)=(2000106164933597/2000000000000000 : ℝ) by norm_num, show 1+2*(10920650305698027/100000000000000000000 : ℝ)=(50010920650305698027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37592480448161161/100000000000000000000 : ℝ)+(10920650305698027/100000000000000000000 : ℝ) ≤ ((38157909124112006729/38170000000000000000 : ℝ)+(81013185461/47712500000000 : ℝ)*((3677/25000 : ℝ)+(10891/100000 : ℝ)))^(4213/1024 : ℝ) := by
    rw [show (38157909124112006729/38170000000000000000 : ℝ)+(81013185461/47712500000000 : ℝ)*((3677/25000 : ℝ)+(10891/100000 : ℝ))=(10001178930151673/10000000000000000 : ℝ) by norm_num, show 1+(37592480448161161/100000000000000000000 : ℝ)+(10920650305698027/100000000000000000000 : ℝ)=(25012128282688464797/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37592480448161161/100000000000000000000 : ℝ) ≤ ((38157909124112006729/38170000000000000000 : ℝ)+2*(81013185461/47712500000000 : ℝ)*(3677/25000 : ℝ))^(4213/1024 : ℝ) := by
    rw [show (38157909124112006729/38170000000000000000 : ℝ)+2*(81013185461/47712500000000 : ℝ)*(3677/25000 : ℝ)=(10001827035635361/10000000000000000 : ℝ) by norm_num, show 1+2*(37592480448161161/100000000000000000000 : ℝ)=(50037592480448161161/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38157909124112006729/38170000000000000000 : ℝ)*(X 1 0+X 2 0)+(81013185461/47712500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4213/1024 : ℝ)) (lo := (10891/100000 : ℝ)) (hi := (3677/25000 : ℝ)) (c := (38157909124112006729/38170000000000000000 : ℝ)) (alpha := (81013185461/47712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38157909124112006729/38170000000000000000 : ℝ)*(X 0 1+X 2 1)+(81013185461/47712500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4213/1024 : ℝ)) (lo := (10891/100000 : ℝ)) (hi := (3677/25000 : ℝ)) (c := (38157909124112006729/38170000000000000000 : ℝ)) (alpha := (81013185461/47712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38157909124112006729/38170000000000000000 : ℝ)*(X 0 2+X 1 2)+(81013185461/47712500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4213/1024 : ℝ)) (lo := (10891/100000 : ℝ)) (hi := (3677/25000 : ℝ)) (c := (38157909124112006729/38170000000000000000 : ℝ)) (alpha := (81013185461/47712500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1061540567/5000000000 : ℝ)*X 0 0+(5397815951/10000000000 : ℝ)*X 0 1+(2630506051/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672993613/5000000000 : ℝ)*X 1 0+(-438508657/2000000000 : ℝ)*X 1 1+(5261012091/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672993611/5000000000 : ℝ)*X 2 0+(2630506009/5000000000 : ℝ)*X 2 1+(-2192543387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((217576903/500000000 : ℝ)*X 0 0+(526892741/1250000000 : ℝ)*X 0 1+(4492229631/10000000000 : ℝ)*X 0 2+(217576903/500000000 : ℝ)*X 1 0+(526892741/1250000000 : ℝ)*X 1 1+(4492229631/10000000000 : ℝ)*X 1 2+(217576903/500000000 : ℝ)*X 2 0+(526892741/1250000000 : ℝ)*X 2 1+(4492229631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2123087311/10000000000 : ℝ)*X 0 0+(5261391629/10000000000 : ℝ)*X 0 1+(674679369/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655550853/5000000000 : ℝ)*X 1 0+(-2056120451/10000000000 : ℝ)*X 1 1+(1079487001/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655550893/5000000000 : ℝ)*X 2 0+(674679361/1250000000 : ℝ)*X 2 1+(-4112241/20000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((271971919/625000000 : ℝ)*X 0 0+(2245730411/5000000000 : ℝ)*X 0 1+(1053978449/2500000000 : ℝ)*X 0 2+(271971919/625000000 : ℝ)*X 1 0+(2245730411/5000000000 : ℝ)*X 1 1+(1053978449/2500000000 : ℝ)*X 1 2+(271971919/625000000 : ℝ)*X 2 0+(2245730411/5000000000 : ℝ)*X 2 1+(1053978449/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (458270886551645929732384161/173500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (237196987/25000000000000 : ℝ)*(base19) + (109846343/12500000000000 : ℝ)*(base23) + (19189641/100000000000000 : ℝ)*(upper2) + (40186289/20000000000000 : ℝ)*(upper3) + (26848419/50000000000000 : ℝ)*(upper4) + (5459383742969167/100000000000000 : ℝ)*(major0) + (5459383742969167/100000000000000 : ℝ)*(major1) + (5459383742969167/100000000000000 : ℝ)*(major2) + (7309761758000381/100000000000000 : ℝ)*(sp0) + (1461955689950253/20000000000000 : ℝ)*(sp1) + (7309778519768469/100000000000000 : ℝ)*(sp2) + (451121847585379/12500000000000 : ℝ)*(sp3) + (1102533677/6250000000000 : ℝ)*(sp4) + (13218671723/100000000000000 : ℝ)*(sp7) + (902246999838689/25000000000000 : ℝ)*(f.failure) + (7309779398539213/100000000000000 : ℝ)*(f.sum) + (9790566029313/867500000000000000000000000 : ℝ)*base65 + (3866295782808738613/347000000000000000000000000000000 : ℝ)*base67 + (1550083980953738613/347000000000000000000000000000000 : ℝ)*base69 + (301405021118261387/347000000000000000000000000000000 : ℝ)*base72 + (8169640834941/1735000000000000000000000000 : ℝ)*base73 + (1016285750629261387/347000000000000000000000000000000 : ℝ)*base76 + (1744103685765738613/347000000000000000000000000000000 : ℝ)*base77 + (1844553796107738613/347000000000000000000000000000000 : ℝ)*base79 + (8717986335741/1735000000000000000000000000 : ℝ)*base81 + (7894497/2500000000000000000000 : ℝ)*base89 + (7894497/2500000000000000000000 : ℝ)*base91 + (7894497/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7610868336442952777215450221/1908500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (456133693/50000000000000 : ℝ)*(base19) + (1026718459/100000000000000 : ℝ)*(base23) + (1956601/12500000000000 : ℝ)*(upper2) + (72819437/100000000000000 : ℝ)*(upper3) + (70886983/50000000000000 : ℝ)*(upper5) + (5489873466396061/100000000000000 : ℝ)*(major0) + (5489873466396061/100000000000000 : ℝ)*(major1) + (5489873466396061/100000000000000 : ℝ)*(major2) + (7073880407/25000000000000 : ℝ)*(sp1) + (12188310111/50000000000000 : ℝ)*(sp2) + (7350603220477043/100000000000000 : ℝ)*(sp4) + (735057401268803/10000000000000 : ℝ)*(sp5) + (3675288908569181/50000000000000 : ℝ)*(sp6) + (1814571789692873/50000000000000 : ℝ)*(sp7) + (1814571789692873/50000000000000 : ℝ)*(f.failure) + (7350603220477043/100000000000000 : ℝ)*(f.sum) + (62703299379967/19085000000000000000000000000 : ℝ)*base66 + (5897334987095105531/3817000000000000000000000000000000 : ℝ)*base68 + (6321184182876105531/3817000000000000000000000000000000 : ℝ)*base70 + (180430997056105531/3817000000000000000000000000000000 : ℝ)*base72 + (21695967675149/9542500000000000000000000000 : ℝ)*base73 + (118253515843630105531/3817000000000000000000000000000000 : ℝ)*base76 + (610281337492105531/3817000000000000000000000000000000 : ℝ)*base78 + (6351284708980105531/3817000000000000000000000000000000 : ℝ)*base80 + (8756871345851/9542500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (56538871/5000000000000000000000 : ℝ)*base90 + (56538871/5000000000000000000000 : ℝ)*base92 + (56538871/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1234_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151271873/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10891/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1234_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1234_s5_0 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2123543617/10000000000 : ℝ)*x 0 + (5392599153/10000000000 : ℝ)*x 1 + (5265924913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123543617/10000000000 : ℝ)^8427 ≤ (6456272577633/50000000000000 : ℝ)^6379 := by
    have hnat : (2123543617 : ℕ)^8427*50000000000000^6379 ≤ 6456272577633^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123543617 10000000000 6456272577633 50000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392599153/10000000000 : ℝ)^8427 ≤ (44227358801403/100000000000000 : ℝ)^6379 := by
    have hnat : (5392599153 : ℕ)^8427*100000000000000^6379 ≤ 44227358801403^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392599153 10000000000 44227358801403 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265924913/10000000000 : ℝ)^8427 ≤ (42860096026329/100000000000000 : ℝ)^6379 := by
    have hnat : (5265924913 : ℕ)^8427*100000000000000^6379 ≤ 42860096026329^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265924913 10000000000 42860096026329 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2123543617/10000000000 : ℝ), (5392599153/10000000000 : ℝ), (5265924913/10000000000 : ℝ)] ![(6456272577633/50000000000000 : ℝ), (44227358801403/100000000000000 : ℝ), (42860096026329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2123543617/10000000000 : ℝ)|^8427 ≤ (6456272577633/50000000000000 : ℝ)^6379
        have hw : |(-2123543617/10000000000 : ℝ)|=(2123543617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392599153/10000000000 : ℝ)|^8427 ≤ (44227358801403/100000000000000 : ℝ)^6379
        have hw : |(5392599153/10000000000 : ℝ)|=(5392599153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265924913/10000000000 : ℝ)|^8427 ≤ (42860096026329/100000000000000 : ℝ)^6379
        have hw : |(5265924913/10000000000 : ℝ)|=(5265924913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s5_1 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534466799/1000000000 : ℝ)*x 0 + (-2187790127/10000000000 : ℝ)*x 1 + (2632962421/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534466799/1000000000 : ℝ)^8427 ≤ (43708785836739/100000000000000 : ℝ)^6379 := by
    have hnat : (534466799 : ℕ)^8427*100000000000000^6379 ≤ 43708785836739^6379*1000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534466799 1000000000 43708785836739 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2187790127/10000000000 : ℝ)^8427 ≤ (1343111888619/10000000000000 : ℝ)^6379 := by
    have hnat : (2187790127 : ℕ)^8427*10000000000000^6379 ≤ 1343111888619^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187790127 10000000000 1343111888619 10000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632962421/5000000000 : ℝ)^8427 ≤ (1071502381573/2500000000000 : ℝ)^6379 := by
    have hnat : (2632962421 : ℕ)^8427*2500000000000^6379 ≤ 1071502381573^6379*5000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632962421 5000000000 1071502381573 2500000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534466799/1000000000 : ℝ), (-2187790127/10000000000 : ℝ), (2632962421/5000000000 : ℝ)] ![(43708785836739/100000000000000 : ℝ), (1343111888619/10000000000000 : ℝ), (1071502381573/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534466799/1000000000 : ℝ)|^8427 ≤ (43708785836739/100000000000000 : ℝ)^6379
        have hw : |(534466799/1000000000 : ℝ)|=(534466799/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2187790127/10000000000 : ℝ)|^8427 ≤ (1343111888619/10000000000000 : ℝ)^6379
        have hw : |(-2187790127/10000000000 : ℝ)|=(2187790127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632962421/5000000000 : ℝ)|^8427 ≤ (1071502381573/2500000000000 : ℝ)^6379
        have hw : |(2632962421/5000000000 : ℝ)|=(2632962421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s5_2 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672334173/5000000000 : ℝ)*x 0 + (1053184957/2000000000 : ℝ)*x 1 + (-2187789729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672334173/5000000000 : ℝ)^8427 ≤ (2185439484141/5000000000000 : ℝ)^6379 := by
    have hnat : (2672334173 : ℕ)^8427*5000000000000^6379 ≤ 2185439484141^6379*5000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672334173 5000000000 2185439484141 5000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053184957/2000000000 : ℝ)^8427 ≤ (21430047325021/50000000000000 : ℝ)^6379 := by
    have hnat : (1053184957 : ℕ)^8427*50000000000000^6379 ≤ 21430047325021^6379*2000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053184957 2000000000 21430047325021 50000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2187789729/10000000000 : ℝ)^8427 ≤ (2686223131673/20000000000000 : ℝ)^6379 := by
    have hnat : (2187789729 : ℕ)^8427*20000000000000^6379 ≤ 2686223131673^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187789729 10000000000 2686223131673 20000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672334173/5000000000 : ℝ), (1053184957/2000000000 : ℝ), (-2187789729/10000000000 : ℝ)] ![(2185439484141/5000000000000 : ℝ), (21430047325021/50000000000000 : ℝ), (2686223131673/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672334173/5000000000 : ℝ)|^8427 ≤ (2185439484141/5000000000000 : ℝ)^6379
        have hw : |(2672334173/5000000000 : ℝ)|=(2672334173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053184957/2000000000 : ℝ)|^8427 ≤ (21430047325021/50000000000000 : ℝ)^6379
        have hw : |(1053184957/2000000000 : ℝ)|=(1053184957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2187789729/10000000000 : ℝ)|^8427 ≤ (2686223131673/20000000000000 : ℝ)^6379
        have hw : |(-2187789729/10000000000 : ℝ)|=(2187789729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s5_3 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2175904237/5000000000 : ℝ)*x 0 + (4225367401/10000000000 : ℝ)*x 1 + (1120483923/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2175904237/5000000000 : ℝ)^8427 ≤ (33316813312867/100000000000000 : ℝ)^6379 := by
    have hnat : (2175904237 : ℕ)^8427*100000000000000^6379 ≤ 33316813312867^6379*5000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2175904237 5000000000 33316813312867 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4225367401/10000000000 : ℝ)^8427 ≤ (32044018558049/100000000000000 : ℝ)^6379 := by
    have hnat : (4225367401 : ℕ)^8427*100000000000000^6379 ≤ 32044018558049^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225367401 10000000000 32044018558049 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120483923/2500000000 : ℝ)^8427 ≤ (34639168124489/100000000000000 : ℝ)^6379 := by
    have hnat : (1120483923 : ℕ)^8427*100000000000000^6379 ≤ 34639168124489^6379*2500000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120483923 2500000000 34639168124489 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2175904237/5000000000 : ℝ), (4225367401/10000000000 : ℝ), (1120483923/2500000000 : ℝ)] ![(33316813312867/100000000000000 : ℝ), (32044018558049/100000000000000 : ℝ), (34639168124489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2175904237/5000000000 : ℝ)|^8427 ≤ (33316813312867/100000000000000 : ℝ)^6379
        have hw : |(2175904237/5000000000 : ℝ)|=(2175904237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4225367401/10000000000 : ℝ)|^8427 ≤ (32044018558049/100000000000000 : ℝ)^6379
        have hw : |(4225367401/10000000000 : ℝ)|=(4225367401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1120483923/2500000000 : ℝ)|^8427 ≤ (34639168124489/100000000000000 : ℝ)^6379
        have hw : |(1120483923/2500000000 : ℝ)|=(1120483923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s5_4 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2123548779/10000000000 : ℝ)*x 0 + (1053250147/2000000000 : ℝ)*x 1 + (215690879/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123548779/10000000000 : ℝ)^8427 ≤ (3228146655247/25000000000000 : ℝ)^6379 := by
    have hnat : (2123548779 : ℕ)^8427*25000000000000^6379 ≤ 3228146655247^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123548779 10000000000 3228146655247 25000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053250147/2000000000 : ℝ)^8427 ≤ (42863599376817/100000000000000 : ℝ)^6379 := by
    have hnat : (1053250147 : ℕ)^8427*100000000000000^6379 ≤ 42863599376817^6379*2000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053250147 2000000000 42863599376817 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215690879/400000000 : ℝ)^8427 ≤ (4422381399011/10000000000000 : ℝ)^6379 := by
    have hnat : (215690879 : ℕ)^8427*10000000000000^6379 ≤ 4422381399011^6379*400000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215690879 400000000 4422381399011 10000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2123548779/10000000000 : ℝ), (1053250147/2000000000 : ℝ), (215690879/400000000 : ℝ)] ![(3228146655247/25000000000000 : ℝ), (42863599376817/100000000000000 : ℝ), (4422381399011/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2123548779/10000000000 : ℝ)|^8427 ≤ (3228146655247/25000000000000 : ℝ)^6379
        have hw : |(-2123548779/10000000000 : ℝ)|=(2123548779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053250147/2000000000 : ℝ)|^8427 ≤ (42863599376817/100000000000000 : ℝ)^6379
        have hw : |(1053250147/2000000000 : ℝ)|=(1053250147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215690879/400000000 : ℝ)|^8427 ≤ (4422381399011/10000000000000 : ℝ)^6379
        have hw : |(215690879/400000000 : ℝ)|=(215690879/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s5_5 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656182171/5000000000 : ℝ)*x 0 + (-2061443077/10000000000 : ℝ)*x 1 + (215690879/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656182171/5000000000 : ℝ)^8427 ≤ (21680064646867/50000000000000 : ℝ)^6379 := by
    have hnat : (2656182171 : ℕ)^8427*50000000000000^6379 ≤ 21680064646867^6379*5000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656182171 5000000000 21680064646867 50000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2061443077/10000000000 : ℝ)^8427 ≤ (6208028352171/50000000000000 : ℝ)^6379 := by
    have hnat : (2061443077 : ℕ)^8427*50000000000000^6379 ≤ 6208028352171^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061443077 10000000000 6208028352171 50000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215690879/400000000 : ℝ)^8427 ≤ (4422381399011/10000000000000 : ℝ)^6379 := by
    have hnat : (215690879 : ℕ)^8427*10000000000000^6379 ≤ 4422381399011^6379*400000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215690879 400000000 4422381399011 10000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656182171/5000000000 : ℝ), (-2061443077/10000000000 : ℝ), (215690879/400000000 : ℝ)] ![(21680064646867/50000000000000 : ℝ), (6208028352171/50000000000000 : ℝ), (4422381399011/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656182171/5000000000 : ℝ)|^8427 ≤ (21680064646867/50000000000000 : ℝ)^6379
        have hw : |(2656182171/5000000000 : ℝ)|=(2656182171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2061443077/10000000000 : ℝ)|^8427 ≤ (6208028352171/50000000000000 : ℝ)^6379
        have hw : |(-2061443077/10000000000 : ℝ)|=(2061443077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215690879/400000000 : ℝ)|^8427 ≤ (4422381399011/10000000000000 : ℝ)^6379
        have hw : |(215690879/400000000 : ℝ)|=(215690879/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s5_6 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312364341/10000000000 : ℝ)*x 0 + (215690879/400000000 : ℝ)*x 1 + (-1030721539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312364341/10000000000 : ℝ)^8427 ≤ (43360129282951/100000000000000 : ℝ)^6379 := by
    have hnat : (5312364341 : ℕ)^8427*100000000000000^6379 ≤ 43360129282951^6379*10000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312364341 10000000000 43360129282951 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215690879/400000000 : ℝ)^8427 ≤ (4422381399011/10000000000000 : ℝ)^6379 := by
    have hnat : (215690879 : ℕ)^8427*10000000000000^6379 ≤ 4422381399011^6379*400000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215690879 400000000 4422381399011 10000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030721539/5000000000 : ℝ)^8427 ≤ (6208028356149/50000000000000 : ℝ)^6379 := by
    have hnat : (1030721539 : ℕ)^8427*50000000000000^6379 ≤ 6208028356149^6379*5000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030721539 5000000000 6208028356149 50000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312364341/10000000000 : ℝ), (215690879/400000000 : ℝ), (-1030721539/5000000000 : ℝ)] ![(43360129282951/100000000000000 : ℝ), (4422381399011/10000000000000 : ℝ), (6208028356149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312364341/10000000000 : ℝ)|^8427 ≤ (43360129282951/100000000000000 : ℝ)^6379
        have hw : |(5312364341/10000000000 : ℝ)|=(5312364341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215690879/400000000 : ℝ)|^8427 ≤ (4422381399011/10000000000000 : ℝ)^6379
        have hw : |(215690879/400000000 : ℝ)|=(215690879/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1030721539/5000000000 : ℝ)|^8427 ≤ (6208028356149/50000000000000 : ℝ)^6379
        have hw : |(-1030721539/5000000000 : ℝ)|=(1030721539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1234_s5_7 (p : ℝ) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870363887/2000000000 : ℝ)*x 0 + (2240638183/5000000000 : ℝ)*x 1 + (169041129/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870363887/2000000000 : ℝ)^8427 ≤ (166584620851/500000000000 : ℝ)^6379 := by
    have hnat : (870363887 : ℕ)^8427*500000000000^6379 ≤ 166584620851^6379*2000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870363887 2000000000 166584620851 500000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2240638183/5000000000 : ℝ)^8427 ≤ (34632436619523/100000000000000 : ℝ)^6379 := by
    have hnat : (2240638183 : ℕ)^8427*100000000000000^6379 ≤ 34632436619523^6379*5000000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240638183 5000000000 34632436619523 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169041129/400000000 : ℝ)^8427 ≤ (32050639192339/100000000000000 : ℝ)^6379 := by
    have hnat : (169041129 : ℕ)^8427*100000000000000^6379 ≤ 32050639192339^6379*400000000^8427 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169041129 400000000 32050639192339 100000000000000 8427 6379 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8427/2048 : ℝ)) 8427 6379 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870363887/2000000000 : ℝ), (2240638183/5000000000 : ℝ), (169041129/400000000 : ℝ)] ![(166584620851/500000000000 : ℝ), (34632436619523/100000000000000 : ℝ), (32050639192339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870363887/2000000000 : ℝ)|^8427 ≤ (166584620851/500000000000 : ℝ)^6379
        have hw : |(870363887/2000000000 : ℝ)|=(870363887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2240638183/5000000000 : ℝ)|^8427 ≤ (34632436619523/100000000000000 : ℝ)^6379
        have hw : |(2240638183/5000000000 : ℝ)|=(2240638183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169041129/400000000 : ℝ)|^8427 ≤ (32050639192339/100000000000000 : ℝ)^6379
        have hw : |(169041129/400000000 : ℝ)|=(169041129/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1234_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151271873/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11443/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14127/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11339/100000 : ℝ) ^ (4213/1024 : ℝ) ≤ (2578141777794421/20000000000000000000 : ℝ) := by
    have hpowers : (11339/100000 : ℝ)^4213 ≤ (2578141777794421/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11339 : ℕ)^4213*20000000000000000000^1024 ≤ 2578141777794421^1024*100000^4213 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11339 100000 2578141777794421 20000000000000000000 4213 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11339/100000 : ℝ)) (X := (2578141777794421/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4213 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (4213/1024 : ℝ) ≤ (32871527055044169/100000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^4213 ≤ (32871527055044169/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3559 : ℕ)^4213*100000000000000000000^1024 ≤ 32871527055044169^1024*25000^4213 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 32871527055044169 100000000000000000000 4213 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (32871527055044169/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4213 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002578141777794421/10000000000000000000 : ℝ) ≤ (2500156643699199/2500000000000000 : ℝ) ^ (4213/1024 : ℝ) := by
    have hpowers : (10002578141777794421/10000000000000000000 : ℝ)^1024 ≤ (2500156643699199/2500000000000000 : ℝ)^4213 := by
      have hnat : (10002578141777794421 : ℕ)^1024*2500000000000000^4213 ≤ 2500156643699199^4213*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002578141777794421 10000000000000000000 2500156643699199 2500000000000000 1024 4213 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500156643699199/2500000000000000 : ℝ)) (X := (10002578141777794421/10000000000000000000 : ℝ)) (by norm_num) 4213 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022881117972008137/50000000000000000000 : ℝ) ≤ (2000222418303723/2000000000000000 : ℝ) ^ (4213/1024 : ℝ) := by
    have hpowers : (50022881117972008137/50000000000000000000 : ℝ)^1024 ≤ (2000222418303723/2000000000000000 : ℝ)^4213 := by
      have hnat : (50022881117972008137 : ℕ)^1024*2000000000000000^4213 ≤ 2000222418303723^4213*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022881117972008137 50000000000000000000 2000222418303723 2000000000000000 1024 4213 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000222418303723/2000000000000000 : ℝ)) (X := (50022881117972008137/50000000000000000000 : ℝ)) (by norm_num) 4213 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032871527055044169/50000000000000000000 : ℝ) ≤ (5000798804120217/5000000000000000 : ℝ) ^ (4213/1024 : ℝ) := by
    have hpowers : (50032871527055044169/50000000000000000000 : ℝ)^1024 ≤ (5000798804120217/5000000000000000 : ℝ)^4213 := by
      have hnat : (50032871527055044169 : ℕ)^1024*5000000000000000^4213 ≤ 5000798804120217^4213*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032871527055044169 50000000000000000000 5000798804120217 5000000000000000 1024 4213 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000798804120217/5000000000000000 : ℝ)) (X := (50032871527055044169/50000000000000000000 : ℝ)) (by norm_num) 4213 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2578141777794421/20000000000000000000 : ℝ) ≤ ((2896080463896890673/2897000000000000000 : ℝ)+2*(485516721819/289700000000000 : ℝ)*(11339/100000 : ℝ))^(4213/1024 : ℝ) := by
    rw [show (2896080463896890673/2897000000000000000 : ℝ)+2*(485516721819/289700000000000 : ℝ)*(11339/100000 : ℝ)=(2500156643699199/2500000000000000 : ℝ) by norm_num, show 1+2*(2578141777794421/20000000000000000000 : ℝ)=(10002578141777794421/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32871527055044169/100000000000000000000 : ℝ)+(2578141777794421/20000000000000000000 : ℝ) ≤ ((2896080463896890673/2897000000000000000 : ℝ)+(485516721819/289700000000000 : ℝ)*((3559/25000 : ℝ)+(11339/100000 : ℝ)))^(4213/1024 : ℝ) := by
    rw [show (2896080463896890673/2897000000000000000 : ℝ)+(485516721819/289700000000000 : ℝ)*((3559/25000 : ℝ)+(11339/100000 : ℝ))=(2000222418303723/2000000000000000 : ℝ) by norm_num, show 1+(32871527055044169/100000000000000000000 : ℝ)+(2578141777794421/20000000000000000000 : ℝ)=(50022881117972008137/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32871527055044169/100000000000000000000 : ℝ) ≤ ((2896080463896890673/2897000000000000000 : ℝ)+2*(485516721819/289700000000000 : ℝ)*(3559/25000 : ℝ))^(4213/1024 : ℝ) := by
    rw [show (2896080463896890673/2897000000000000000 : ℝ)+2*(485516721819/289700000000000 : ℝ)*(3559/25000 : ℝ)=(5000798804120217/5000000000000000 : ℝ) by norm_num, show 1+2*(32871527055044169/100000000000000000000 : ℝ)=(50032871527055044169/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2896080463896890673/2897000000000000000 : ℝ)*(X 1 0+X 2 0)+(485516721819/289700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4213/1024 : ℝ)) (lo := (11339/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (2896080463896890673/2897000000000000000 : ℝ)) (alpha := (485516721819/289700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2896080463896890673/2897000000000000000 : ℝ)*(X 0 1+X 2 1)+(485516721819/289700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4213/1024 : ℝ)) (lo := (11339/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (2896080463896890673/2897000000000000000 : ℝ)) (alpha := (485516721819/289700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2896080463896890673/2897000000000000000 : ℝ)*(X 0 2+X 1 2)+(485516721819/289700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4213/1024 : ℝ)) (lo := (11339/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (2896080463896890673/2897000000000000000 : ℝ)) (alpha := (485516721819/289700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2123543617/10000000000 : ℝ)*X 0 0+(5392599153/10000000000 : ℝ)*X 0 1+(5265924913/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534466799/1000000000 : ℝ)*X 1 0+(-2187790127/10000000000 : ℝ)*X 1 1+(2632962421/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672334173/5000000000 : ℝ)*X 2 0+(1053184957/2000000000 : ℝ)*X 2 1+(-2187789729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2175904237/5000000000 : ℝ)*X 0 0+(4225367401/10000000000 : ℝ)*X 0 1+(1120483923/2500000000 : ℝ)*X 0 2+(2175904237/5000000000 : ℝ)*X 1 0+(4225367401/10000000000 : ℝ)*X 1 1+(1120483923/2500000000 : ℝ)*X 1 2+(2175904237/5000000000 : ℝ)*X 2 0+(4225367401/10000000000 : ℝ)*X 2 1+(1120483923/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2123548779/10000000000 : ℝ)*X 0 0+(1053250147/2000000000 : ℝ)*X 0 1+(215690879/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656182171/5000000000 : ℝ)*X 1 0+(-2061443077/10000000000 : ℝ)*X 1 1+(215690879/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312364341/10000000000 : ℝ)*X 2 0+(215690879/400000000 : ℝ)*X 2 1+(-1030721539/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((870363887/2000000000 : ℝ)*X 0 0+(2240638183/5000000000 : ℝ)*X 0 1+(169041129/400000000 : ℝ)*X 0 2+(870363887/2000000000 : ℝ)*X 1 0+(2240638183/5000000000 : ℝ)*X 1 1+(169041129/400000000 : ℝ)*X 1 2+(870363887/2000000000 : ℝ)*X 2 0+(2240638183/5000000000 : ℝ)*X 2 1+(169041129/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1234_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1530876788476012619683894773/144850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (400584747/25000000000000 : ℝ)*(base19) + (251383701/12500000000000 : ℝ)*(base23) + (104141247/100000000000000 : ℝ)*(lower3) + (123615253/100000000000000 : ℝ)*(upper4) + (1474006174429929/25000000000000 : ℝ)*(major0) + (1474006174429929/25000000000000 : ℝ)*(major1) + (5896024697719717/100000000000000 : ℝ)*(major2) + (7894331816102587/100000000000000 : ℝ)*(sp0) + (3947197028888789/50000000000000 : ℝ)*(sp1) + (1973603135188939/25000000000000 : ℝ)*(sp2) + (974403724468079/25000000000000 : ℝ)*(sp3) + (41367861389/50000000000000 : ℝ)*(sp4) + (5903659/31250000000 : ℝ)*(sp5) + (4898362901/25000000000000 : ℝ)*(sp7) + (48720431141549/1250000000000 : ℝ)*(f.failure) + (1578882910365073/20000000000000 : ℝ)*(f.sum) + (150666875010117/28970000000000000000000000000 : ℝ)*base65 + (631486149665715283/72425000000000000000000000000000 : ℝ)*base68 + (474407897625439541/289700000000000000000000000000000 : ℝ)*base69 + (371183300036009717/72425000000000000000000000000000 : ℝ)*base71 + (107967774995847/28970000000000000000000000000 : ℝ)*base73 + (3725978623933939541/289700000000000000000000000000000 : ℝ)*base75 + (2269926273053162217/72425000000000000000000000000000 : ℝ)*base77 + (429357508788662217/72425000000000000000000000000000 : ℝ)*base79 + (9211231845219/3621250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (351277/125000000000000000000 : ℝ)*base89 + (351277/125000000000000000000 : ℝ)*base91 + (898723/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59958418114276302595107/7242500000000000000000000000 : ℝ) := by norm_num
    linear_combination (298575261/20000000000000 : ℝ)*(base19) + (1616883227/100000000000000 : ℝ)*(base23) + (41798079/25000000000000 : ℝ)*(upper3) + (57289769/100000000000000 : ℝ)*(lower4) + (4239449/2500000000000 : ℝ)*(upper5) + (5926462413329669/100000000000000 : ℝ)*(major0) + (5926462413329669/100000000000000 : ℝ)*(major1) + (5926462413329669/100000000000000 : ℝ)*(major2) + (41210628991/100000000000000 : ℝ)*(sp1) + (44114068237/100000000000000 : ℝ)*(sp2) + (247974026865927/3125000000000 : ℝ)*(sp4) + (7935126156204367/100000000000000 : ℝ)*(sp5) + (39675615643791/500000000000 : ℝ)*(sp6) + (979438922748327/25000000000000 : ℝ)*(sp7) + (979438922748327/25000000000000 : ℝ)*(f.failure) + (247974026865927/3125000000000 : ℝ)*(f.sum) + (18705463539229/14485000000000000000000000000 : ℝ)*base66 + (1320960477289787237/289700000000000000000000000000000 : ℝ)*base67 + (2114163916110612763/289700000000000000000000000000000 : ℝ)*base70 + (1200746908294587237/289700000000000000000000000000000 : ℝ)*base71 + (23888614981909/14485000000000000000000000000 : ℝ)*base74 + (2367692798886512763/289700000000000000000000000000000 : ℝ)*base76 + (418702917346012763/289700000000000000000000000000000 : ℝ)*base78 + (2802950954641287237/289700000000000000000000000000000 : ℝ)*base79 + (31933515369921/3621250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (7906471/2500000000000000000000 : ℝ)*base89 + (7906471/2500000000000000000000 : ℝ)*base91 + (7906471/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1234_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151271873/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11443/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14127/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1234_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1234_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151271873/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4061/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11443/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14127/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1234_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1234_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1234_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4213/1024 : ℝ) ≤ p) (hpb : p ≤ (8427/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151271873/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4061/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9467/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11443/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14127/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1234_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

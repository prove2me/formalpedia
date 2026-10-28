-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1036_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:43:06.61785+00:00
-- url     : https://prove2.me/submissions/82728556-00be-4683-9ea5-f85005518a9e

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
theorem support_rectangle_w1036_s6_0 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-443713889/2000000000 : ℝ)*x 0 + (1348884057/2500000000 : ℝ)*x 1 + (5263265717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (443713889/2000000000 : ℝ)^8229 ≤ (3367768261021/25000000000000 : ℝ)^6181 := by
    have hnat : (443713889 : ℕ)^8229*25000000000000^6181 ≤ 3367768261021^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443713889 2000000000 3367768261021 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348884057/2500000000 : ℝ)^8229 ≤ (1099480456011/2500000000000 : ℝ)^6181 := by
    have hnat : (1348884057 : ℕ)^8229*2500000000000^6181 ≤ 1099480456011^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348884057 2500000000 1099480456011 2500000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263265717/10000000000 : ℝ)^8229 ≤ (42549708710519/100000000000000 : ℝ)^6181 := by
    have hnat : (5263265717 : ℕ)^8229*100000000000000^6181 ≤ 42549708710519^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263265717 10000000000 42549708710519 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-443713889/2000000000 : ℝ), (1348884057/2500000000 : ℝ), (5263265717/10000000000 : ℝ)] ![(3367768261021/25000000000000 : ℝ), (1099480456011/2500000000000 : ℝ), (42549708710519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-443713889/2000000000 : ℝ)|^8229 ≤ (3367768261021/25000000000000 : ℝ)^6181
        have hw : |(-443713889/2000000000 : ℝ)|=(443713889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348884057/2500000000 : ℝ)|^8229 ≤ (1099480456011/2500000000000 : ℝ)^6181
        have hw : |(1348884057/2500000000 : ℝ)|=(1348884057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263265717/10000000000 : ℝ)|^8229 ≤ (42549708710519/100000000000000 : ℝ)^6181
        have hw : |(5263265717/10000000000 : ℝ)|=(5263265717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s6_1 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345203789/10000000000 : ℝ)*x 0 + (-285712157/1250000000 : ℝ)*x 1 + (3289541/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345203789/10000000000 : ℝ)^8229 ≤ (868677345539/2000000000000 : ℝ)^6181 := by
    have hnat : (5345203789 : ℕ)^8229*2000000000000^6181 ≤ 868677345539^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345203789 10000000000 868677345539 2000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285712157/1250000000 : ℝ)^8229 ≤ (2803285052779/20000000000000 : ℝ)^6181 := by
    have hnat : (285712157 : ℕ)^8229*20000000000000^6181 ≤ 2803285052779^6181*1250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285712157 1250000000 2803285052779 20000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3289541/6250000 : ℝ)^8229 ≤ (21274853725629/50000000000000 : ℝ)^6181 := by
    have hnat : (3289541 : ℕ)^8229*50000000000000^6181 ≤ 21274853725629^6181*6250000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3289541 6250000 21274853725629 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345203789/10000000000 : ℝ), (-285712157/1250000000 : ℝ), (3289541/6250000 : ℝ)] ![(868677345539/2000000000000 : ℝ), (2803285052779/20000000000000 : ℝ), (21274853725629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345203789/10000000000 : ℝ)|^8229 ≤ (868677345539/2000000000000 : ℝ)^6181
        have hw : |(5345203789/10000000000 : ℝ)|=(5345203789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-285712157/1250000000 : ℝ)|^8229 ≤ (2803285052779/20000000000000 : ℝ)^6181
        have hw : |(-285712157/1250000000 : ℝ)|=(285712157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3289541/6250000 : ℝ)|^8229 ≤ (21274853725629/50000000000000 : ℝ)^6181
        have hw : |(3289541/6250000 : ℝ)|=(3289541/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s6_2 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345203657/10000000000 : ℝ)*x 0 + (5263265769/10000000000 : ℝ)*x 1 + (-2285697207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345203657/10000000000 : ℝ)^8229 ≤ (10858466462239/25000000000000 : ℝ)^6181 := by
    have hnat : (5345203657 : ℕ)^8229*25000000000000^6181 ≤ 10858466462239^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345203657 10000000000 10858466462239 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263265769/10000000000 : ℝ)^8229 ≤ (4254970927019/10000000000000 : ℝ)^6181 := by
    have hnat : (5263265769 : ℕ)^8229*10000000000000^6181 ≤ 4254970927019^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263265769 10000000000 4254970927019 10000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2285697207/10000000000 : ℝ)^8229 ≤ (2803284972771/20000000000000 : ℝ)^6181 := by
    have hnat : (2285697207 : ℕ)^8229*20000000000000^6181 ≤ 2803284972771^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285697207 10000000000 2803284972771 20000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345203657/10000000000 : ℝ), (5263265769/10000000000 : ℝ), (-2285697207/10000000000 : ℝ)] ![(10858466462239/25000000000000 : ℝ), (4254970927019/10000000000000 : ℝ), (2803284972771/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345203657/10000000000 : ℝ)|^8229 ≤ (10858466462239/25000000000000 : ℝ)^6181
        have hw : |(5345203657/10000000000 : ℝ)|=(5345203657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263265769/10000000000 : ℝ)|^8229 ≤ (4254970927019/10000000000000 : ℝ)^6181
        have hw : |(5263265769/10000000000 : ℝ)|=(5263265769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2285697207/10000000000 : ℝ)|^8229 ≤ (2803284972771/20000000000000 : ℝ)^6181
        have hw : |(-2285697207/10000000000 : ℝ)|=(2285697207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s6_3 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (875958321/2000000000 : ℝ)*x 0 + (2126440371/5000000000 : ℝ)*x 1 + (4510569773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875958321/2000000000 : ℝ)^8229 ≤ (33316038808357/100000000000000 : ℝ)^6181 := by
    have hnat : (875958321 : ℕ)^8229*100000000000000^6181 ≤ 33316038808357^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875958321 2000000000 33316038808357 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126440371/5000000000 : ℝ)^8229 ≤ (32037000709239/100000000000000 : ℝ)^6181 := by
    have hnat : (2126440371 : ℕ)^8229*100000000000000^6181 ≤ 32037000709239^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126440371 5000000000 32037000709239 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4510569773/10000000000 : ℝ)^8229 ≤ (17323480232883/50000000000000 : ℝ)^6181 := by
    have hnat : (4510569773 : ℕ)^8229*50000000000000^6181 ≤ 17323480232883^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510569773 10000000000 17323480232883 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875958321/2000000000 : ℝ), (2126440371/5000000000 : ℝ), (4510569773/10000000000 : ℝ)] ![(33316038808357/100000000000000 : ℝ), (32037000709239/100000000000000 : ℝ), (17323480232883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875958321/2000000000 : ℝ)|^8229 ≤ (33316038808357/100000000000000 : ℝ)^6181
        have hw : |(875958321/2000000000 : ℝ)|=(875958321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2126440371/5000000000 : ℝ)|^8229 ≤ (32037000709239/100000000000000 : ℝ)^6181
        have hw : |(2126440371/5000000000 : ℝ)|=(2126440371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4510569773/10000000000 : ℝ)|^8229 ≤ (17323480232883/50000000000000 : ℝ)^6181
        have hw : |(4510569773/10000000000 : ℝ)|=(4510569773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s6_4 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1109287403/5000000000 : ℝ)*x 0 + (1315899949/2500000000 : ℝ)*x 1 + (5395200883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1109287403/5000000000 : ℝ)^8229 ≤ (2694223276309/20000000000000 : ℝ)^6181 := by
    have hnat : (1109287403 : ℕ)^8229*20000000000000^6181 ≤ 2694223276309^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109287403 5000000000 2694223276309 20000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315899949/2500000000 : ℝ)^8229 ≤ (8510660881951/20000000000000 : ℝ)^6181 := by
    have hnat : (1315899949 : ℕ)^8229*20000000000000^6181 ≤ 8510660881951^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315899949 2500000000 8510660881951 20000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395200883/10000000000 : ℝ)^8229 ≤ (43975579185817/100000000000000 : ℝ)^6181 := by
    have hnat : (5395200883 : ℕ)^8229*100000000000000^6181 ≤ 43975579185817^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395200883 10000000000 43975579185817 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1109287403/5000000000 : ℝ), (1315899949/2500000000 : ℝ), (5395200883/10000000000 : ℝ)] ![(2694223276309/20000000000000 : ℝ), (8510660881951/20000000000000 : ℝ), (43975579185817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1109287403/5000000000 : ℝ)|^8229 ≤ (2694223276309/20000000000000 : ℝ)^6181
        have hw : |(-1109287403/5000000000 : ℝ)|=(1109287403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315899949/2500000000 : ℝ)|^8229 ≤ (8510660881951/20000000000000 : ℝ)^6181
        have hw : |(1315899949/2500000000 : ℝ)|=(1315899949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395200883/10000000000 : ℝ)|^8229 ≤ (43975579185817/100000000000000 : ℝ)^6181
        have hw : |(5395200883/10000000000 : ℝ)|=(5395200883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s6_5 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311967853/10000000000 : ℝ)*x 0 + (-1076881043/5000000000 : ℝ)*x 1 + (2697600467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311967853/10000000000 : ℝ)^8229 ≤ (21537343599717/50000000000000 : ℝ)^6181 := by
    have hnat : (5311967853 : ℕ)^8229*50000000000000^6181 ≤ 21537343599717^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311967853 10000000000 21537343599717 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076881043/5000000000 : ℝ)^8229 ≤ (129497330371/1000000000000 : ℝ)^6181 := by
    have hnat : (1076881043 : ℕ)^8229*1000000000000^6181 ≤ 129497330371^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076881043 5000000000 129497330371 1000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697600467/5000000000 : ℝ)^8229 ≤ (21987789869623/50000000000000 : ℝ)^6181 := by
    have hnat : (2697600467 : ℕ)^8229*50000000000000^6181 ≤ 21987789869623^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697600467 5000000000 21987789869623 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311967853/10000000000 : ℝ), (-1076881043/5000000000 : ℝ), (2697600467/5000000000 : ℝ)] ![(21537343599717/50000000000000 : ℝ), (129497330371/1000000000000 : ℝ), (21987789869623/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311967853/10000000000 : ℝ)|^8229 ≤ (21537343599717/50000000000000 : ℝ)^6181
        have hw : |(5311967853/10000000000 : ℝ)|=(5311967853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1076881043/5000000000 : ℝ)|^8229 ≤ (129497330371/1000000000000 : ℝ)^6181
        have hw : |(-1076881043/5000000000 : ℝ)|=(1076881043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697600467/5000000000 : ℝ)|^8229 ≤ (21987789869623/50000000000000 : ℝ)^6181
        have hw : |(2697600467/5000000000 : ℝ)|=(2697600467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s6_6 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1327991977/2500000000 : ℝ)*x 0 + (2697600409/5000000000 : ℝ)*x 1 + (-2153762171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327991977/2500000000 : ℝ)^8229 ≤ (43074687793203/100000000000000 : ℝ)^6181 := by
    have hnat : (1327991977 : ℕ)^8229*100000000000000^6181 ≤ 43074687793203^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327991977 2500000000 43074687793203 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697600409/5000000000 : ℝ)^8229 ≤ (8795115696093/20000000000000 : ℝ)^6181 := by
    have hnat : (2697600409 : ℕ)^8229*20000000000000^6181 ≤ 8795115696093^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697600409 5000000000 8795115696093 20000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2153762171/10000000000 : ℝ)^8229 ≤ (12949733717509/100000000000000 : ℝ)^6181 := by
    have hnat : (2153762171 : ℕ)^8229*100000000000000^6181 ≤ 12949733717509^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153762171 10000000000 12949733717509 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327991977/2500000000 : ℝ), (2697600409/5000000000 : ℝ), (-2153762171/10000000000 : ℝ)] ![(43074687793203/100000000000000 : ℝ), (8795115696093/20000000000000 : ℝ), (12949733717509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327991977/2500000000 : ℝ)|^8229 ≤ (43074687793203/100000000000000 : ℝ)^6181
        have hw : |(1327991977/2500000000 : ℝ)|=(1327991977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697600409/5000000000 : ℝ)|^8229 ≤ (8795115696093/20000000000000 : ℝ)^6181
        have hw : |(2697600409/5000000000 : ℝ)|=(2697600409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2153762171/10000000000 : ℝ)|^8229 ≤ (12949733717509/100000000000000 : ℝ)^6181
        have hw : |(-2153762171/10000000000 : ℝ)|=(2153762171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s6_7 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (437980203/1000000000 : ℝ)*x 0 + (2254959271/5000000000 : ℝ)*x 1 + (4253534231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437980203/1000000000 : ℝ)^8229 ≤ (33316144384177/100000000000000 : ℝ)^6181 := by
    have hnat : (437980203 : ℕ)^8229*100000000000000^6181 ≤ 33316144384177^6181*1000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437980203 1000000000 33316144384177 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254959271/5000000000 : ℝ)^8229 ≤ (17320150443719/50000000000000 : ℝ)^6181 := by
    have hnat : (2254959271 : ℕ)^8229*50000000000000^6181 ≤ 17320150443719^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254959271 5000000000 17320150443719 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4253534231/10000000000 : ℝ)^8229 ≤ (32043554707197/100000000000000 : ℝ)^6181 := by
    have hnat : (4253534231 : ℕ)^8229*100000000000000^6181 ≤ 32043554707197^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4253534231 10000000000 32043554707197 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(437980203/1000000000 : ℝ), (2254959271/5000000000 : ℝ), (4253534231/10000000000 : ℝ)] ![(33316144384177/100000000000000 : ℝ), (17320150443719/50000000000000 : ℝ), (32043554707197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(437980203/1000000000 : ℝ)|^8229 ≤ (33316144384177/100000000000000 : ℝ)^6181
        have hw : |(437980203/1000000000 : ℝ)|=(437980203/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254959271/5000000000 : ℝ)|^8229 ≤ (17320150443719/50000000000000 : ℝ)^6181
        have hw : |(2254959271/5000000000 : ℝ)|=(2254959271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4253534231/10000000000 : ℝ)|^8229 ≤ (32043554707197/100000000000000 : ℝ)^6181
        have hw : |(4253534231/10000000000 : ℝ)|=(4253534231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1036_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11149/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2799/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6999/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14047/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11149/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14047/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11149/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14047/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11149/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14047/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11149/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14047/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11149/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14047/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11149/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11149/100000 : ℝ) ^ (2057/512 : ℝ) ≤ (2973211824502069/20000000000000000000 : ℝ) := by
    have hpowers : (11149/100000 : ℝ)^2057 ≤ (2973211824502069/20000000000000000000 : ℝ)^512 := by
      have hnat : (11149 : ℕ)^2057*20000000000000000000^512 ≤ 2973211824502069^512*100000^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11149 100000 2973211824502069 20000000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11149/100000 : ℝ)) (X := (2973211824502069/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14047/100000 : ℝ) ^ (2057/512 : ℝ) ≤ (2350880018609213/6250000000000000000 : ℝ) := by
    have hpowers : (14047/100000 : ℝ)^2057 ≤ (2350880018609213/6250000000000000000 : ℝ)^512 := by
      have hnat : (14047 : ℕ)^2057*6250000000000000000^512 ≤ 2350880018609213^512*100000^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14047 100000 2350880018609213 6250000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14047/100000 : ℝ)) (X := (2350880018609213/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002973211824502069/10000000000000000000 : ℝ) ≤ (2500184992040389/2500000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (10002973211824502069/10000000000000000000 : ℝ)^512 ≤ (2500184992040389/2500000000000000 : ℝ)^2057 := by
      have hnat : (10002973211824502069 : ℕ)^512*2500000000000000^2057 ≤ 2500184992040389^2057*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002973211824502069 10000000000000000000 2500184992040389 2500000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500184992040389/2500000000000000 : ℝ)) (X := (10002973211824502069/10000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052480139420257753/100000000000000000000 : ℝ) ≤ (10001306005702273/10000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (100052480139420257753/100000000000000000000 : ℝ)^512 ≤ (10001306005702273/10000000000000000 : ℝ)^2057 := by
      have hnat : (100052480139420257753 : ℕ)^512*10000000000000000^2057 ≤ 10001306005702273^2057*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052480139420257753 100000000000000000000 10001306005702273 10000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001306005702273/10000000000000000 : ℝ)) (X := (100052480139420257753/100000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127350880018609213/3125000000000000000 : ℝ) ≤ (1000187204324299/1000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (3127350880018609213/3125000000000000000 : ℝ)^512 ≤ (1000187204324299/1000000000000000 : ℝ)^2057 := by
      have hnat : (3127350880018609213 : ℕ)^512*1000000000000000^2057 ≤ 1000187204324299^2057*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127350880018609213 3125000000000000000 1000187204324299 1000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000187204324299/1000000000000000 : ℝ)) (X := (3127350880018609213/3125000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2973211824502069/20000000000000000000 : ℝ) ≤ ((4828253820441546937/4830000000000000000 : ℝ)+2*(188679180239/96600000000000 : ℝ)*(11149/100000 : ℝ))^(2057/512 : ℝ) := by
    rw [show (4828253820441546937/4830000000000000000 : ℝ)+2*(188679180239/96600000000000 : ℝ)*(11149/100000 : ℝ)=(2500184992040389/2500000000000000 : ℝ) by norm_num, show 1+2*(2973211824502069/20000000000000000000 : ℝ)=(10002973211824502069/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2350880018609213/6250000000000000000 : ℝ)+(2973211824502069/20000000000000000000 : ℝ) ≤ ((4828253820441546937/4830000000000000000 : ℝ)+(188679180239/96600000000000 : ℝ)*((14047/100000 : ℝ)+(11149/100000 : ℝ)))^(2057/512 : ℝ) := by
    rw [show (4828253820441546937/4830000000000000000 : ℝ)+(188679180239/96600000000000 : ℝ)*((14047/100000 : ℝ)+(11149/100000 : ℝ))=(10001306005702273/10000000000000000 : ℝ) by norm_num, show 1+(2350880018609213/6250000000000000000 : ℝ)+(2973211824502069/20000000000000000000 : ℝ)=(100052480139420257753/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2350880018609213/6250000000000000000 : ℝ) ≤ ((4828253820441546937/4830000000000000000 : ℝ)+2*(188679180239/96600000000000 : ℝ)*(14047/100000 : ℝ))^(2057/512 : ℝ) := by
    rw [show (4828253820441546937/4830000000000000000 : ℝ)+2*(188679180239/96600000000000 : ℝ)*(14047/100000 : ℝ)=(1000187204324299/1000000000000000 : ℝ) by norm_num, show 1+2*(2350880018609213/6250000000000000000 : ℝ)=(3127350880018609213/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4828253820441546937/4830000000000000000 : ℝ)*(X 1 0+X 2 0)+(188679180239/96600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (11149/100000 : ℝ)) (hi := (14047/100000 : ℝ)) (c := (4828253820441546937/4830000000000000000 : ℝ)) (alpha := (188679180239/96600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4828253820441546937/4830000000000000000 : ℝ)*(X 0 1+X 2 1)+(188679180239/96600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (11149/100000 : ℝ)) (hi := (14047/100000 : ℝ)) (c := (4828253820441546937/4830000000000000000 : ℝ)) (alpha := (188679180239/96600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4828253820441546937/4830000000000000000 : ℝ)*(X 0 2+X 1 2)+(188679180239/96600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (11149/100000 : ℝ)) (hi := (14047/100000 : ℝ)) (c := (4828253820441546937/4830000000000000000 : ℝ)) (alpha := (188679180239/96600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-443713889/2000000000 : ℝ)*X 0 0+(1348884057/2500000000 : ℝ)*X 0 1+(5263265717/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345203789/10000000000 : ℝ)*X 1 0+(-285712157/1250000000 : ℝ)*X 1 1+(3289541/6250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345203657/10000000000 : ℝ)*X 2 0+(5263265769/10000000000 : ℝ)*X 2 1+(-2285697207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((875958321/2000000000 : ℝ)*X 0 0+(2126440371/5000000000 : ℝ)*X 0 1+(4510569773/10000000000 : ℝ)*X 0 2+(875958321/2000000000 : ℝ)*X 1 0+(2126440371/5000000000 : ℝ)*X 1 1+(4510569773/10000000000 : ℝ)*X 1 2+(875958321/2000000000 : ℝ)*X 2 0+(2126440371/5000000000 : ℝ)*X 2 1+(4510569773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1109287403/5000000000 : ℝ)*X 0 0+(1315899949/2500000000 : ℝ)*X 0 1+(5395200883/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311967853/10000000000 : ℝ)*X 1 0+(-1076881043/5000000000 : ℝ)*X 1 1+(2697600467/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327991977/2500000000 : ℝ)*X 2 0+(2697600409/5000000000 : ℝ)*X 2 1+(-2153762171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((437980203/1000000000 : ℝ)*X 0 0+(2254959271/5000000000 : ℝ)*X 0 1+(4253534231/10000000000 : ℝ)*X 0 2+(437980203/1000000000 : ℝ)*X 1 0+(2254959271/5000000000 : ℝ)*X 1 1+(4253534231/10000000000 : ℝ)*X 1 2+(437980203/1000000000 : ℝ)*X 2 0+(2254959271/5000000000 : ℝ)*X 2 1+(4253534231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14458975302507809687289183/2012500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (452552223/25000000000000 : ℝ)*(base19) + (738517189/50000000000000 : ℝ)*(base23) + (7829189/10000000000000 : ℝ)*(lower2) + (5737547/3125000000000 : ℝ)*(upper3) + (11330141/10000000000000 : ℝ)*(upper5) + (143013154400747/2500000000000 : ℝ)*(major0) + (143013154400747/2500000000000 : ℝ)*(major1) + (143013154400747/2500000000000 : ℝ)*(major2) + (7560311320039959/100000000000000 : ℝ)*(sp0) + (7560353879366883/100000000000000 : ℝ)*(sp1) + (7560354212541397/100000000000000 : ℝ)*(sp2) + (1940335360443797/50000000000000 : ℝ)*(sp3) + (5546191977/12500000000000 : ℝ)*(sp4) + (3212763781/12500000000000 : ℝ)*(sp7) + (3880696422997841/100000000000000 : ℝ)*(f.failure) + (302414227583031/4000000000000 : ℝ)*(f.sum) + (361263164053/96600000000000000000000000 : ℝ)*base66 + (70146321509611939/12075000000000000000000000000000 : ℝ)*base67 + (125537422869436939/12075000000000000000000000000000 : ℝ)*base69 + (242729344008736939/12075000000000000000000000000000 : ℝ)*base71 + (518427872737/60375000000000000000000000 : ℝ)*base74 + (113281132816261939/12075000000000000000000000000000 : ℝ)*base75 + (18429346619086939/12075000000000000000000000000000 : ℝ)*base77 + (137511404916736939/12075000000000000000000000000000 : ℝ)*base79 + (463995987761/483000000000000000000000000 : ℝ)*base82 + (48721497/10000000000000000000000 : ℝ)*base90 + (48721497/10000000000000000000000 : ℝ)*base92 + (48721497/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (89510720028080769384162429/11500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1618003093/100000000000000 : ℝ)*(base19) + (180449187/10000000000000 : ℝ)*(base23) + (145353307/100000000000000 : ℝ)*(upper3) + (18831841/25000000000000 : ℝ)*(lower4) + (271319083/100000000000000 : ℝ)*(upper5) + (5749558793280127/100000000000000 : ℝ)*(major0) + (5749558793280127/100000000000000 : ℝ)*(major1) + (5749558793280127/100000000000000 : ℝ)*(major2) + (48391745231/100000000000000 : ℝ)*(sp1) + (42958679461/100000000000000 : ℝ)*(sp2) + (7598725727400657/100000000000000 : ℝ)*(sp4) + (7598675717652333/100000000000000 : ℝ)*(sp5) + (303947238569173/4000000000000 : ℝ)*(sp6) + (975097899927057/25000000000000 : ℝ)*(sp7) + (975097899927057/25000000000000 : ℝ)*(f.failure) + (7598725727400657/100000000000000 : ℝ)*(f.sum) + (3135623245859/690000000000000000000000000 : ℝ)*base65 + (461621787870495857/69000000000000000000000000000000 : ℝ)*base67 + (262535863551495857/69000000000000000000000000000000 : ℝ)*base69 + (579425170470495857/69000000000000000000000000000000 : ℝ)*base71 + (1037695148099/690000000000000000000000000 : ℝ)*base73 + (11786241672495857/69000000000000000000000000000000 : ℝ)*base75 + (400704153309495857/69000000000000000000000000000000 : ℝ)*base77 + (1033715113167495857/69000000000000000000000000000000 : ℝ)*base79 + (3324360761939/690000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (13198631/2500000000000000000000 : ℝ)*base89 + (13198631/2500000000000000000000 : ℝ)*base91 + (13198631/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1036_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11149/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2799/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1036_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1036_s7_0 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-443723251/2000000000 : ℝ)*x 0 + (5395001233/10000000000 : ℝ)*x 1 + (2631884977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (443723251/2000000000 : ℝ)^8229 ≤ (13471451449759/100000000000000 : ℝ)^6181 := by
    have hnat : (443723251 : ℕ)^8229*100000000000000^6181 ≤ 13471451449759^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443723251 2000000000 13471451449759 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395001233/10000000000 : ℝ)^8229 ≤ (4397341268469/10000000000000 : ℝ)^6181 := by
    have hnat : (5395001233 : ℕ)^8229*10000000000000^6181 ≤ 4397341268469^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395001233 10000000000 4397341268469 10000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631884977/5000000000 : ℝ)^8229 ≤ (42555135852919/100000000000000 : ℝ)^6181 := by
    have hnat : (2631884977 : ℕ)^8229*100000000000000^6181 ≤ 42555135852919^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631884977 5000000000 42555135852919 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-443723251/2000000000 : ℝ), (5395001233/10000000000 : ℝ), (2631884977/5000000000 : ℝ)] ![(13471451449759/100000000000000 : ℝ), (4397341268469/10000000000000 : ℝ), (42555135852919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-443723251/2000000000 : ℝ)|^8229 ≤ (13471451449759/100000000000000 : ℝ)^6181
        have hw : |(-443723251/2000000000 : ℝ)|=(443723251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395001233/10000000000 : ℝ)|^8229 ≤ (4397341268469/10000000000000 : ℝ)^6181
        have hw : |(5395001233/10000000000 : ℝ)|=(5395001233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631884977/5000000000 : ℝ)|^8229 ≤ (42555135852919/100000000000000 : ℝ)^6181
        have hw : |(2631884977/5000000000 : ℝ)|=(2631884977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s7_1 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345070039/10000000000 : ℝ)*x 0 + (-114260481/500000000 : ℝ)*x 1 + (328985619/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345070039/10000000000 : ℝ)^8229 ≤ (21716210178439/50000000000000 : ℝ)^6181 := by
    have hnat : (5345070039 : ℕ)^8229*50000000000000^6181 ≤ 21716210178439^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345070039 10000000000 21716210178439 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114260481/500000000 : ℝ)^8229 ≤ (7006222154363/50000000000000 : ℝ)^6181 := by
    have hnat : (114260481 : ℕ)^8229*50000000000000^6181 ≤ 7006222154363^6181*500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114260481 500000000 7006222154363 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328985619/625000000 : ℝ)^8229 ≤ (42555135314757/100000000000000 : ℝ)^6181 := by
    have hnat : (328985619 : ℕ)^8229*100000000000000^6181 ≤ 42555135314757^6181*625000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328985619 625000000 42555135314757 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345070039/10000000000 : ℝ), (-114260481/500000000 : ℝ), (328985619/625000000 : ℝ)] ![(21716210178439/50000000000000 : ℝ), (7006222154363/50000000000000 : ℝ), (42555135314757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345070039/10000000000 : ℝ)|^8229 ≤ (21716210178439/50000000000000 : ℝ)^6181
        have hw : |(5345070039/10000000000 : ℝ)|=(5345070039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-114260481/500000000 : ℝ)|^8229 ≤ (7006222154363/50000000000000 : ℝ)^6181
        have hw : |(-114260481/500000000 : ℝ)|=(114260481/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328985619/625000000 : ℝ)|^8229 ≤ (42555135314757/100000000000000 : ℝ)^6181
        have hw : |(328985619/625000000 : ℝ)|=(328985619/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s7_2 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345069773/10000000000 : ℝ)*x 0 + (131594247/250000000 : ℝ)*x 1 + (-457042001/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345069773/10000000000 : ℝ)^8229 ≤ (43432417479277/100000000000000 : ℝ)^6181 := by
    have hnat : (5345069773 : ℕ)^8229*100000000000000^6181 ≤ 43432417479277^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345069773 10000000000 43432417479277 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131594247/250000000 : ℝ)^8229 ≤ (42555135056439/100000000000000 : ℝ)^6181 := by
    have hnat : (131594247 : ℕ)^8229*100000000000000^6181 ≤ 42555135056439^6181*250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131594247 250000000 42555135056439 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (457042001/2000000000 : ℝ)^8229 ≤ (1751555931459/12500000000000 : ℝ)^6181 := by
    have hnat : (457042001 : ℕ)^8229*12500000000000^6181 ≤ 1751555931459^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457042001 2000000000 1751555931459 12500000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345069773/10000000000 : ℝ), (131594247/250000000 : ℝ), (-457042001/2000000000 : ℝ)] ![(43432417479277/100000000000000 : ℝ), (42555135056439/100000000000000 : ℝ), (1751555931459/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345069773/10000000000 : ℝ)|^8229 ≤ (43432417479277/100000000000000 : ℝ)^6181
        have hw : |(5345069773/10000000000 : ℝ)|=(5345069773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131594247/250000000 : ℝ)|^8229 ≤ (42555135056439/100000000000000 : ℝ)^6181
        have hw : |(131594247/250000000 : ℝ)|=(131594247/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-457042001/2000000000 : ℝ)|^8229 ≤ (1751555931459/12500000000000 : ℝ)^6181
        have hw : |(-457042001/2000000000 : ℝ)|=(457042001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s7_3 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (8554331/19531250 : ℝ)*x 0 + (2126944861/5000000000 : ℝ)*x 1 + (281847161/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8554331/19531250 : ℝ)^8229 ≤ (16658150384099/50000000000000 : ℝ)^6181 := by
    have hnat : (8554331 : ℕ)^8229*50000000000000^6181 ≤ 16658150384099^6181*19531250^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8554331 19531250 16658150384099 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126944861/5000000000 : ℝ)^8229 ≤ (32047120151837/100000000000000 : ℝ)^6181 := by
    have hnat : (2126944861 : ℕ)^8229*100000000000000^6181 ≤ 32047120151837^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126944861 5000000000 32047120151837 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281847161/625000000 : ℝ)^8229 ≤ (692731581191/2000000000000 : ℝ)^6181 := by
    have hnat : (281847161 : ℕ)^8229*2000000000000^6181 ≤ 692731581191^6181*625000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281847161 625000000 692731581191 2000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8554331/19531250 : ℝ), (2126944861/5000000000 : ℝ), (281847161/625000000 : ℝ)] ![(16658150384099/50000000000000 : ℝ), (32047120151837/100000000000000 : ℝ), (692731581191/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8554331/19531250 : ℝ)|^8229 ≤ (16658150384099/50000000000000 : ℝ)^6181
        have hw : |(8554331/19531250 : ℝ)|=(8554331/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2126944861/5000000000 : ℝ)|^8229 ≤ (32047120151837/100000000000000 : ℝ)^6181
        have hw : |(2126944861/5000000000 : ℝ)|=(2126944861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(281847161/625000000 : ℝ)|^8229 ≤ (692731581191/2000000000000 : ℝ)^6181
        have hw : |(281847161/625000000 : ℝ)|=(281847161/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s7_4 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1109310211/5000000000 : ℝ)*x 0 + (5264098953/10000000000 : ℝ)*x 1 + (1348667949/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1109310211/5000000000 : ℝ)^8229 ≤ (13471485135349/100000000000000 : ℝ)^6181 := by
    have hnat : (1109310211 : ℕ)^8229*100000000000000^6181 ≤ 13471485135349^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1109310211 5000000000 13471485135349 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264098953/10000000000 : ℝ)^8229 ≤ (132995865587/312500000000 : ℝ)^6181 := by
    have hnat : (5264098953 : ℕ)^8229*312500000000^6181 ≤ 132995865587^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264098953 10000000000 132995865587 312500000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348667949/2500000000 : ℝ)^8229 ≤ (43969837858567/100000000000000 : ℝ)^6181 := by
    have hnat : (1348667949 : ℕ)^8229*100000000000000^6181 ≤ 43969837858567^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348667949 2500000000 43969837858567 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1109310211/5000000000 : ℝ), (5264098953/10000000000 : ℝ), (1348667949/2500000000 : ℝ)] ![(13471485135349/100000000000000 : ℝ), (132995865587/312500000000 : ℝ), (43969837858567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1109310211/5000000000 : ℝ)|^8229 ≤ (13471485135349/100000000000000 : ℝ)^6181
        have hw : |(-1109310211/5000000000 : ℝ)|=(1109310211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264098953/10000000000 : ℝ)|^8229 ≤ (132995865587/312500000000 : ℝ)^6181
        have hw : |(5264098953/10000000000 : ℝ)|=(5264098953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348667949/2500000000 : ℝ)|^8229 ≤ (43969837858567/100000000000000 : ℝ)^6181
        have hw : |(1348667949/2500000000 : ℝ)|=(1348667949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s7_5 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312095723/10000000000 : ℝ)*x 0 + (-2154307097/10000000000 : ℝ)*x 1 + (269733583/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312095723/10000000000 : ℝ)^8229 ≤ (8615213532893/20000000000000 : ℝ)^6181 := by
    have hnat : (5312095723 : ℕ)^8229*20000000000000^6181 ≤ 8615213532893^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312095723 10000000000 8615213532893 20000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2154307097/10000000000 : ℝ)^8229 ≤ (12954095933291/100000000000000 : ℝ)^6181 := by
    have hnat : (2154307097 : ℕ)^8229*100000000000000^6181 ≤ 12954095933291^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154307097 10000000000 12954095933291 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269733583/500000000 : ℝ)^8229 ≤ (21984918191401/50000000000000 : ℝ)^6181 := by
    have hnat : (269733583 : ℕ)^8229*50000000000000^6181 ≤ 21984918191401^6181*500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269733583 500000000 21984918191401 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312095723/10000000000 : ℝ), (-2154307097/10000000000 : ℝ), (269733583/500000000 : ℝ)] ![(8615213532893/20000000000000 : ℝ), (12954095933291/100000000000000 : ℝ), (21984918191401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312095723/10000000000 : ℝ)|^8229 ≤ (8615213532893/20000000000000 : ℝ)^6181
        have hw : |(5312095723/10000000000 : ℝ)|=(5312095723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2154307097/10000000000 : ℝ)|^8229 ≤ (12954095933291/100000000000000 : ℝ)^6181
        have hw : |(-2154307097/10000000000 : ℝ)|=(2154307097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269733583/500000000 : ℝ)|^8229 ≤ (21984918191401/50000000000000 : ℝ)^6181
        have hw : |(269733583/500000000 : ℝ)|=(269733583/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s7_6 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664012049/1250000000 : ℝ)*x 0 + (5394671601/10000000000 : ℝ)*x 1 + (-86172251/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664012049/1250000000 : ℝ)^8229 ≤ (10769018721729/25000000000000 : ℝ)^6181 := by
    have hnat : (664012049 : ℕ)^8229*25000000000000^6181 ≤ 10769018721729^6181*1250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664012049 1250000000 10769018721729 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394671601/10000000000 : ℝ)^8229 ≤ (43969835742581/100000000000000 : ℝ)^6181 := by
    have hnat : (5394671601 : ℕ)^8229*100000000000000^6181 ≤ 43969835742581^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394671601 10000000000 43969835742581 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86172251/400000000 : ℝ)^8229 ≤ (647704467639/5000000000000 : ℝ)^6181 := by
    have hnat : (86172251 : ℕ)^8229*5000000000000^6181 ≤ 647704467639^6181*400000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86172251 400000000 647704467639 5000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664012049/1250000000 : ℝ), (5394671601/10000000000 : ℝ), (-86172251/400000000 : ℝ)] ![(10769018721729/25000000000000 : ℝ), (43969835742581/100000000000000 : ℝ), (647704467639/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664012049/1250000000 : ℝ)|^8229 ≤ (10769018721729/25000000000000 : ℝ)^6181
        have hw : |(664012049/1250000000 : ℝ)|=(664012049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394671601/10000000000 : ℝ)|^8229 ≤ (43969835742581/100000000000000 : ℝ)^6181
        have hw : |(5394671601/10000000000 : ℝ)|=(5394671601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86172251/400000000 : ℝ)|^8229 ≤ (647704467639/5000000000000 : ℝ)^6181
        have hw : |(-86172251/400000000 : ℝ)|=(86172251/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s7_7 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (547478609/1250000000 : ℝ)*x 0 + (901782713/2000000000 : ℝ)*x 1 + (4254531709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547478609/1250000000 : ℝ)^8229 ≤ (33316416218247/100000000000000 : ℝ)^6181 := by
    have hnat : (547478609 : ℕ)^8229*100000000000000^6181 ≤ 33316416218247^6181*1250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547478609 1250000000 33316416218247 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901782713/2000000000 : ℝ)^8229 ≤ (34630024478807/100000000000000 : ℝ)^6181 := by
    have hnat : (901782713 : ℕ)^8229*100000000000000^6181 ≤ 34630024478807^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901782713 2000000000 34630024478807 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4254531709/10000000000 : ℝ)^8229 ≤ (32053559296647/100000000000000 : ℝ)^6181 := by
    have hnat : (4254531709 : ℕ)^8229*100000000000000^6181 ≤ 32053559296647^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254531709 10000000000 32053559296647 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547478609/1250000000 : ℝ), (901782713/2000000000 : ℝ), (4254531709/10000000000 : ℝ)] ![(33316416218247/100000000000000 : ℝ), (34630024478807/100000000000000 : ℝ), (32053559296647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547478609/1250000000 : ℝ)|^8229 ≤ (33316416218247/100000000000000 : ℝ)^6181
        have hw : |(547478609/1250000000 : ℝ)|=(547478609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901782713/2000000000 : ℝ)|^8229 ≤ (34630024478807/100000000000000 : ℝ)^6181
        have hw : |(901782713/2000000000 : ℝ)|=(901782713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4254531709/10000000000 : ℝ)|^8229 ≤ (32053559296647/100000000000000 : ℝ)^6181
        have hw : |(4254531709/10000000000 : ℝ)|=(4254531709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1036_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2799/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11207/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13987/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6999/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2799/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6999/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2799/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6999/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2799/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6999/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2799/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6999/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2799/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6999/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2799/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (2799/25000 : ℝ) ^ (2057/512 : ℝ) ≤ (3023889127268611/20000000000000000000 : ℝ) := by
    have hpowers : (2799/25000 : ℝ)^2057 ≤ (3023889127268611/20000000000000000000 : ℝ)^512 := by
      have hnat : (2799 : ℕ)^2057*20000000000000000000^512 ≤ 3023889127268611^512*25000^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2799 25000 3023889127268611 20000000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2799/25000 : ℝ)) (X := (3023889127268611/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hpowhi : (6999/50000 : ℝ) ^ (2057/512 : ℝ) ≤ (18544853303922547/50000000000000000000 : ℝ) := by
    have hpowers : (6999/50000 : ℝ)^2057 ≤ (18544853303922547/50000000000000000000 : ℝ)^512 := by
      have hnat : (6999 : ℕ)^2057*50000000000000000000^512 ≤ 18544853303922547^512*50000^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6999 50000 18544853303922547 50000000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6999/50000 : ℝ)) (X := (18544853303922547/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10003023889127268611/10000000000000000000 : ℝ) ≤ (1250094072401869/1250000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (10003023889127268611/10000000000000000000 : ℝ)^512 ≤ (1250094072401869/1250000000000000 : ℝ)^2057 := by
      have hnat : (10003023889127268611 : ℕ)^512*1250000000000000^2057 ≤ 1250094072401869^2057*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003023889127268611 10000000000000000000 1250094072401869 1250000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250094072401869/1250000000000000 : ℝ)) (X := (10003023889127268611/10000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052209152244188149/100000000000000000000 : ℝ) ≤ (5000649631657399/5000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (100052209152244188149/100000000000000000000 : ℝ)^512 ≤ (5000649631657399/5000000000000000 : ℝ)^2057 := by
      have hnat : (100052209152244188149 : ℕ)^512*5000000000000000^2057 ≤ 5000649631657399^2057*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052209152244188149 100000000000000000000 5000649631657399 5000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000649631657399/5000000000000000 : ℝ)) (X := (100052209152244188149/100000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018544853303922547/25000000000000000000 : ℝ) ≤ (2500461486853661/2500000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (25018544853303922547/25000000000000000000 : ℝ)^512 ≤ (2500461486853661/2500000000000000 : ℝ)^2057 := by
      have hnat : (25018544853303922547 : ℕ)^512*2500000000000000^2057 ≤ 2500461486853661^2057*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018544853303922547 25000000000000000000 2500461486853661 2500000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500461486853661/2500000000000000 : ℝ)) (X := (25018544853303922547/25000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3023889127268611/20000000000000000000 : ℝ) ≤ ((72942362959886833/72968750000000000 : ℝ)+2*(91114016641/46700000000000 : ℝ)*(2799/25000 : ℝ))^(2057/512 : ℝ) := by
    rw [show (72942362959886833/72968750000000000 : ℝ)+2*(91114016641/46700000000000 : ℝ)*(2799/25000 : ℝ)=(1250094072401869/1250000000000000 : ℝ) by norm_num, show 1+2*(3023889127268611/20000000000000000000 : ℝ)=(10003023889127268611/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18544853303922547/50000000000000000000 : ℝ)+(3023889127268611/20000000000000000000 : ℝ) ≤ ((72942362959886833/72968750000000000 : ℝ)+(91114016641/46700000000000 : ℝ)*((6999/50000 : ℝ)+(2799/25000 : ℝ)))^(2057/512 : ℝ) := by
    rw [show (72942362959886833/72968750000000000 : ℝ)+(91114016641/46700000000000 : ℝ)*((6999/50000 : ℝ)+(2799/25000 : ℝ))=(5000649631657399/5000000000000000 : ℝ) by norm_num, show 1+(18544853303922547/50000000000000000000 : ℝ)+(3023889127268611/20000000000000000000 : ℝ)=(100052209152244188149/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18544853303922547/50000000000000000000 : ℝ) ≤ ((72942362959886833/72968750000000000 : ℝ)+2*(91114016641/46700000000000 : ℝ)*(6999/50000 : ℝ))^(2057/512 : ℝ) := by
    rw [show (72942362959886833/72968750000000000 : ℝ)+2*(91114016641/46700000000000 : ℝ)*(6999/50000 : ℝ)=(2500461486853661/2500000000000000 : ℝ) by norm_num, show 1+2*(18544853303922547/50000000000000000000 : ℝ)=(25018544853303922547/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (72942362959886833/72968750000000000 : ℝ)*(X 1 0+X 2 0)+(91114016641/46700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (2799/25000 : ℝ)) (hi := (6999/50000 : ℝ)) (c := (72942362959886833/72968750000000000 : ℝ)) (alpha := (91114016641/46700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (72942362959886833/72968750000000000 : ℝ)*(X 0 1+X 2 1)+(91114016641/46700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (2799/25000 : ℝ)) (hi := (6999/50000 : ℝ)) (c := (72942362959886833/72968750000000000 : ℝ)) (alpha := (91114016641/46700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (72942362959886833/72968750000000000 : ℝ)*(X 0 2+X 1 2)+(91114016641/46700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (2799/25000 : ℝ)) (hi := (6999/50000 : ℝ)) (c := (72942362959886833/72968750000000000 : ℝ)) (alpha := (91114016641/46700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-443723251/2000000000 : ℝ)*X 0 0+(5395001233/10000000000 : ℝ)*X 0 1+(2631884977/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345070039/10000000000 : ℝ)*X 1 0+(-114260481/500000000 : ℝ)*X 1 1+(328985619/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345069773/10000000000 : ℝ)*X 2 0+(131594247/250000000 : ℝ)*X 2 1+(-457042001/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((8554331/19531250 : ℝ)*X 0 0+(2126944861/5000000000 : ℝ)*X 0 1+(281847161/625000000 : ℝ)*X 0 2+(8554331/19531250 : ℝ)*X 1 0+(2126944861/5000000000 : ℝ)*X 1 1+(281847161/625000000 : ℝ)*X 1 2+(8554331/19531250 : ℝ)*X 2 0+(2126944861/5000000000 : ℝ)*X 2 1+(281847161/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1109310211/5000000000 : ℝ)*X 0 0+(5264098953/10000000000 : ℝ)*X 0 1+(1348667949/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312095723/10000000000 : ℝ)*X 1 0+(-2154307097/10000000000 : ℝ)*X 1 1+(269733583/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664012049/1250000000 : ℝ)*X 2 0+(5394671601/10000000000 : ℝ)*X 2 1+(-86172251/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((547478609/1250000000 : ℝ)*X 0 0+(901782713/2000000000 : ℝ)*X 0 1+(4254531709/10000000000 : ℝ)*X 0 2+(547478609/1250000000 : ℝ)*X 1 0+(901782713/2000000000 : ℝ)*X 1 1+(4254531709/10000000000 : ℝ)*X 1 2+(547478609/1250000000 : ℝ)*X 2 0+(901782713/2000000000 : ℝ)*X 2 1+(4254531709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52118273945237969004704523/7296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1099068151/100000000000000 : ℝ)*(base21) + (229484499/100000000000000 : ℝ)*(upper2) + (3188657/3125000000000 : ℝ)*(upper3) + (220067349/50000000000000 : ℝ)*(upper4) + (300489591/100000000000000 : ℝ)*(upper5) + (2882867167685831/50000000000000 : ℝ)*(major0) + (2882867167685831/50000000000000 : ℝ)*(major1) + (2882867167685831/50000000000000 : ℝ)*(major2) + (7620103652091801/100000000000000 : ℝ)*(sp0) + (1524018589308167/20000000000000 : ℝ)*(sp1) + (7620062046283543/100000000000000 : ℝ)*(sp2) + (3911364780566607/100000000000000 : ℝ)*(sp3) + (5352775483/50000000000000 : ℝ)*(sp5) + (40506740107/100000000000000 : ℝ)*(sp6) + (3911364780566607/100000000000000 : ℝ)*(f.failure) + (7620103652091801/100000000000000 : ℝ)*(f.sum) + (23036099974073/2335000000000000000000000000 : ℝ)*base66 + (13451889111223799/1824218750000000000000000000000 : ℝ)*base67 + (26820159853754571/7296875000000000000000000000000 : ℝ)*base69 + (68704712087005049/1824218750000000000000000000000 : ℝ)*base71 + (2986359976039/1167500000000000000000000000 : ℝ)*base74 + (42929425214973321/7296875000000000000000000000000 : ℝ)*base75 + (1002143339173197/228027343750000000000000000000 : ℝ)*base78 + (10560618808088223/3648437500000000000000000000000 : ℝ)*base79 + (4148080430739/1167500000000000000000000000 : ℝ)*base82 + (45083719/10000000000000000000000 : ℝ)*base90 + (45083719/10000000000000000000000 : ℝ)*base92 + (45083719/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (68186038073911397234175021/7296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (786174981/100000000000000 : ℝ)*(base19) + (3519224497/100000000000000 : ℝ)*(base23) + (20546483/12500000000000 : ℝ)*(upper3) + (126631211/20000000000000 : ℝ)*(lower4) + (81619633/100000000000000 : ℝ)*(upper5) + (5794827927218073/100000000000000 : ℝ)*(major0) + (5794827927218073/100000000000000 : ℝ)*(major1) + (5794827927218073/100000000000000 : ℝ)*(major2) + (3572572039/50000000000000 : ℝ)*(sp1) + (100041179253/100000000000000 : ℝ)*(sp2) + (7658554221664859/100000000000000 : ℝ)*(sp4) + (7658546290345799/100000000000000 : ℝ)*(sp5) + (7658450661261109/100000000000000 : ℝ)*(sp6) + (491387665160771/12500000000000 : ℝ)*(sp7) + (491387665160771/12500000000000 : ℝ)*(f.failure) + (7658554221664859/100000000000000 : ℝ)*(f.sum) + (2282404137463/2335000000000000000000000000 : ℝ)*base65 + (71568843585612493/14593750000000000000000000000000 : ℝ)*base67 + (34114078465731257/14593750000000000000000000000000 : ℝ)*base70 + (182452481993237493/14593750000000000000000000000000 : ℝ)*base71 + (10156825092651/1167500000000000000000000000 : ℝ)*base74 + (53828324750018743/14593750000000000000000000000000 : ℝ)*base75 + (21062512714299993/14593750000000000000000000000000 : ℝ)*base77 + (118318792907325007/14593750000000000000000000000000 : ℝ)*base80 + (9788200608327/2335000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (722693/1250000000000000000000 : ℝ)*base89 + (722693/1250000000000000000000 : ℝ)*base91 + (722693/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1036_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6999/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2799/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1036_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1036_s8_0 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2218623293/10000000000 : ℝ)*x 0 + (2697441227/5000000000 : ℝ)*x 1 + (5263884419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2218623293/10000000000 : ℝ)^8229 ≤ (13471508344223/100000000000000 : ℝ)^6181 := by
    have hnat : (2218623293 : ℕ)^8229*100000000000000^6181 ≤ 13471508344223^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218623293 10000000000 13471508344223 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697441227/5000000000 : ℝ)^8229 ≤ (1099303094187/2500000000000 : ℝ)^6181 := by
    have hnat : (2697441227 : ℕ)^8229*2500000000000^6181 ≤ 1099303094187^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697441227 5000000000 1099303094187 2500000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263884419/10000000000 : ℝ)^8229 ≤ (2659772992043/6250000000000 : ℝ)^6181 := by
    have hnat : (5263884419 : ℕ)^8229*6250000000000^6181 ≤ 2659772992043^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263884419 10000000000 2659772992043 6250000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2218623293/10000000000 : ℝ), (2697441227/5000000000 : ℝ), (5263884419/10000000000 : ℝ)] ![(13471508344223/100000000000000 : ℝ), (1099303094187/2500000000000 : ℝ), (2659772992043/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2218623293/10000000000 : ℝ)|^8229 ≤ (13471508344223/100000000000000 : ℝ)^6181
        have hw : |(-2218623293/10000000000 : ℝ)|=(2218623293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697441227/5000000000 : ℝ)|^8229 ≤ (1099303094187/2500000000000 : ℝ)^6181
        have hw : |(2697441227/5000000000 : ℝ)|=(2697441227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263884419/10000000000 : ℝ)|^8229 ≤ (2659772992043/6250000000000 : ℝ)^6181
        have hw : |(5263884419/10000000000 : ℝ)|=(5263884419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s8_1 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672521053/5000000000 : ℝ)*x 0 + (-3570463/15625000 : ℝ)*x 1 + (657985489/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672521053/5000000000 : ℝ)^8229 ≤ (10858029544143/25000000000000 : ℝ)^6181 := by
    have hnat : (2672521053 : ℕ)^8229*25000000000000^6181 ≤ 10858029544143^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672521053 5000000000 10858029544143 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3570463/15625000 : ℝ)^8229 ≤ (14011519392247/100000000000000 : ℝ)^6181 := by
    have hnat : (3570463 : ℕ)^8229*100000000000000^6181 ≤ 14011519392247^6181*15625000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3570463 15625000 14011519392247 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657985489/1250000000 : ℝ)^8229 ≤ (42556362415681/100000000000000 : ℝ)^6181 := by
    have hnat : (657985489 : ℕ)^8229*100000000000000^6181 ≤ 42556362415681^6181*1250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657985489 1250000000 42556362415681 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672521053/5000000000 : ℝ), (-3570463/15625000 : ℝ), (657985489/1250000000 : ℝ)] ![(10858029544143/25000000000000 : ℝ), (14011519392247/100000000000000 : ℝ), (42556362415681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672521053/5000000000 : ℝ)|^8229 ≤ (10858029544143/25000000000000 : ℝ)^6181
        have hw : |(2672521053/5000000000 : ℝ)|=(2672521053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3570463/15625000 : ℝ)|^8229 ≤ (14011519392247/100000000000000 : ℝ)^6181
        have hw : |(-3570463/15625000 : ℝ)|=(3570463/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657985489/1250000000 : ℝ)|^8229 ≤ (42556362415681/100000000000000 : ℝ)^6181
        have hw : |(657985489/1250000000 : ℝ)|=(657985489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s8_2 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345042091/10000000000 : ℝ)*x 0 + (5263883161/10000000000 : ℝ)*x 1 + (-2285097331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345042091/10000000000 : ℝ)^8229 ≤ (21716059007151/50000000000000 : ℝ)^6181 := by
    have hnat : (5345042091 : ℕ)^8229*50000000000000^6181 ≤ 21716059007151^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345042091 10000000000 21716059007151 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263883161/10000000000 : ℝ)^8229 ≤ (42556354332423/100000000000000 : ℝ)^6181 := by
    have hnat : (5263883161 : ℕ)^8229*100000000000000^6181 ≤ 42556354332423^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263883161 10000000000 42556354332423 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2285097331/10000000000 : ℝ)^8229 ≤ (7005763822703/50000000000000 : ℝ)^6181 := by
    have hnat : (2285097331 : ℕ)^8229*50000000000000^6181 ≤ 7005763822703^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285097331 10000000000 7005763822703 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345042091/10000000000 : ℝ), (5263883161/10000000000 : ℝ), (-2285097331/10000000000 : ℝ)] ![(21716059007151/50000000000000 : ℝ), (42556354332423/100000000000000 : ℝ), (7005763822703/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345042091/10000000000 : ℝ)|^8229 ≤ (21716059007151/50000000000000 : ℝ)^6181
        have hw : |(5345042091/10000000000 : ℝ)|=(5345042091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263883161/10000000000 : ℝ)|^8229 ≤ (42556354332423/100000000000000 : ℝ)^6181
        have hw : |(5263883161/10000000000 : ℝ)|=(5263883161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2285097331/10000000000 : ℝ)|^8229 ≤ (7005763822703/50000000000000 : ℝ)^6181
        have hw : |(-2285097331/10000000000 : ℝ)|=(2285097331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s8_3 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4379825159/10000000000 : ℝ)*x 0 + (4254114833/10000000000 : ℝ)*x 1 + (56366577/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379825159/10000000000 : ℝ)^8229 ≤ (2082273663497/6250000000000 : ℝ)^6181 := by
    have hnat : (4379825159 : ℕ)^8229*6250000000000^6181 ≤ 2082273663497^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379825159 10000000000 2082273663497 6250000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4254114833/10000000000 : ℝ)^8229 ≤ (16024688991921/50000000000000 : ℝ)^6181 := by
    have hnat : (4254114833 : ℕ)^8229*50000000000000^6181 ≤ 16024688991921^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254114833 10000000000 16024688991921 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56366577/125000000 : ℝ)^8229 ≤ (34634243383859/100000000000000 : ℝ)^6181 := by
    have hnat : (56366577 : ℕ)^8229*100000000000000^6181 ≤ 34634243383859^6181*125000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56366577 125000000 34634243383859 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379825159/10000000000 : ℝ), (4254114833/10000000000 : ℝ), (56366577/125000000 : ℝ)] ![(2082273663497/6250000000000 : ℝ), (16024688991921/50000000000000 : ℝ), (34634243383859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379825159/10000000000 : ℝ)|^8229 ≤ (2082273663497/6250000000000 : ℝ)^6181
        have hw : |(4379825159/10000000000 : ℝ)|=(4379825159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4254114833/10000000000 : ℝ)|^8229 ≤ (16024688991921/50000000000000 : ℝ)^6181
        have hw : |(4254114833/10000000000 : ℝ)|=(4254114833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56366577/125000000 : ℝ)|^8229 ≤ (34634243383859/100000000000000 : ℝ)^6181
        have hw : |(56366577/125000000 : ℝ)|=(56366577/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s8_4 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2218629679/10000000000 : ℝ)*x 0 + (1052842311/2000000000 : ℝ)*x 1 + (674319151/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2218629679/10000000000 : ℝ)^8229 ≤ (6735779984019/50000000000000 : ℝ)^6181 := by
    have hnat : (2218629679 : ℕ)^8229*50000000000000^6181 ≤ 6735779984019^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218629679 10000000000 6735779984019 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052842311/2000000000 : ℝ)^8229 ≤ (4255988898063/10000000000000 : ℝ)^6181 := by
    have hnat : (1052842311 : ℕ)^8229*10000000000000^6181 ≤ 4255988898063^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052842311 2000000000 4255988898063 10000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674319151/1250000000 : ℝ)^8229 ≤ (21984275520001/50000000000000 : ℝ)^6181 := by
    have hnat : (674319151 : ℕ)^8229*50000000000000^6181 ≤ 21984275520001^6181*1250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674319151 1250000000 21984275520001 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2218629679/10000000000 : ℝ), (1052842311/2000000000 : ℝ), (674319151/1250000000 : ℝ)] ![(6735779984019/50000000000000 : ℝ), (4255988898063/10000000000000 : ℝ), (21984275520001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2218629679/10000000000 : ℝ)|^8229 ≤ (6735779984019/50000000000000 : ℝ)^6181
        have hw : |(-2218629679/10000000000 : ℝ)|=(2218629679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052842311/2000000000 : ℝ)|^8229 ≤ (4255988898063/10000000000000 : ℝ)^6181
        have hw : |(1052842311/2000000000 : ℝ)|=(1052842311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674319151/1250000000 : ℝ)|^8229 ≤ (21984275520001/50000000000000 : ℝ)^6181
        have hw : |(674319151/1250000000 : ℝ)|=(674319151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s8_5 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664015651/1250000000 : ℝ)*x 0 + (-538606971/2500000000 : ℝ)*x 1 + (2697276607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664015651/1250000000 : ℝ)^8229 ≤ (21538192990797/50000000000000 : ℝ)^6181 := by
    have hnat : (664015651 : ℕ)^8229*50000000000000^6181 ≤ 21538192990797^6181*1250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664015651 1250000000 21538192990797 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538606971/2500000000 : ℝ)^8229 ≤ (6477531450581/50000000000000 : ℝ)^6181 := by
    have hnat : (538606971 : ℕ)^8229*50000000000000^6181 ≤ 6477531450581^6181*2500000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538606971 2500000000 6477531450581 50000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697276607/5000000000 : ℝ)^8229 ≤ (10992137776277/25000000000000 : ℝ)^6181 := by
    have hnat : (2697276607 : ℕ)^8229*25000000000000^6181 ≤ 10992137776277^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697276607 5000000000 10992137776277 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664015651/1250000000 : ℝ), (-538606971/2500000000 : ℝ), (2697276607/5000000000 : ℝ)] ![(21538192990797/50000000000000 : ℝ), (6477531450581/50000000000000 : ℝ), (10992137776277/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664015651/1250000000 : ℝ)|^8229 ≤ (21538192990797/50000000000000 : ℝ)^6181
        have hw : |(664015651/1250000000 : ℝ)|=(664015651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-538606971/2500000000 : ℝ)|^8229 ≤ (6477531450581/50000000000000 : ℝ)^6181
        have hw : |(-538606971/2500000000 : ℝ)|=(538606971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697276607/5000000000 : ℝ)|^8229 ≤ (10992137776277/25000000000000 : ℝ)^6181
        have hw : |(2697276607/5000000000 : ℝ)|=(2697276607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s8_6 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656062609/5000000000 : ℝ)*x 0 + (2697276603/5000000000 : ℝ)*x 1 + (-2154427881/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656062609/5000000000 : ℝ)^8229 ≤ (43076386089553/100000000000000 : ℝ)^6181 := by
    have hnat : (2656062609 : ℕ)^8229*100000000000000^6181 ≤ 43076386089553^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656062609 5000000000 43076386089553 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697276603/5000000000 : ℝ)^8229 ≤ (43968551018299/100000000000000 : ℝ)^6181 := by
    have hnat : (2697276603 : ℕ)^8229*100000000000000^6181 ≤ 43968551018299^6181*5000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697276603 5000000000 43968551018299 100000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2154427881/10000000000 : ℝ)^8229 ≤ (2591012575429/20000000000000 : ℝ)^6181 := by
    have hnat : (2154427881 : ℕ)^8229*20000000000000^6181 ≤ 2591012575429^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154427881 10000000000 2591012575429 20000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656062609/5000000000 : ℝ), (2697276603/5000000000 : ℝ), (-2154427881/10000000000 : ℝ)] ![(43076386089553/100000000000000 : ℝ), (43968551018299/100000000000000 : ℝ), (2591012575429/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656062609/5000000000 : ℝ)|^8229 ≤ (43076386089553/100000000000000 : ℝ)^6181
        have hw : |(2656062609/5000000000 : ℝ)|=(2656062609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697276603/5000000000 : ℝ)|^8229 ≤ (43968551018299/100000000000000 : ℝ)^6181
        have hw : |(2697276603/5000000000 : ℝ)|=(2697276603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2154427881/10000000000 : ℝ)|^8229 ≤ (2591012575429/20000000000000 : ℝ)^6181
        have hw : |(-2154427881/10000000000 : ℝ)|=(2154427881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1036_s8_7 (p : ℝ) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (109495857/250000000 : ℝ)*x 0 + (4508687613/10000000000 : ℝ)*x 1 + (850951317/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109495857/250000000 : ℝ)^8229 ≤ (8329117746541/25000000000000 : ℝ)^6181 := by
    have hnat : (109495857 : ℕ)^8229*25000000000000^6181 ≤ 8329117746541^6181*250000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109495857 250000000 8329117746541 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4508687613/10000000000 : ℝ)^8229 ≤ (8656928526863/25000000000000 : ℝ)^6181 := by
    have hnat : (4508687613 : ℕ)^8229*25000000000000^6181 ≤ 8656928526863^6181*10000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508687613 10000000000 8656928526863 25000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850951317/2000000000 : ℝ)^8229 ≤ (3205581488439/10000000000000 : ℝ)^6181 := by
    have hnat : (850951317 : ℕ)^8229*10000000000000^6181 ≤ 3205581488439^6181*2000000000^8229 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850951317 2000000000 3205581488439 10000000000000 8229 6181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8229/2048 : ℝ)) 8229 6181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109495857/250000000 : ℝ), (4508687613/10000000000 : ℝ), (850951317/2000000000 : ℝ)] ![(8329117746541/25000000000000 : ℝ), (8656928526863/25000000000000 : ℝ), (3205581488439/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109495857/250000000 : ℝ)|^8229 ≤ (8329117746541/25000000000000 : ℝ)^6181
        have hw : |(109495857/250000000 : ℝ)|=(109495857/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4508687613/10000000000 : ℝ)|^8229 ≤ (8656928526863/25000000000000 : ℝ)^6181
        have hw : |(4508687613/10000000000 : ℝ)|=(4508687613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(850951317/2000000000 : ℝ)|^8229 ≤ (3205581488439/10000000000000 : ℝ)^6181
        have hw : |(850951317/2000000000 : ℝ)|=(850951317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1036_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11209/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (437/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13987/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11207/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13987/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11207/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13987/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11207/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11207/100000 : ℝ) ^ (2057/512 : ℝ) ≤ (75896071626573/500000000000000000 : ℝ) := by
    have hpowers : (11207/100000 : ℝ)^2057 ≤ (75896071626573/500000000000000000 : ℝ)^512 := by
      have hnat : (11207 : ℕ)^2057*500000000000000000^512 ≤ 75896071626573^512*100000^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11207 100000 75896071626573 500000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11207/100000 : ℝ)) (X := (75896071626573/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hpowhi : (13987/100000 : ℝ) ^ (2057/512 : ℝ) ≤ (9243187183024373/25000000000000000000 : ℝ) := by
    have hpowers : (13987/100000 : ℝ)^2057 ≤ (9243187183024373/25000000000000000000 : ℝ)^512 := by
      have hnat : (13987 : ℕ)^2057*25000000000000000000^512 ≤ 9243187183024373^512*100000^2057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13987 100000 9243187183024373 25000000000000000000 2057 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13987/100000 : ℝ)) (X := (9243187183024373/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (250075896071626573/250000000000000000 : ℝ) ≤ (2000151110779433/2000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (250075896071626573/250000000000000000 : ℝ)^512 ≤ (2000151110779433/2000000000000000 : ℝ)^2057 := by
      have hnat : (250075896071626573 : ℕ)^512*2000000000000000^2057 ≤ 2000151110779433^2057*250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250075896071626573 250000000000000000 2000151110779433 2000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000151110779433/2000000000000000 : ℝ)) (X := (250075896071626573/250000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25013037990764353023/25000000000000000000 : ℝ) ≤ (10001297840398271/10000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (25013037990764353023/25000000000000000000 : ℝ)^512 ≤ (10001297840398271/10000000000000000 : ℝ)^2057 := by
      have hnat : (25013037990764353023 : ℕ)^512*10000000000000000^2057 ≤ 10001297840398271^2057*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013037990764353023 25000000000000000000 10001297840398271 10000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001297840398271/10000000000000000 : ℝ)) (X := (25013037990764353023/25000000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509243187183024373/12500000000000000000 : ℝ) ≤ (10001840126899377/10000000000000000 : ℝ) ^ (2057/512 : ℝ) := by
    have hpowers : (12509243187183024373/12500000000000000000 : ℝ)^512 ≤ (10001840126899377/10000000000000000 : ℝ)^2057 := by
      have hnat : (12509243187183024373 : ℕ)^512*10000000000000000^2057 ≤ 10001840126899377^2057*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509243187183024373 12500000000000000000 10001840126899377 10000000000000000 512 2057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001840126899377/10000000000000000 : ℝ)) (X := (12509243187183024373/12500000000000000000 : ℝ)) (by norm_num) 2057 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(75896071626573/500000000000000000 : ℝ) ≤ ((1736871601887395551/1737500000000000000 : ℝ)+2*(271143250553/139000000000000 : ℝ)*(11207/100000 : ℝ))^(2057/512 : ℝ) := by
    rw [show (1736871601887395551/1737500000000000000 : ℝ)+2*(271143250553/139000000000000 : ℝ)*(11207/100000 : ℝ)=(2000151110779433/2000000000000000 : ℝ) by norm_num, show 1+2*(75896071626573/500000000000000000 : ℝ)=(250075896071626573/250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9243187183024373/25000000000000000000 : ℝ)+(75896071626573/500000000000000000 : ℝ) ≤ ((1736871601887395551/1737500000000000000 : ℝ)+(271143250553/139000000000000 : ℝ)*((13987/100000 : ℝ)+(11207/100000 : ℝ)))^(2057/512 : ℝ) := by
    rw [show (1736871601887395551/1737500000000000000 : ℝ)+(271143250553/139000000000000 : ℝ)*((13987/100000 : ℝ)+(11207/100000 : ℝ))=(10001297840398271/10000000000000000 : ℝ) by norm_num, show 1+(9243187183024373/25000000000000000000 : ℝ)+(75896071626573/500000000000000000 : ℝ)=(25013037990764353023/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9243187183024373/25000000000000000000 : ℝ) ≤ ((1736871601887395551/1737500000000000000 : ℝ)+2*(271143250553/139000000000000 : ℝ)*(13987/100000 : ℝ))^(2057/512 : ℝ) := by
    rw [show (1736871601887395551/1737500000000000000 : ℝ)+2*(271143250553/139000000000000 : ℝ)*(13987/100000 : ℝ)=(10001840126899377/10000000000000000 : ℝ) by norm_num, show 1+2*(9243187183024373/25000000000000000000 : ℝ)=(12509243187183024373/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1736871601887395551/1737500000000000000 : ℝ)*(X 1 0+X 2 0)+(271143250553/139000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (13987/100000 : ℝ)) (c := (1736871601887395551/1737500000000000000 : ℝ)) (alpha := (271143250553/139000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1736871601887395551/1737500000000000000 : ℝ)*(X 0 1+X 2 1)+(271143250553/139000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (13987/100000 : ℝ)) (c := (1736871601887395551/1737500000000000000 : ℝ)) (alpha := (271143250553/139000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1736871601887395551/1737500000000000000 : ℝ)*(X 0 2+X 1 2)+(271143250553/139000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2057/512 : ℝ)) (lo := (11207/100000 : ℝ)) (hi := (13987/100000 : ℝ)) (c := (1736871601887395551/1737500000000000000 : ℝ)) (alpha := (271143250553/139000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2218623293/10000000000 : ℝ)*X 0 0+(2697441227/5000000000 : ℝ)*X 0 1+(5263884419/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672521053/5000000000 : ℝ)*X 1 0+(-3570463/15625000 : ℝ)*X 1 1+(657985489/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345042091/10000000000 : ℝ)*X 2 0+(5263883161/10000000000 : ℝ)*X 2 1+(-2285097331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4379825159/10000000000 : ℝ)*X 0 0+(4254114833/10000000000 : ℝ)*X 0 1+(56366577/125000000 : ℝ)*X 0 2+(4379825159/10000000000 : ℝ)*X 1 0+(4254114833/10000000000 : ℝ)*X 1 1+(56366577/125000000 : ℝ)*X 1 2+(4379825159/10000000000 : ℝ)*X 2 0+(4254114833/10000000000 : ℝ)*X 2 1+(56366577/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2218629679/10000000000 : ℝ)*X 0 0+(1052842311/2000000000 : ℝ)*X 0 1+(674319151/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664015651/1250000000 : ℝ)*X 1 0+(-538606971/2500000000 : ℝ)*X 1 1+(2697276607/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656062609/5000000000 : ℝ)*X 2 0+(2697276603/5000000000 : ℝ)*X 2 1+(-2154427881/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((109495857/250000000 : ℝ)*X 0 0+(4508687613/10000000000 : ℝ)*X 0 1+(850951317/2000000000 : ℝ)*X 0 2+(109495857/250000000 : ℝ)*X 1 0+(4508687613/10000000000 : ℝ)*X 1 1+(850951317/2000000000 : ℝ)*X 1 2+(109495857/250000000 : ℝ)*X 2 0+(4508687613/10000000000 : ℝ)*X 2 1+(850951317/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1036_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1336756574101517821911/173750000000000000000000000 : ℝ) := by norm_num
    linear_combination (639173477/50000000000000 : ℝ)*(base19) + (1525803477/50000000000000 : ℝ)*(base23) + (1554309/800000000000 : ℝ)*(lower2) + (1153554219/100000000000000 : ℝ)*(lower4) + (116862699/50000000000000 : ℝ)*(lower5) + (36100486596227/625000000000 : ℝ)*(major0) + (36100486596227/625000000000 : ℝ)*(major1) + (36100486596227/625000000000 : ℝ)*(major2) + (954219638929739/12500000000000 : ℝ)*(sp0) + (3816886273844271/50000000000000 : ℝ)*(sp1) + (3816885387214271/50000000000000 : ℝ)*(sp2) + (783670807898189/20000000000000 : ℝ)*(sp3) + (3342919517/20000000000000 : ℝ)*(sp4) + (27588814091/100000000000000 : ℝ)*(sp7) + (979595407076259/25000000000000 : ℝ)*(f.failure) + (7633773826035497/100000000000000 : ℝ)*(f.sum) + (473164589973/86875000000000000000000000 : ℝ)*base66 + (4304820216118471/2171875000000000000000000000000 : ℝ)*base68 + (13621784881881529/2171875000000000000000000000000 : ℝ)*base69 + (8591249034756529/2171875000000000000000000000000 : ℝ)*base71 + (45567242827/21718750000000000000000000 : ℝ)*base74 + (18450381195368471/2171875000000000000000000000000 : ℝ)*base76 + (20724745495399721/2171875000000000000000000000000 : ℝ)*base78 + (1269904533686363/271484375000000000000000000000 : ℝ)*base79 + (419378711439/695000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3641797/2500000000000000000000 : ℝ)*base89 + (3641797/2500000000000000000000 : ℝ)*base91 + (3641797/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (241619497047998607382550619/43437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (105332429/10000000000000 : ℝ)*(base19) + (227319353/20000000000000 : ℝ)*(base23) + (365205207/100000000000000 : ℝ)*(lower1) + (62250473/50000000000000 : ℝ)*(upper3) + (31045443/100000000000000 : ℝ)*(lower4) + (65254437/50000000000000 : ℝ)*(upper5) + (2902544728515777/50000000000000 : ℝ)*(major0) + (2902544728515777/50000000000000 : ℝ)*(major1) + (2902544728515777/50000000000000 : ℝ)*(major2) + (1676296281/100000000000000 : ℝ)*(sp2) + (3836058090113351/50000000000000 : ℝ)*(sp4) + (1918028781725603/25000000000000 : ℝ)*(sp5) + (7672113367333657/100000000000000 : ℝ)*(sp6) + (984515637105231/25000000000000 : ℝ)*(sp7) + (984515637105231/25000000000000 : ℝ)*(f.failure) + (3836058090113351/50000000000000 : ℝ)*(f.sum) + (7639552090769/3475000000000000000000000000 : ℝ)*base66 + (2776154381865370627/86875000000000000000000000000000 : ℝ)*base67 + (315690315474120627/86875000000000000000000000000000 : ℝ)*base69 + (18130092610136620627/86875000000000000000000000000000 : ℝ)*base71 + (4130400284219/3475000000000000000000000000 : ℝ)*base74 + (11245425502730879373/86875000000000000000000000000000 : ℝ)*base76 + (411030766362245627/86875000000000000000000000000000 : ℝ)*base77 + (1068580142664004373/86875000000000000000000000000000 : ℝ)*base80 + (6284836675481/3475000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (125127/2500000000000000000000 : ℝ)*base90 + (125127/2500000000000000000000 : ℝ)*base92 + (125127/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1036_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13987/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11207/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (437/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1036_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1036_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11149/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (437/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1036_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1036_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1036_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2057/512 : ℝ) ≤ p) (hpb : p ≤ (8229/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147409783/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14047/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11149/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11209/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (437/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1036_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1463_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:08:38.983818+00:00
-- url     : https://prove2.me/submissions/71af0630-018e-4809-8100-4bd2ef74686e

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
theorem support_rectangle_w1463_s6_0 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-485968879/2500000000 : ℝ)*x 0 + (5406465641/10000000000 : ℝ)*x 1 + (5247616521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (485968879/2500000000 : ℝ)^4423 ≤ (5933884640479/50000000000000 : ℝ)^3399 := by
    have hnat : (485968879 : ℕ)^4423*50000000000000^3399 ≤ 5933884640479^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485968879 2500000000 5933884640479 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406465641/10000000000 : ℝ)^4423 ≤ (22460509337351/50000000000000 : ℝ)^3399 := by
    have hnat : (5406465641 : ℕ)^4423*50000000000000^3399 ≤ 22460509337351^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406465641 10000000000 22460509337351 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247616521/10000000000 : ℝ)^4423 ≤ (43211212039773/100000000000000 : ℝ)^3399 := by
    have hnat : (5247616521 : ℕ)^4423*100000000000000^3399 ≤ 43211212039773^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247616521 10000000000 43211212039773 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-485968879/2500000000 : ℝ), (5406465641/10000000000 : ℝ), (5247616521/10000000000 : ℝ)] ![(5933884640479/50000000000000 : ℝ), (22460509337351/50000000000000 : ℝ), (43211212039773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-485968879/2500000000 : ℝ)|^4423 ≤ (5933884640479/50000000000000 : ℝ)^3399
        have hw : |(-485968879/2500000000 : ℝ)|=(485968879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406465641/10000000000 : ℝ)|^4423 ≤ (22460509337351/50000000000000 : ℝ)^3399
        have hw : |(5406465641/10000000000 : ℝ)|=(5406465641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247616521/10000000000 : ℝ)|^4423 ≤ (43211212039773/100000000000000 : ℝ)^3399
        have hw : |(5247616521/10000000000 : ℝ)|=(5247616521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s6_1 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673294439/5000000000 : ℝ)*x 0 + (-2024725609/10000000000 : ℝ)*x 1 + (1049523293/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673294439/5000000000 : ℝ)^4423 ≤ (69179250069/156250000000 : ℝ)^3399 := by
    have hnat : (2673294439 : ℕ)^4423*156250000000^3399 ≤ 69179250069^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673294439 5000000000 69179250069 156250000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2024725609/10000000000 : ℝ)^4423 ≤ (2502813699489/20000000000000 : ℝ)^3399 := by
    have hnat : (2024725609 : ℕ)^4423*20000000000000^3399 ≤ 2502813699489^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024725609 10000000000 2502813699489 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049523293/2000000000 : ℝ)^4423 ≤ (21605605719861/50000000000000 : ℝ)^3399 := by
    have hnat : (1049523293 : ℕ)^4423*50000000000000^3399 ≤ 21605605719861^3399*2000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049523293 2000000000 21605605719861 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673294439/5000000000 : ℝ), (-2024725609/10000000000 : ℝ), (1049523293/2000000000 : ℝ)] ![(69179250069/156250000000 : ℝ), (2502813699489/20000000000000 : ℝ), (21605605719861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673294439/5000000000 : ℝ)|^4423 ≤ (69179250069/156250000000 : ℝ)^3399
        have hw : |(2673294439/5000000000 : ℝ)|=(2673294439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2024725609/10000000000 : ℝ)|^4423 ≤ (2502813699489/20000000000000 : ℝ)^3399
        have hw : |(-2024725609/10000000000 : ℝ)|=(2024725609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049523293/2000000000 : ℝ)|^4423 ≤ (21605605719861/50000000000000 : ℝ)^3399
        have hw : |(1049523293/2000000000 : ℝ)|=(1049523293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s6_2 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336647267/2500000000 : ℝ)*x 0 + (262380811/500000000 : ℝ)*x 1 + (-2024725681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336647267/2500000000 : ℝ)^4423 ≤ (44274722091539/100000000000000 : ℝ)^3399 := by
    have hnat : (1336647267 : ℕ)^4423*100000000000000^3399 ≤ 44274722091539^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336647267 2500000000 44274722091539 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262380811/500000000 : ℝ)^4423 ≤ (43211208814499/100000000000000 : ℝ)^3399 := by
    have hnat : (262380811 : ℕ)^4423*100000000000000^3399 ≤ 43211208814499^3399*500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262380811 500000000 43211208814499 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2024725681/10000000000 : ℝ)^4423 ≤ (6257034538257/50000000000000 : ℝ)^3399 := by
    have hnat : (2024725681 : ℕ)^4423*50000000000000^3399 ≤ 6257034538257^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024725681 10000000000 6257034538257 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336647267/2500000000 : ℝ), (262380811/500000000 : ℝ), (-2024725681/10000000000 : ℝ)] ![(44274722091539/100000000000000 : ℝ), (43211208814499/100000000000000 : ℝ), (6257034538257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336647267/2500000000 : ℝ)|^4423 ≤ (44274722091539/100000000000000 : ℝ)^3399
        have hw : |(1336647267/2500000000 : ℝ)|=(1336647267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262380811/500000000 : ℝ)|^4423 ≤ (43211208814499/100000000000000 : ℝ)^3399
        have hw : |(262380811/500000000 : ℝ)|=(262380811/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2024725681/10000000000 : ℝ)|^4423 ≤ (6257034538257/50000000000000 : ℝ)^3399
        have hw : |(-2024725681/10000000000 : ℝ)|=(2024725681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s6_3 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (536993061/1250000000 : ℝ)*x 0 + (206255059/500000000 : ℝ)*x 1 + (4473031527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536993061/1250000000 : ℝ)^4423 ≤ (33305200280779/100000000000000 : ℝ)^3399 := by
    have hnat : (536993061 : ℕ)^4423*100000000000000^3399 ≤ 33305200280779^3399*1250000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536993061 1250000000 33305200280779 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206255059/500000000 : ℝ)^4423 ≤ (15796049502169/50000000000000 : ℝ)^3399 := by
    have hnat : (206255059 : ℕ)^4423*50000000000000^3399 ≤ 15796049502169^3399*500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206255059 500000000 15796049502169 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4473031527/10000000000 : ℝ)^4423 ≤ (1096959397083/3125000000000 : ℝ)^3399 := by
    have hnat : (4473031527 : ℕ)^4423*3125000000000^3399 ≤ 1096959397083^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473031527 10000000000 1096959397083 3125000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536993061/1250000000 : ℝ), (206255059/500000000 : ℝ), (4473031527/10000000000 : ℝ)] ![(33305200280779/100000000000000 : ℝ), (15796049502169/50000000000000 : ℝ), (1096959397083/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536993061/1250000000 : ℝ)|^4423 ≤ (33305200280779/100000000000000 : ℝ)^3399
        have hw : |(536993061/1250000000 : ℝ)|=(536993061/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(206255059/500000000 : ℝ)|^4423 ≤ (15796049502169/50000000000000 : ℝ)^3399
        have hw : |(206255059/500000000 : ℝ)|=(206255059/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4473031527/10000000000 : ℝ)|^4423 ≤ (1096959397083/3125000000000 : ℝ)^3399
        have hw : |(4473031527/10000000000 : ℝ)|=(4473031527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s6_4 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1943886467/10000000000 : ℝ)*x 0 + (5248191041/10000000000 : ℝ)*x 1 + (5405888193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1943886467/10000000000 : ℝ)^4423 ≤ (5933928140611/50000000000000 : ℝ)^3399 := by
    have hnat : (1943886467 : ℕ)^4423*50000000000000^3399 ≤ 5933928140611^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1943886467 10000000000 5933928140611 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5248191041/10000000000 : ℝ)^4423 ≤ (43217368235881/100000000000000 : ℝ)^3399 := by
    have hnat : (5248191041 : ℕ)^4423*100000000000000^3399 ≤ 43217368235881^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5248191041 10000000000 43217368235881 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405888193/10000000000 : ℝ)^4423 ≤ (44914775466507/100000000000000 : ℝ)^3399 := by
    have hnat : (5405888193 : ℕ)^4423*100000000000000^3399 ≤ 44914775466507^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405888193 10000000000 44914775466507 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1943886467/10000000000 : ℝ), (5248191041/10000000000 : ℝ), (5405888193/10000000000 : ℝ)] ![(5933928140611/50000000000000 : ℝ), (43217368235881/100000000000000 : ℝ), (44914775466507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1943886467/10000000000 : ℝ)|^4423 ≤ (5933928140611/50000000000000 : ℝ)^3399
        have hw : |(-1943886467/10000000000 : ℝ)|=(1943886467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5248191041/10000000000 : ℝ)|^4423 ≤ (43217368235881/100000000000000 : ℝ)^3399
        have hw : |(5248191041/10000000000 : ℝ)|=(5248191041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405888193/10000000000 : ℝ)|^4423 ≤ (44914775466507/100000000000000 : ℝ)^3399
        have hw : |(5405888193/10000000000 : ℝ)|=(5405888193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s6_5 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305158979/10000000000 : ℝ)*x 0 + (-1866453833/10000000000 : ℝ)*x 1 + (5405888193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305158979/10000000000 : ℝ)^4423 ≤ (43828806620417/100000000000000 : ℝ)^3399 := by
    have hnat : (5305158979 : ℕ)^4423*100000000000000^3399 ≤ 43828806620417^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305158979 10000000000 43828806620417 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1866453833/10000000000 : ℝ)^4423 ≤ (11256417888249/100000000000000 : ℝ)^3399 := by
    have hnat : (1866453833 : ℕ)^4423*100000000000000^3399 ≤ 11256417888249^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866453833 10000000000 11256417888249 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405888193/10000000000 : ℝ)^4423 ≤ (44914775466507/100000000000000 : ℝ)^3399 := by
    have hnat : (5405888193 : ℕ)^4423*100000000000000^3399 ≤ 44914775466507^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405888193 10000000000 44914775466507 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305158979/10000000000 : ℝ), (-1866453833/10000000000 : ℝ), (5405888193/10000000000 : ℝ)] ![(43828806620417/100000000000000 : ℝ), (11256417888249/100000000000000 : ℝ), (44914775466507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305158979/10000000000 : ℝ)|^4423 ≤ (43828806620417/100000000000000 : ℝ)^3399
        have hw : |(5305158979/10000000000 : ℝ)|=(5305158979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1866453833/10000000000 : ℝ)|^4423 ≤ (11256417888249/100000000000000 : ℝ)^3399
        have hw : |(-1866453833/10000000000 : ℝ)|=(1866453833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405888193/10000000000 : ℝ)|^4423 ≤ (44914775466507/100000000000000 : ℝ)^3399
        have hw : |(5405888193/10000000000 : ℝ)|=(5405888193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s6_6 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305158979/10000000000 : ℝ)*x 0 + (5405888193/10000000000 : ℝ)*x 1 + (-1866453833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305158979/10000000000 : ℝ)^4423 ≤ (43828806620417/100000000000000 : ℝ)^3399 := by
    have hnat : (5305158979 : ℕ)^4423*100000000000000^3399 ≤ 43828806620417^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305158979 10000000000 43828806620417 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405888193/10000000000 : ℝ)^4423 ≤ (44914775466507/100000000000000 : ℝ)^3399 := by
    have hnat : (5405888193 : ℕ)^4423*100000000000000^3399 ≤ 44914775466507^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405888193 10000000000 44914775466507 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1866453833/10000000000 : ℝ)^4423 ≤ (11256417888249/100000000000000 : ℝ)^3399 := by
    have hnat : (1866453833 : ℕ)^4423*100000000000000^3399 ≤ 11256417888249^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866453833 10000000000 11256417888249 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305158979/10000000000 : ℝ), (5405888193/10000000000 : ℝ), (-1866453833/10000000000 : ℝ)] ![(43828806620417/100000000000000 : ℝ), (44914775466507/100000000000000 : ℝ), (11256417888249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305158979/10000000000 : ℝ)|^4423 ≤ (43828806620417/100000000000000 : ℝ)^3399
        have hw : |(5305158979/10000000000 : ℝ)|=(5305158979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405888193/10000000000 : ℝ)|^4423 ≤ (44914775466507/100000000000000 : ℝ)^3399
        have hw : |(5405888193/10000000000 : ℝ)|=(5405888193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1866453833/10000000000 : ℝ)|^4423 ≤ (11256417888249/100000000000000 : ℝ)^3399
        have hw : |(-1866453833/10000000000 : ℝ)|=(1866453833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s6_7 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4295968387/10000000000 : ℝ)*x 0 + (1117943189/2500000000 : ℝ)*x 1 + (412636673/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4295968387/10000000000 : ℝ)^4423 ≤ (6661088276383/20000000000000 : ℝ)^3399 := by
    have hnat : (4295968387 : ℕ)^4423*20000000000000^3399 ≤ 6661088276383^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4295968387 10000000000 6661088276383 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1117943189/2500000000 : ℝ)^4423 ≤ (8772461718331/25000000000000 : ℝ)^3399 := by
    have hnat : (1117943189 : ℕ)^4423*25000000000000^3399 ≤ 8772461718331^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117943189 2500000000 8772461718331 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (412636673/1000000000 : ℝ)^4423 ≤ (31604711732263/100000000000000 : ℝ)^3399 := by
    have hnat : (412636673 : ℕ)^4423*100000000000000^3399 ≤ 31604711732263^3399*1000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412636673 1000000000 31604711732263 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4295968387/10000000000 : ℝ), (1117943189/2500000000 : ℝ), (412636673/1000000000 : ℝ)] ![(6661088276383/20000000000000 : ℝ), (8772461718331/25000000000000 : ℝ), (31604711732263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4295968387/10000000000 : ℝ)|^4423 ≤ (6661088276383/20000000000000 : ℝ)^3399
        have hw : |(4295968387/10000000000 : ℝ)|=(4295968387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1117943189/2500000000 : ℝ)|^4423 ≤ (8772461718331/25000000000000 : ℝ)^3399
        have hw : |(1117943189/2500000000 : ℝ)|=(1117943189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(412636673/1000000000 : ℝ)|^4423 ≤ (31604711732263/100000000000000 : ℝ)^3399
        have hw : |(412636673/1000000000 : ℝ)|=(412636673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1463_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2281/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (713/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7387/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1847/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2281/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1847/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2281/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1847/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2281/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1847/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2281/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1847/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2281/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1847/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2281/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2281/20000 : ℝ) ^ (2211/512 : ℝ) ≤ (847614942376523/10000000000000000000 : ℝ) := by
    have hpowers : (2281/20000 : ℝ)^2211 ≤ (847614942376523/10000000000000000000 : ℝ)^512 := by
      have hnat : (2281 : ℕ)^2211*10000000000000000000^512 ≤ 847614942376523^512*20000^2211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2281 20000 847614942376523 10000000000000000000 2211 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2281/20000 : ℝ)) (X := (847614942376523/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1847/12500 : ℝ) ^ (2211/512 : ℝ) ≤ (162079539906551/625000000000000000 : ℝ) := by
    have hpowers : (1847/12500 : ℝ)^2211 ≤ (162079539906551/625000000000000000 : ℝ)^512 := by
      have hnat : (1847 : ℕ)^2211*625000000000000000^512 ≤ 162079539906551^512*12500^2211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1847 12500 162079539906551 625000000000000000 2211 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1847/12500 : ℝ)) (X := (162079539906551/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000847614942376523/5000000000000000000 : ℝ) ≤ (10000392537844267/10000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (5000847614942376523/5000000000000000000 : ℝ)^512 ≤ (10000392537844267/10000000000000000 : ℝ)^2211 := by
      have hnat : (5000847614942376523 : ℕ)^512*10000000000000000^2211 ≤ 10000392537844267^2211*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000847614942376523 5000000000000000000 10000392537844267 10000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000392537844267/10000000000000000 : ℝ)) (X := (5000847614942376523/5000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003440887580881339/10000000000000000000 : ℝ) ≤ (5000398349520583/5000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (10003440887580881339/10000000000000000000 : ℝ)^512 ≤ (5000398349520583/5000000000000000 : ℝ)^2211 := by
      have hnat : (10003440887580881339 : ℕ)^512*5000000000000000^2211 ≤ 5000398349520583^2211*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003440887580881339 10000000000000000000 5000398349520583 5000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000398349520583/5000000000000000 : ℝ)) (X := (10003440887580881339/10000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (312662079539906551/312500000000000000 : ℝ) ≤ (2000240172047613/2000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (312662079539906551/312500000000000000 : ℝ)^512 ≤ (2000240172047613/2000000000000000 : ℝ)^2211 := by
      have hnat : (312662079539906551 : ℕ)^512*2000000000000000^2211 ≤ 2000240172047613^2211*312500000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312662079539906551 312500000000000000 2000240172047613 2000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000240172047613/2000000000000000 : ℝ)) (X := (312662079539906551/312500000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(847614942376523/10000000000000000000 : ℝ) ≤ ((33702104328171757867/33710000000000000000 : ℝ)+2*(404161196899/337100000000000 : ℝ)*(2281/20000 : ℝ))^(2211/512 : ℝ) := by
    rw [show (33702104328171757867/33710000000000000000 : ℝ)+2*(404161196899/337100000000000 : ℝ)*(2281/20000 : ℝ)=(10000392537844267/10000000000000000 : ℝ) by norm_num, show 1+2*(847614942376523/10000000000000000000 : ℝ)=(5000847614942376523/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(162079539906551/625000000000000000 : ℝ)+(847614942376523/10000000000000000000 : ℝ) ≤ ((33702104328171757867/33710000000000000000 : ℝ)+(404161196899/337100000000000 : ℝ)*((1847/12500 : ℝ)+(2281/20000 : ℝ)))^(2211/512 : ℝ) := by
    rw [show (33702104328171757867/33710000000000000000 : ℝ)+(404161196899/337100000000000 : ℝ)*((1847/12500 : ℝ)+(2281/20000 : ℝ))=(5000398349520583/5000000000000000 : ℝ) by norm_num, show 1+(162079539906551/625000000000000000 : ℝ)+(847614942376523/10000000000000000000 : ℝ)=(10003440887580881339/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(162079539906551/625000000000000000 : ℝ) ≤ ((33702104328171757867/33710000000000000000 : ℝ)+2*(404161196899/337100000000000 : ℝ)*(1847/12500 : ℝ))^(2211/512 : ℝ) := by
    rw [show (33702104328171757867/33710000000000000000 : ℝ)+2*(404161196899/337100000000000 : ℝ)*(1847/12500 : ℝ)=(2000240172047613/2000000000000000 : ℝ) by norm_num, show 1+2*(162079539906551/625000000000000000 : ℝ)=(312662079539906551/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33702104328171757867/33710000000000000000 : ℝ)*(X 1 0+X 2 0)+(404161196899/337100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (2281/20000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (33702104328171757867/33710000000000000000 : ℝ)) (alpha := (404161196899/337100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33702104328171757867/33710000000000000000 : ℝ)*(X 0 1+X 2 1)+(404161196899/337100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (2281/20000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (33702104328171757867/33710000000000000000 : ℝ)) (alpha := (404161196899/337100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33702104328171757867/33710000000000000000 : ℝ)*(X 0 2+X 1 2)+(404161196899/337100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (2281/20000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (33702104328171757867/33710000000000000000 : ℝ)) (alpha := (404161196899/337100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-485968879/2500000000 : ℝ)*X 0 0+(5406465641/10000000000 : ℝ)*X 0 1+(5247616521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673294439/5000000000 : ℝ)*X 1 0+(-2024725609/10000000000 : ℝ)*X 1 1+(1049523293/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336647267/2500000000 : ℝ)*X 2 0+(262380811/500000000 : ℝ)*X 2 1+(-2024725681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((536993061/1250000000 : ℝ)*X 0 0+(206255059/500000000 : ℝ)*X 0 1+(4473031527/10000000000 : ℝ)*X 0 2+(536993061/1250000000 : ℝ)*X 1 0+(206255059/500000000 : ℝ)*X 1 1+(4473031527/10000000000 : ℝ)*X 1 2+(536993061/1250000000 : ℝ)*X 2 0+(206255059/500000000 : ℝ)*X 2 1+(4473031527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1943886467/10000000000 : ℝ)*X 0 0+(5248191041/10000000000 : ℝ)*X 0 1+(5405888193/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305158979/10000000000 : ℝ)*X 1 0+(-1866453833/10000000000 : ℝ)*X 1 1+(5405888193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305158979/10000000000 : ℝ)*X 2 0+(5405888193/10000000000 : ℝ)*X 2 1+(-1866453833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4295968387/10000000000 : ℝ)*X 0 0+(1117943189/2500000000 : ℝ)*X 0 1+(412636673/1000000000 : ℝ)*X 0 2+(4295968387/10000000000 : ℝ)*X 1 0+(1117943189/2500000000 : ℝ)*X 1 1+(412636673/1000000000 : ℝ)*X 1 2+(4295968387/10000000000 : ℝ)*X 2 0+(1117943189/2500000000 : ℝ)*X 2 1+(412636673/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3624998760800015659159879323/842750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (512639353/50000000000000 : ℝ)*(base19) + (1149167243/100000000000000 : ℝ)*(base23) + (1334321/2500000000000 : ℝ)*(lower2) + (6638107/3125000000000 : ℝ)*(upper3) + (83918489/100000000000000 : ℝ)*(upper5) + (4584738577513477/100000000000000 : ℝ)*(major0) + (4584738577513477/100000000000000 : ℝ)*(major1) + (2292369288756739/50000000000000 : ℝ)*(major2) + (6295299076964917/100000000000000 : ℝ)*(sp0) + (3147656594429967/50000000000000 : ℝ)*(sp1) + (1573828266242849/25000000000000 : ℝ)*(sp2) + (17963431468651/625000000000 : ℝ)*(sp3) + (15137173723/100000000000000 : ℝ)*(sp4) + (3440631097/25000000000000 : ℝ)*(sp7) + (718540699377137/25000000000000 : ℝ)*(f.failure) + (6295314214138639/100000000000000 : ℝ)*(f.sum) + (57802528295357/6742000000000000000000000000 : ℝ)*base66 + (611423106717473559/3371000000000000000000000000000000 : ℝ)*base67 + (15472705419675665713/1685500000000000000000000000000000 : ℝ)*base69 + (28196209178597473559/3371000000000000000000000000000000 : ℝ)*base71 + (1971465446483/1348400000000000000000000000 : ℝ)*base74 + (2553830032421334287/1685500000000000000000000000000000 : ℝ)*base76 + (18170604941911573559/3371000000000000000000000000000000 : ℝ)*base77 + (20616622484747573559/3371000000000000000000000000000000 : ℝ)*base79 + (62151759501997/16855000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1997197/2500000000000000000000 : ℝ)*base90 + (1997197/2500000000000000000000 : ℝ)*base92 + (26997197/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87337780026374449462347/8427500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1727658563/100000000000000 : ℝ)*(base19) + (1876598361/100000000000000 : ℝ)*(base23) + (582627641/100000000000000 : ℝ)*(lower1) + (211078009/100000000000000 : ℝ)*(upper3) + (33801279/50000000000000 : ℝ)*(lower4) + (42524903/20000000000000 : ℝ)*(upper5) + (4618178316016047/100000000000000 : ℝ)*(major0) + (4618178316016047/100000000000000 : ℝ)*(major1) + (4618178316016047/100000000000000 : ℝ)*(major2) + (2754610009/100000000000000 : ℝ)*(sp2) + (6341230188609087/100000000000000 : ℝ)*(sp4) + (1585307115237631/25000000000000 : ℝ)*(sp5) + (6341225557400717/100000000000000 : ℝ)*(sp6) + (1447563048987713/50000000000000 : ℝ)*(sp7) + (1447563048987713/50000000000000 : ℝ)*(f.failure) + (6341230188609087/100000000000000 : ℝ)*(f.sum) + (55971009574481/8427500000000000000000000000 : ℝ)*base66 + (142374596754862791749/3371000000000000000000000000000000 : ℝ)*base67 + (16116140842954791749/3371000000000000000000000000000000 : ℝ)*base69 + (36719942003677791749/3371000000000000000000000000000000 : ℝ)*base71 + (67694329292967/16855000000000000000000000000 : ℝ)*base74 + (330230354869556208251/3371000000000000000000000000000000 : ℝ)*base76 + (843160074711208251/3371000000000000000000000000000000 : ℝ)*base78 + (33450664411711208251/3371000000000000000000000000000000 : ℝ)*base80 + (72551035058803/16855000000000000000000000000 : ℝ)*base81 + (12589347/5000000000000000000000 : ℝ)*base89 + (12589347/5000000000000000000000 : ℝ)*base91 + (12589347/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1463_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2281/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (713/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1463_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1463_s7_0 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346585507/10000000000 : ℝ)*x 0 + (1049526569/2000000000 : ℝ)*x 1 + (-2024708303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346585507/10000000000 : ℝ)^4423 ≤ (5534335464917/12500000000000 : ℝ)^3399 := by
    have hnat : (5346585507 : ℕ)^4423*12500000000000^3399 ≤ 5534335464917^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346585507 10000000000 5534335464917 12500000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049526569/2000000000 : ℝ)^4423 ≤ (270071168467/625000000000 : ℝ)^3399 := by
    have hnat : (1049526569 : ℕ)^4423*625000000000^3399 ≤ 270071168467^3399*2000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049526569 2000000000 270071168467 625000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2024708303/10000000000 : ℝ)^4423 ≤ (6256964655929/50000000000000 : ℝ)^3399 := by
    have hnat : (2024708303 : ℕ)^4423*50000000000000^3399 ≤ 6256964655929^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2024708303 10000000000 6256964655929 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346585507/10000000000 : ℝ), (1049526569/2000000000 : ℝ), (-2024708303/10000000000 : ℝ)] ![(5534335464917/12500000000000 : ℝ), (270071168467/625000000000 : ℝ), (6256964655929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346585507/10000000000 : ℝ)|^4423 ≤ (5534335464917/12500000000000 : ℝ)^3399
        have hw : |(5346585507/10000000000 : ℝ)|=(5346585507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049526569/2000000000 : ℝ)|^4423 ≤ (270071168467/625000000000 : ℝ)^3399
        have hw : |(1049526569/2000000000 : ℝ)|=(1049526569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2024708303/10000000000 : ℝ)|^4423 ≤ (6256964655929/50000000000000 : ℝ)^3399
        have hw : |(-2024708303/10000000000 : ℝ)|=(2024708303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s7_1 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (134248293/312500000 : ℝ)*x 0 + (2062568403/5000000000 : ℝ)*x 1 + (2236497941/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134248293/312500000 : ℝ)^4423 ≤ (16652604619607/50000000000000 : ℝ)^3399 := by
    have hnat : (134248293 : ℕ)^4423*50000000000000^3399 ≤ 16652604619607^3399*312500000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134248293 312500000 16652604619607 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062568403/5000000000 : ℝ)^4423 ≤ (15796227022167/50000000000000 : ℝ)^3399 := by
    have hnat : (2062568403 : ℕ)^4423*50000000000000^3399 ≤ 15796227022167^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062568403 5000000000 15796227022167 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2236497941/5000000000 : ℝ)^4423 ≤ (17551168352883/50000000000000 : ℝ)^3399 := by
    have hnat : (2236497941 : ℕ)^4423*50000000000000^3399 ≤ 17551168352883^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2236497941 5000000000 17551168352883 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134248293/312500000 : ℝ), (2062568403/5000000000 : ℝ), (2236497941/5000000000 : ℝ)] ![(16652604619607/50000000000000 : ℝ), (15796227022167/50000000000000 : ℝ), (17551168352883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134248293/312500000 : ℝ)|^4423 ≤ (16652604619607/50000000000000 : ℝ)^3399
        have hw : |(134248293/312500000 : ℝ)|=(134248293/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2062568403/5000000000 : ℝ)|^4423 ≤ (15796227022167/50000000000000 : ℝ)^3399
        have hw : |(2062568403/5000000000 : ℝ)|=(2062568403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2236497941/5000000000 : ℝ)|^4423 ≤ (17551168352883/50000000000000 : ℝ)^3399
        have hw : |(2236497941/5000000000 : ℝ)|=(2236497941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s7_2 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-971942813/5000000000 : ℝ)*x 0 + (1312051831/2500000000 : ℝ)*x 1 + (168933521/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (971942813/5000000000 : ℝ)^4423 ≤ (11867849599889/100000000000000 : ℝ)^3399 := by
    have hnat : (971942813 : ℕ)^4423*100000000000000^3399 ≤ 11867849599889^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971942813 5000000000 11867849599889 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1312051831/2500000000 : ℝ)^4423 ≤ (21608771358629/50000000000000 : ℝ)^3399 := by
    have hnat : (1312051831 : ℕ)^4423*50000000000000^3399 ≤ 21608771358629^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312051831 2500000000 21608771358629 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168933521/312500000 : ℝ)^4423 ≤ (44914607660517/100000000000000 : ℝ)^3399 := by
    have hnat : (168933521 : ℕ)^4423*100000000000000^3399 ≤ 44914607660517^3399*312500000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168933521 312500000 44914607660517 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-971942813/5000000000 : ℝ), (1312051831/2500000000 : ℝ), (168933521/312500000 : ℝ)] ![(11867849599889/100000000000000 : ℝ), (21608771358629/50000000000000 : ℝ), (44914607660517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-971942813/5000000000 : ℝ)|^4423 ≤ (11867849599889/100000000000000 : ℝ)^3399
        have hw : |(-971942813/5000000000 : ℝ)|=(971942813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1312051831/2500000000 : ℝ)|^4423 ≤ (21608771358629/50000000000000 : ℝ)^3399
        have hw : |(1312051831/2500000000 : ℝ)|=(1312051831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168933521/312500000 : ℝ)|^4423 ≤ (44914607660517/100000000000000 : ℝ)^3399
        have hw : |(168933521/312500000 : ℝ)|=(168933521/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s7_3 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652581673/5000000000 : ℝ)*x 0 + (-1866469431/10000000000 : ℝ)*x 1 + (5405872529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652581673/5000000000 : ℝ)^4423 ≤ (43828853567679/100000000000000 : ℝ)^3399 := by
    have hnat : (2652581673 : ℕ)^4423*100000000000000^3399 ≤ 43828853567679^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652581673 5000000000 43828853567679 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1866469431/10000000000 : ℝ)^4423 ≤ (2251308059723/20000000000000 : ℝ)^3399 := by
    have hnat : (1866469431 : ℕ)^4423*20000000000000^3399 ≤ 2251308059723^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866469431 10000000000 2251308059723 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405872529/10000000000 : ℝ)^4423 ≤ (44914606114467/100000000000000 : ℝ)^3399 := by
    have hnat : (5405872529 : ℕ)^4423*100000000000000^3399 ≤ 44914606114467^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405872529 10000000000 44914606114467 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652581673/5000000000 : ℝ), (-1866469431/10000000000 : ℝ), (5405872529/10000000000 : ℝ)] ![(43828853567679/100000000000000 : ℝ), (2251308059723/20000000000000 : ℝ), (44914606114467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652581673/5000000000 : ℝ)|^4423 ≤ (43828853567679/100000000000000 : ℝ)^3399
        have hw : |(2652581673/5000000000 : ℝ)|=(2652581673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1866469431/10000000000 : ℝ)|^4423 ≤ (2251308059723/20000000000000 : ℝ)^3399
        have hw : |(-1866469431/10000000000 : ℝ)|=(1866469431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405872529/10000000000 : ℝ)|^4423 ≤ (44914606114467/100000000000000 : ℝ)^3399
        have hw : |(5405872529/10000000000 : ℝ)|=(5405872529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s7_4 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305164411/10000000000 : ℝ)*x 0 + (2702936081/5000000000 : ℝ)*x 1 + (-1866468479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305164411/10000000000 : ℝ)^4423 ≤ (43828865016921/100000000000000 : ℝ)^3399 := by
    have hnat : (5305164411 : ℕ)^4423*100000000000000^3399 ≤ 43828865016921^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305164411 10000000000 43828865016921 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702936081/5000000000 : ℝ)^4423 ≤ (5614325268329/12500000000000 : ℝ)^3399 := by
    have hnat : (2702936081 : ℕ)^4423*12500000000000^3399 ≤ 5614325268329^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702936081 5000000000 5614325268329 12500000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1866468479/10000000000 : ℝ)^4423 ≤ (11256532827477/100000000000000 : ℝ)^3399 := by
    have hnat : (1866468479 : ℕ)^4423*100000000000000^3399 ≤ 11256532827477^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866468479 10000000000 11256532827477 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305164411/10000000000 : ℝ), (2702936081/5000000000 : ℝ), (-1866468479/10000000000 : ℝ)] ![(43828865016921/100000000000000 : ℝ), (5614325268329/12500000000000 : ℝ), (11256532827477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305164411/10000000000 : ℝ)|^4423 ≤ (43828865016921/100000000000000 : ℝ)^3399
        have hw : |(5305164411/10000000000 : ℝ)|=(5305164411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702936081/5000000000 : ℝ)|^4423 ≤ (5614325268329/12500000000000 : ℝ)^3399
        have hw : |(2702936081/5000000000 : ℝ)|=(2702936081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1866468479/10000000000 : ℝ)|^4423 ≤ (11256532827477/100000000000000 : ℝ)^3399
        have hw : |(-1866468479/10000000000 : ℝ)|=(1866468479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_s7_5 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (859193797/2000000000 : ℝ)*x 0 + (4471738377/10000000000 : ℝ)*x 1 + (825280269/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859193797/2000000000 : ℝ)^4423 ≤ (6661089482949/20000000000000 : ℝ)^3399 := by
    have hnat : (859193797 : ℕ)^4423*20000000000000^3399 ≤ 6661089482949^3399*2000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859193797 2000000000 6661089482949 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4471738377/10000000000 : ℝ)^4423 ≤ (35089495830371/100000000000000 : ℝ)^3399 := by
    have hnat : (4471738377 : ℕ)^4423*100000000000000^3399 ≤ 35089495830371^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4471738377 10000000000 35089495830371 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (825280269/2000000000 : ℝ)^4423 ≤ (31605056728747/100000000000000 : ℝ)^3399 := by
    have hnat : (825280269 : ℕ)^4423*100000000000000^3399 ≤ 31605056728747^3399*2000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825280269 2000000000 31605056728747 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859193797/2000000000 : ℝ), (4471738377/10000000000 : ℝ), (825280269/2000000000 : ℝ)] ![(6661089482949/20000000000000 : ℝ), (35089495830371/100000000000000 : ℝ), (31605056728747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859193797/2000000000 : ℝ)|^4423 ≤ (6661089482949/20000000000000 : ℝ)^3399
        have hw : |(859193797/2000000000 : ℝ)|=(859193797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4471738377/10000000000 : ℝ)|^4423 ≤ (35089495830371/100000000000000 : ℝ)^3399
        have hw : |(4471738377/10000000000 : ℝ)|=(4471738377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(825280269/2000000000 : ℝ)|^4423 ≤ (31605056728747/100000000000000 : ℝ)^3399
        have hw : |(825280269/2000000000 : ℝ)|=(825280269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1463_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (713/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (713/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14773/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7387/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (713/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7387/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (713/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7387/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (713/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7387/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (713/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7387/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (713/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7387/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (713/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
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
  have hpowlo : (713/6250 : ℝ) ^ (2211/512 : ℝ) ≤ (8485781787840201/100000000000000000000 : ℝ) := by
    have hpowers : (713/6250 : ℝ)^2211 ≤ (8485781787840201/100000000000000000000 : ℝ)^512 := by
      have hnat : (713 : ℕ)^2211*100000000000000000000^512 ≤ 8485781787840201^512*6250^2211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        713 6250 8485781787840201 100000000000000000000 2211 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (713/6250 : ℝ)) (X := (8485781787840201/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7387/50000 : ℝ) ^ (2211/512 : ℝ) ≤ (647939296317477/2500000000000000000 : ℝ) := by
    have hpowers : (7387/50000 : ℝ)^2211 ≤ (647939296317477/2500000000000000000 : ℝ)^512 := by
      have hnat : (7387 : ℕ)^2211*2500000000000000000^512 ≤ 647939296317477^512*50000^2211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7387 50000 647939296317477 2500000000000000000 2211 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7387/50000 : ℝ)) (X := (647939296317477/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008485781787840201/50000000000000000000 : ℝ) ≤ (2500098245974583/2500000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (50008485781787840201/50000000000000000000 : ℝ)^512 ≤ (2500098245974583/2500000000000000 : ℝ)^2211 := by
      have hnat : (50008485781787840201 : ℕ)^512*2500000000000000^2211 ≤ 2500098245974583^2211*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008485781787840201 50000000000000000000 2500098245974583 2500000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500098245974583/2500000000000000 : ℝ)) (X := (50008485781787840201/50000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034403353640539281/100000000000000000000 : ℝ) ≤ (10000796571198431/10000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (100034403353640539281/100000000000000000000 : ℝ)^512 ≤ (10000796571198431/10000000000000000 : ℝ)^2211 := by
      have hnat : (100034403353640539281 : ℕ)^512*10000000000000000^2211 ≤ 10000796571198431^2211*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034403353640539281 100000000000000000000 10000796571198431 10000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000796571198431/10000000000000000 : ℝ)) (X := (100034403353640539281/100000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250647939296317477/1250000000000000000 : ℝ) ≤ (1000120015849853/1000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (1250647939296317477/1250000000000000000 : ℝ)^512 ≤ (1000120015849853/1000000000000000 : ℝ)^2211 := by
      have hnat : (1250647939296317477 : ℕ)^512*1000000000000000^2211 ≤ 1000120015849853^2211*1250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250647939296317477 1250000000000000000 1000120015849853 1000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000120015849853/1000000000000000 : ℝ)) (X := (1250647939296317477/1250000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8485781787840201/100000000000000000000 : ℝ) ≤ ((1402171438998446947/1402500000000000000 : ℝ)+2*(134529100033/112200000000000 : ℝ)*(713/6250 : ℝ))^(2211/512 : ℝ) := by
    rw [show (1402171438998446947/1402500000000000000 : ℝ)+2*(134529100033/112200000000000 : ℝ)*(713/6250 : ℝ)=(2500098245974583/2500000000000000 : ℝ) by norm_num, show 1+2*(8485781787840201/100000000000000000000 : ℝ)=(50008485781787840201/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(647939296317477/2500000000000000000 : ℝ)+(8485781787840201/100000000000000000000 : ℝ) ≤ ((1402171438998446947/1402500000000000000 : ℝ)+(134529100033/112200000000000 : ℝ)*((7387/50000 : ℝ)+(713/6250 : ℝ)))^(2211/512 : ℝ) := by
    rw [show (1402171438998446947/1402500000000000000 : ℝ)+(134529100033/112200000000000 : ℝ)*((7387/50000 : ℝ)+(713/6250 : ℝ))=(10000796571198431/10000000000000000 : ℝ) by norm_num, show 1+(647939296317477/2500000000000000000 : ℝ)+(8485781787840201/100000000000000000000 : ℝ)=(100034403353640539281/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(647939296317477/2500000000000000000 : ℝ) ≤ ((1402171438998446947/1402500000000000000 : ℝ)+2*(134529100033/112200000000000 : ℝ)*(7387/50000 : ℝ))^(2211/512 : ℝ) := by
    rw [show (1402171438998446947/1402500000000000000 : ℝ)+2*(134529100033/112200000000000 : ℝ)*(7387/50000 : ℝ)=(1000120015849853/1000000000000000 : ℝ) by norm_num, show 1+2*(647939296317477/2500000000000000000 : ℝ)=(1250647939296317477/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1402171438998446947/1402500000000000000 : ℝ)*(X 1 0+X 2 0)+(134529100033/112200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (713/6250 : ℝ)) (hi := (7387/50000 : ℝ)) (c := (1402171438998446947/1402500000000000000 : ℝ)) (alpha := (134529100033/112200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1402171438998446947/1402500000000000000 : ℝ)*(X 0 1+X 2 1)+(134529100033/112200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (713/6250 : ℝ)) (hi := (7387/50000 : ℝ)) (c := (1402171438998446947/1402500000000000000 : ℝ)) (alpha := (134529100033/112200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1402171438998446947/1402500000000000000 : ℝ)*(X 0 2+X 1 2)+(134529100033/112200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (713/6250 : ℝ)) (hi := (7387/50000 : ℝ)) (c := (1402171438998446947/1402500000000000000 : ℝ)) (alpha := (134529100033/112200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5346585507/10000000000 : ℝ)*X 2 0+(1049526569/2000000000 : ℝ)*X 2 1+(-2024708303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s7_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((134248293/312500000 : ℝ)*X 0 0+(2062568403/5000000000 : ℝ)*X 0 1+(2236497941/5000000000 : ℝ)*X 0 2+(134248293/312500000 : ℝ)*X 1 0+(2062568403/5000000000 : ℝ)*X 1 1+(2236497941/5000000000 : ℝ)*X 1 2+(134248293/312500000 : ℝ)*X 2 0+(2062568403/5000000000 : ℝ)*X 2 1+(2236497941/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s7_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-971942813/5000000000 : ℝ)*X 0 0+(1312051831/2500000000 : ℝ)*X 0 1+(168933521/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s7_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2652581673/5000000000 : ℝ)*X 1 0+(-1866469431/10000000000 : ℝ)*X 1 1+(5405872529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s7_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5305164411/10000000000 : ℝ)*X 2 0+(2702936081/5000000000 : ℝ)*X 2 1+(-1866468479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s7_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((859193797/2000000000 : ℝ)*X 0 0+(4471738377/10000000000 : ℝ)*X 0 1+(825280269/2000000000 : ℝ)*X 0 2+(859193797/2000000000 : ℝ)*X 1 0+(4471738377/10000000000 : ℝ)*X 1 1+(825280269/2000000000 : ℝ)*X 1 2+(859193797/2000000000 : ℝ)*X 2 0+(4471738377/10000000000 : ℝ)*X 2 1+(825280269/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (125633810052687409699537237/23375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (589827/20000000000000 : ℝ)*(base8) + (2101539/10000000000000 : ℝ)*(upper1) + (11971809/3125000000000 : ℝ)*(lower2) + (68089249/100000000000000 : ℝ)*(lower3) + (17272703/5000000000000 : ℝ)*(upper4) + (4619161988555429/100000000000000 : ℝ)*(major0) + (4619161988555429/100000000000000 : ℝ)*(major1) + (461916198855543/10000000000000 : ℝ)*(major2) + (12811604367/100000000000000 : ℝ)*(sp0) + (2647263091/50000000000000 : ℝ)*(sp1) + (792822629352577/12500000000000 : ℝ)*(sp2) + (6342581037769751/100000000000000 : ℝ)*(sp3) + (792821028270673/12500000000000 : ℝ)*(sp4) + (1447868732828983/50000000000000 : ℝ)*(sp5) + (723935690046037/25000000000000 : ℝ)*(f.failure) + (6342581037769751/100000000000000 : ℝ)*(f.sum) + (124958681240627/11220000000000000000000000000 : ℝ)*base65 + (123944094122209067/12750000000000000000000000000000 : ℝ)*base68 + (697937063673826529/14025000000000000000000000000000 : ℝ)*base70 + (258416187170290933/12750000000000000000000000000000 : ℝ)*base71 + (14310621912887/11220000000000000000000000000 : ℝ)*base73 + (4694899139998471/14025000000000000000000000000000 : ℝ)*base75 + (29528940260345921/46750000000000000000000000000000 : ℝ)*base77 + (158764015586845921/46750000000000000000000000000000 : ℝ)*base79 + (10522362383387/5610000000000000000000000000 : ℝ)*base81 + (5551903/2500000000000000000000 : ℝ)*base89 + (5551903/2500000000000000000000 : ℝ)*base91 + (19448097/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1463_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (713/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (713/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1463_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1463_box_0 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-892815899/5000000000 : ℝ)*x 0 + (2692396633/5000000000 : ℝ)*x 1 + (5384792997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892815899/5000000000 : ℝ)^4423 ≤ (106263212921/1000000000000 : ℝ)^3399 := by
    have hnat : (892815899 : ℕ)^4423*1000000000000^3399 ≤ 106263212921^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892815899 5000000000 106263212921 1000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692396633/5000000000 : ℝ)^4423 ≤ (22343420398041/50000000000000 : ℝ)^3399 := by
    have hnat : (2692396633 : ℕ)^4423*50000000000000^3399 ≤ 22343420398041^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692396633 5000000000 22343420398041 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384792997/10000000000 : ℝ)^4423 ≤ (44686837891199/100000000000000 : ℝ)^3399 := by
    have hnat : (5384792997 : ℕ)^4423*100000000000000^3399 ≤ 44686837891199^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384792997 10000000000 44686837891199 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-892815899/5000000000 : ℝ), (2692396633/5000000000 : ℝ), (5384792997/10000000000 : ℝ)] ![(106263212921/1000000000000 : ℝ), (22343420398041/50000000000000 : ℝ), (44686837891199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-892815899/5000000000 : ℝ)|^4423 ≤ (106263212921/1000000000000 : ℝ)^3399
        have hw : |(-892815899/5000000000 : ℝ)|=(892815899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692396633/5000000000 : ℝ)|^4423 ≤ (22343420398041/50000000000000 : ℝ)^3399
        have hw : |(2692396633/5000000000 : ℝ)|=(2692396633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384792997/10000000000 : ℝ)|^4423 ≤ (44686837891199/100000000000000 : ℝ)^3399
        have hw : |(5384792997/10000000000 : ℝ)|=(5384792997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_box_1 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643133687/5000000000 : ℝ)*x 0 + (-960562067/5000000000 : ℝ)*x 1 + (5384792937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643133687/5000000000 : ℝ)^4423 ≤ (43625822220463/100000000000000 : ℝ)^3399 := by
    have hnat : (2643133687 : ℕ)^4423*100000000000000^3399 ≤ 43625822220463^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643133687 5000000000 43625822220463 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (960562067/5000000000 : ℝ)^4423 ≤ (11687340525443/100000000000000 : ℝ)^3399 := by
    have hnat : (960562067 : ℕ)^4423*100000000000000^3399 ≤ 11687340525443^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960562067 5000000000 11687340525443 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384792937/10000000000 : ℝ)^4423 ≤ (44686837243269/100000000000000 : ℝ)^3399 := by
    have hnat : (5384792937 : ℕ)^4423*100000000000000^3399 ≤ 44686837243269^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384792937 10000000000 44686837243269 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643133687/5000000000 : ℝ), (-960562067/5000000000 : ℝ), (5384792937/10000000000 : ℝ)] ![(43625822220463/100000000000000 : ℝ), (11687340525443/100000000000000 : ℝ), (44686837243269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643133687/5000000000 : ℝ)|^4423 ≤ (43625822220463/100000000000000 : ℝ)^3399
        have hw : |(2643133687/5000000000 : ℝ)|=(2643133687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-960562067/5000000000 : ℝ)|^4423 ≤ (11687340525443/100000000000000 : ℝ)^3399
        have hw : |(-960562067/5000000000 : ℝ)|=(960562067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384792937/10000000000 : ℝ)|^4423 ≤ (44686837243269/100000000000000 : ℝ)^3399
        have hw : |(5384792937/10000000000 : ℝ)|=(5384792937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_box_2 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5286267231/10000000000 : ℝ)*x 0 + (1346198303/2500000000 : ℝ)*x 1 + (-120070247/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286267231/10000000000 : ℝ)^4423 ≤ (43625820684799/100000000000000 : ℝ)^3399 := by
    have hnat : (5286267231 : ℕ)^4423*100000000000000^3399 ≤ 43625820684799^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286267231 10000000000 43625820684799 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346198303/2500000000 : ℝ)^4423 ≤ (8937368042589/20000000000000 : ℝ)^3399 := by
    have hnat : (1346198303 : ℕ)^4423*20000000000000^3399 ≤ 8937368042589^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346198303 2500000000 8937368042589 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120070247/625000000 : ℝ)^4423 ≤ (1460917385583/12500000000000 : ℝ)^3399 := by
    have hnat : (120070247 : ℕ)^4423*12500000000000^3399 ≤ 1460917385583^3399*625000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120070247 625000000 1460917385583 12500000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286267231/10000000000 : ℝ), (1346198303/2500000000 : ℝ), (-120070247/625000000 : ℝ)] ![(43625820684799/100000000000000 : ℝ), (8937368042589/20000000000000 : ℝ), (1460917385583/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286267231/10000000000 : ℝ)|^4423 ≤ (43625820684799/100000000000000 : ℝ)^3399
        have hw : |(5286267231/10000000000 : ℝ)|=(5286267231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346198303/2500000000 : ℝ)|^4423 ≤ (8937368042589/20000000000000 : ℝ)^3399
        have hw : |(1346198303/2500000000 : ℝ)|=(1346198303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-120070247/625000000 : ℝ)|^4423 ≤ (1460917385583/12500000000000 : ℝ)^3399
        have hw : |(-120070247/625000000 : ℝ)|=(120070247/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_box_3 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4441581907/10000000000 : ℝ)*x 0 + (1056692879/2500000000 : ℝ)*x 1 + (264173207/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4441581907/10000000000 : ℝ)^4423 ≤ (17390941329051/50000000000000 : ℝ)^3399 := by
    have hnat : (4441581907 : ℕ)^4423*50000000000000^3399 ≤ 17390941329051^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4441581907 10000000000 17390941329051 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056692879/2500000000 : ℝ)^4423 ≤ (32609059682327/100000000000000 : ℝ)^3399 := by
    have hnat : (1056692879 : ℕ)^4423*100000000000000^3399 ≤ 32609059682327^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056692879 2500000000 32609059682327 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264173207/625000000 : ℝ)^4423 ≤ (32609057634349/100000000000000 : ℝ)^3399 := by
    have hnat : (264173207 : ℕ)^4423*100000000000000^3399 ≤ 32609057634349^3399*625000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264173207 625000000 32609057634349 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4441581907/10000000000 : ℝ), (1056692879/2500000000 : ℝ), (264173207/625000000 : ℝ)] ![(17390941329051/50000000000000 : ℝ), (32609059682327/100000000000000 : ℝ), (32609057634349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4441581907/10000000000 : ℝ)|^4423 ≤ (17390941329051/50000000000000 : ℝ)^3399
        have hw : |(4441581907/10000000000 : ℝ)|=(4441581907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056692879/2500000000 : ℝ)|^4423 ≤ (32609059682327/100000000000000 : ℝ)^3399
        have hw : |(1056692879/2500000000 : ℝ)|=(1056692879/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264173207/625000000 : ℝ)|^4423 ≤ (32609057634349/100000000000000 : ℝ)^3399
        have hw : |(264173207/625000000 : ℝ)|=(264173207/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_box_4 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2104851/10000000 : ℝ)*x 0 + (1316746053/2500000000 : ℝ)*x 1 + (329186479/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2104851/10000000 : ℝ)^4423 ≤ (1316229401553/10000000000000 : ℝ)^3399 := by
    have hnat : (2104851 : ℕ)^4423*10000000000000^3399 ≤ 1316229401553^3399*10000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104851 10000000 1316229401553 10000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316746053/2500000000 : ℝ)^4423 ≤ (2713678495449/6250000000000 : ℝ)^3399 := by
    have hnat : (1316746053 : ℕ)^4423*6250000000000^3399 ≤ 2713678495449^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316746053 2500000000 2713678495449 6250000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329186479/625000000 : ℝ)^4423 ≤ (1356839064023/3125000000000 : ℝ)^3399 := by
    have hnat : (329186479 : ℕ)^4423*3125000000000^3399 ≤ 1356839064023^3399*625000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329186479 625000000 1356839064023 3125000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2104851/10000000 : ℝ), (1316746053/2500000000 : ℝ), (329186479/625000000 : ℝ)] ![(1316229401553/10000000000000 : ℝ), (2713678495449/6250000000000 : ℝ), (1356839064023/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2104851/10000000 : ℝ)|^4423 ≤ (1316229401553/10000000000000 : ℝ)^3399
        have hw : |(-2104851/10000000 : ℝ)|=(2104851/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316746053/2500000000 : ℝ)|^4423 ≤ (2713678495449/6250000000000 : ℝ)^3399
        have hw : |(1316746053/2500000000 : ℝ)|=(1316746053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329186479/625000000 : ℝ)|^4423 ≤ (1356839064023/3125000000000 : ℝ)^3399
        have hw : |(329186479/625000000 : ℝ)|=(329186479/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_box_5 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684301307/5000000000 : ℝ)*x 0 + (-984581989/5000000000 : ℝ)*x 1 + (5266984033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684301307/5000000000 : ℝ)^4423 ≤ (27820050041/62500000000 : ℝ)^3399 := by
    have hnat : (2684301307 : ℕ)^4423*62500000000^3399 ≤ 27820050041^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684301307 5000000000 27820050041 62500000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (984581989/5000000000 : ℝ)^4423 ≤ (12069065908311/100000000000000 : ℝ)^3399 := by
    have hnat : (984581989 : ℕ)^4423*100000000000000^3399 ≤ 12069065908311^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984581989 5000000000 12069065908311 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266984033/10000000000 : ℝ)^4423 ≤ (21709427003517/50000000000000 : ℝ)^3399 := by
    have hnat : (5266984033 : ℕ)^4423*50000000000000^3399 ≤ 21709427003517^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266984033 10000000000 21709427003517 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684301307/5000000000 : ℝ), (-984581989/5000000000 : ℝ), (5266984033/10000000000 : ℝ)] ![(27820050041/62500000000 : ℝ), (12069065908311/100000000000000 : ℝ), (21709427003517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684301307/5000000000 : ℝ)|^4423 ≤ (27820050041/62500000000 : ℝ)^3399
        have hw : |(2684301307/5000000000 : ℝ)|=(2684301307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-984581989/5000000000 : ℝ)|^4423 ≤ (12069065908311/100000000000000 : ℝ)^3399
        have hw : |(-984581989/5000000000 : ℝ)|=(984581989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266984033/10000000000 : ℝ)|^4423 ≤ (21709427003517/50000000000000 : ℝ)^3399
        have hw : |(5266984033/10000000000 : ℝ)|=(5266984033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_box_6 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684301153/5000000000 : ℝ)*x 0 + (5266984027/10000000000 : ℝ)*x 1 + (-492291101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684301153/5000000000 : ℝ)^4423 ≤ (44512076742579/100000000000000 : ℝ)^3399 := by
    have hnat : (2684301153 : ℕ)^4423*100000000000000^3399 ≤ 44512076742579^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684301153 5000000000 44512076742579 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266984027/10000000000 : ℝ)^4423 ≤ (43418853942671/100000000000000 : ℝ)^3399 := by
    have hnat : (5266984027 : ℕ)^4423*100000000000000^3399 ≤ 43418853942671^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266984027 10000000000 43418853942671 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (492291101/2500000000 : ℝ)^4423 ≤ (12069069305871/100000000000000 : ℝ)^3399 := by
    have hnat : (492291101 : ℕ)^4423*100000000000000^3399 ≤ 12069069305871^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492291101 2500000000 12069069305871 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684301153/5000000000 : ℝ), (5266984027/10000000000 : ℝ), (-492291101/2500000000 : ℝ)] ![(44512076742579/100000000000000 : ℝ), (43418853942671/100000000000000 : ℝ), (12069069305871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684301153/5000000000 : ℝ)|^4423 ≤ (44512076742579/100000000000000 : ℝ)^3399
        have hw : |(2684301153/5000000000 : ℝ)|=(2684301153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266984027/10000000000 : ℝ)|^4423 ≤ (43418853942671/100000000000000 : ℝ)^3399
        have hw : |(5266984027/10000000000 : ℝ)|=(5266984027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-492291101/2500000000 : ℝ)|^4423 ≤ (12069069305871/100000000000000 : ℝ)^3399
        have hw : |(-492291101/2500000000 : ℝ)|=(492291101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_box_7 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1037303861/2500000000 : ℝ)*x 0 + (4372904709/10000000000 : ℝ)*x 1 + (4372904693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037303861/2500000000 : ℝ)^4423 ≤ (15916313434807/50000000000000 : ℝ)^3399 := by
    have hnat : (1037303861 : ℕ)^4423*50000000000000^3399 ≤ 15916313434807^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037303861 2500000000 15916313434807 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4372904709/10000000000 : ℝ)^4423 ≤ (17041843318691/50000000000000 : ℝ)^3399 := by
    have hnat : (4372904709 : ℕ)^4423*50000000000000^3399 ≤ 17041843318691^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372904709 10000000000 17041843318691 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4372904693/10000000000 : ℝ)^4423 ≤ (34083686475103/100000000000000 : ℝ)^3399 := by
    have hnat : (4372904693 : ℕ)^4423*100000000000000^3399 ≤ 34083686475103^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372904693 10000000000 34083686475103 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1037303861/2500000000 : ℝ), (4372904709/10000000000 : ℝ), (4372904693/10000000000 : ℝ)] ![(15916313434807/50000000000000 : ℝ), (17041843318691/50000000000000 : ℝ), (34083686475103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1037303861/2500000000 : ℝ)|^4423 ≤ (15916313434807/50000000000000 : ℝ)^3399
        have hw : |(1037303861/2500000000 : ℝ)|=(1037303861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4372904709/10000000000 : ℝ)|^4423 ≤ (17041843318691/50000000000000 : ℝ)^3399
        have hw : |(4372904709/10000000000 : ℝ)|=(4372904709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4372904693/10000000000 : ℝ)|^4423 ≤ (34083686475103/100000000000000 : ℝ)^3399
        have hw : |(4372904693/10000000000 : ℝ)|=(4372904693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_box_8 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2037542053/10000000000 : ℝ)*x 0 + (2592674373/5000000000 : ℝ)*x 1 + (539874473/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2037542053/10000000000 : ℝ)^4423 ≤ (2523448912689/20000000000000 : ℝ)^3399 := by
    have hnat : (2037542053 : ℕ)^4423*20000000000000^3399 ≤ 2523448912689^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2037542053 10000000000 2523448912689 20000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592674373/5000000000 : ℝ)^4423 ≤ (42545196488281/100000000000000 : ℝ)^3399 := by
    have hnat : (2592674373 : ℕ)^4423*100000000000000^3399 ≤ 42545196488281^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592674373 5000000000 42545196488281 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539874473/1000000000 : ℝ)^4423 ≤ (22418779469517/50000000000000 : ℝ)^3399 := by
    have hnat : (539874473 : ℕ)^4423*50000000000000^3399 ≤ 22418779469517^3399*1000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539874473 1000000000 22418779469517 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2037542053/10000000000 : ℝ), (2592674373/5000000000 : ℝ), (539874473/1000000000 : ℝ)] ![(2523448912689/20000000000000 : ℝ), (42545196488281/100000000000000 : ℝ), (22418779469517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2037542053/10000000000 : ℝ)|^4423 ≤ (2523448912689/20000000000000 : ℝ)^3399
        have hw : |(-2037542053/10000000000 : ℝ)|=(2037542053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592674373/5000000000 : ℝ)|^4423 ≤ (42545196488281/100000000000000 : ℝ)^3399
        have hw : |(2592674373/5000000000 : ℝ)|=(2592674373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539874473/1000000000 : ℝ)|^4423 ≤ (22418779469517/50000000000000 : ℝ)^3399
        have hw : |(539874473/1000000000 : ℝ)|=(539874473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_box_9 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276511883/10000000000 : ℝ)*x 0 + (-1915310073/10000000000 : ℝ)*x 1 + (43189971/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276511883/10000000000 : ℝ)^4423 ≤ (43521087998281/100000000000000 : ℝ)^3399 := by
    have hnat : (5276511883 : ℕ)^4423*100000000000000^3399 ≤ 43521087998281^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276511883 10000000000 43521087998281 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1915310073/10000000000 : ℝ)^4423 ≤ (5820667634217/50000000000000 : ℝ)^3399 := by
    have hnat : (1915310073 : ℕ)^4423*50000000000000^3399 ≤ 5820667634217^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915310073 10000000000 5820667634217 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43189971/80000000 : ℝ)^4423 ≤ (44837576716951/100000000000000 : ℝ)^3399 := by
    have hnat : (43189971 : ℕ)^4423*100000000000000^3399 ≤ 44837576716951^3399*80000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43189971 80000000 44837576716951 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276511883/10000000000 : ℝ), (-1915310073/10000000000 : ℝ), (43189971/80000000 : ℝ)] ![(43521087998281/100000000000000 : ℝ), (5820667634217/50000000000000 : ℝ), (44837576716951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276511883/10000000000 : ℝ)|^4423 ≤ (43521087998281/100000000000000 : ℝ)^3399
        have hw : |(5276511883/10000000000 : ℝ)|=(5276511883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1915310073/10000000000 : ℝ)|^4423 ≤ (5820667634217/50000000000000 : ℝ)^3399
        have hw : |(-1915310073/10000000000 : ℝ)|=(1915310073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43189971/80000000 : ℝ)|^4423 ≤ (44837576716951/100000000000000 : ℝ)^3399
        have hw : |(43189971/80000000 : ℝ)|=(43189971/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_box_10 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319127807/2500000000 : ℝ)*x 0 + (5398745017/10000000000 : ℝ)*x 1 + (-1915312817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319127807/2500000000 : ℝ)^4423 ≤ (2720067560513/6250000000000 : ℝ)^3399 := by
    have hnat : (1319127807 : ℕ)^4423*6250000000000^3399 ≤ 2720067560513^3399*2500000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319127807 2500000000 2720067560513 6250000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398745017/10000000000 : ℝ)^4423 ≤ (44837562040713/100000000000000 : ℝ)^3399 := by
    have hnat : (5398745017 : ℕ)^4423*100000000000000^3399 ≤ 44837562040713^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398745017 10000000000 44837562040713 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1915312817/10000000000 : ℝ)^4423 ≤ (11641356971129/100000000000000 : ℝ)^3399 := by
    have hnat : (1915312817 : ℕ)^4423*100000000000000^3399 ≤ 11641356971129^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915312817 10000000000 11641356971129 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319127807/2500000000 : ℝ), (5398745017/10000000000 : ℝ), (-1915312817/10000000000 : ℝ)] ![(2720067560513/6250000000000 : ℝ), (44837562040713/100000000000000 : ℝ), (11641356971129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319127807/2500000000 : ℝ)|^4423 ≤ (2720067560513/6250000000000 : ℝ)^3399
        have hw : |(1319127807/2500000000 : ℝ)|=(1319127807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398745017/10000000000 : ℝ)|^4423 ≤ (44837562040713/100000000000000 : ℝ)^3399
        have hw : |(5398745017/10000000000 : ℝ)|=(5398745017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1915312817/10000000000 : ℝ)|^4423 ≤ (11641356971129/100000000000000 : ℝ)^3399
        have hw : |(-1915312817/10000000000 : ℝ)|=(1915312817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_box_11 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2237825893/5000000000 : ℝ)*x 0 + (4209448291/10000000000 : ℝ)*x 1 + (841890147/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2237825893/5000000000 : ℝ)^4423 ≤ (1756473037717/5000000000000 : ℝ)^3399 := by
    have hnat : (2237825893 : ℕ)^4423*5000000000000^3399 ≤ 1756473037717^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237825893 5000000000 1756473037717 5000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4209448291/10000000000 : ℝ)^4423 ≤ (8108814340617/25000000000000 : ℝ)^3399 := by
    have hnat : (4209448291 : ℕ)^4423*25000000000000^3399 ≤ 8108814340617^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4209448291 10000000000 8108814340617 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (841890147/2000000000 : ℝ)^4423 ≤ (32435281867721/100000000000000 : ℝ)^3399 := by
    have hnat : (841890147 : ℕ)^4423*100000000000000^3399 ≤ 32435281867721^3399*2000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841890147 2000000000 32435281867721 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2237825893/5000000000 : ℝ), (4209448291/10000000000 : ℝ), (841890147/2000000000 : ℝ)] ![(1756473037717/5000000000000 : ℝ), (8108814340617/25000000000000 : ℝ), (32435281867721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2237825893/5000000000 : ℝ)|^4423 ≤ (1756473037717/5000000000000 : ℝ)^3399
        have hw : |(2237825893/5000000000 : ℝ)|=(2237825893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4209448291/10000000000 : ℝ)|^4423 ≤ (8108814340617/25000000000000 : ℝ)^3399
        have hw : |(4209448291/10000000000 : ℝ)|=(4209448291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(841890147/2000000000 : ℝ)|^4423 ≤ (32435281867721/100000000000000 : ℝ)^3399
        have hw : |(841890147/2000000000 : ℝ)|=(841890147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_box_12 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1853063903/10000000000 : ℝ)*x 0 + (136611737/250000000 : ℝ)*x 1 + (5255843713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1853063903/10000000000 : ℝ)^4423 ≤ (1115144994659/10000000000000 : ℝ)^3399 := by
    have hnat : (1853063903 : ℕ)^4423*10000000000000^3399 ≤ 1115144994659^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853063903 10000000000 1115144994659 10000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136611737/250000000 : ℝ)^4423 ≤ (45549161214087/100000000000000 : ℝ)^3399 := by
    have hnat : (136611737 : ℕ)^4423*100000000000000^3399 ≤ 45549161214087^3399*250000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136611737 250000000 45549161214087 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255843713/10000000000 : ℝ)^4423 ≤ (21649694414291/50000000000000 : ℝ)^3399 := by
    have hnat : (5255843713 : ℕ)^4423*50000000000000^3399 ≤ 21649694414291^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255843713 10000000000 21649694414291 50000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1853063903/10000000000 : ℝ), (136611737/250000000 : ℝ), (5255843713/10000000000 : ℝ)] ![(1115144994659/10000000000000 : ℝ), (45549161214087/100000000000000 : ℝ), (21649694414291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1853063903/10000000000 : ℝ)|^4423 ≤ (1115144994659/10000000000000 : ℝ)^3399
        have hw : |(-1853063903/10000000000 : ℝ)|=(1853063903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136611737/250000000 : ℝ)|^4423 ≤ (45549161214087/100000000000000 : ℝ)^3399
        have hw : |(136611737/250000000 : ℝ)|=(136611737/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255843713/10000000000 : ℝ)|^4423 ≤ (21649694414291/50000000000000 : ℝ)^3399
        have hw : |(5255843713/10000000000 : ℝ)|=(5255843713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_box_13 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688193741/5000000000 : ℝ)*x 0 + (-1973608811/10000000000 : ℝ)*x 1 + (5255843143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688193741/5000000000 : ℝ)^4423 ≤ (44596089580831/100000000000000 : ℝ)^3399 := by
    have hnat : (2688193741 : ℕ)^4423*100000000000000^3399 ≤ 44596089580831^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688193741 5000000000 44596089580831 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1973608811/10000000000 : ℝ)^4423 ≤ (12104527690797/100000000000000 : ℝ)^3399 := by
    have hnat : (1973608811 : ℕ)^4423*100000000000000^3399 ≤ 12104527690797^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973608811 10000000000 12104527690797 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255843143/10000000000 : ℝ)^4423 ≤ (43299382718037/100000000000000 : ℝ)^3399 := by
    have hnat : (5255843143 : ℕ)^4423*100000000000000^3399 ≤ 43299382718037^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255843143 10000000000 43299382718037 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688193741/5000000000 : ℝ), (-1973608811/10000000000 : ℝ), (5255843143/10000000000 : ℝ)] ![(44596089580831/100000000000000 : ℝ), (12104527690797/100000000000000 : ℝ), (43299382718037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688193741/5000000000 : ℝ)|^4423 ≤ (44596089580831/100000000000000 : ℝ)^3399
        have hw : |(2688193741/5000000000 : ℝ)|=(2688193741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1973608811/10000000000 : ℝ)|^4423 ≤ (12104527690797/100000000000000 : ℝ)^3399
        have hw : |(-1973608811/10000000000 : ℝ)|=(1973608811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255843143/10000000000 : ℝ)|^4423 ≤ (43299382718037/100000000000000 : ℝ)^3399
        have hw : |(5255843143/10000000000 : ℝ)|=(5255843143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_box_14 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688193749/5000000000 : ℝ)*x 0 + (2627921759/5000000000 : ℝ)*x 1 + (-394721657/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688193749/5000000000 : ℝ)^4423 ≤ (44596089753531/100000000000000 : ℝ)^3399 := by
    have hnat : (2688193749 : ℕ)^4423*100000000000000^3399 ≤ 44596089753531^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688193749 5000000000 44596089753531 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2627921759/5000000000 : ℝ)^4423 ≤ (10824846684533/25000000000000 : ℝ)^3399 := by
    have hnat : (2627921759 : ℕ)^4423*25000000000000^3399 ≤ 10824846684533^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627921759 5000000000 10824846684533 25000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394721657/2000000000 : ℝ)^4423 ≤ (12104523492837/100000000000000 : ℝ)^3399 := by
    have hnat : (394721657 : ℕ)^4423*100000000000000^3399 ≤ 12104523492837^3399*2000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394721657 2000000000 12104523492837 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688193749/5000000000 : ℝ), (2627921759/5000000000 : ℝ), (-394721657/2000000000 : ℝ)] ![(44596089753531/100000000000000 : ℝ), (10824846684533/25000000000000 : ℝ), (12104523492837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688193749/5000000000 : ℝ)|^4423 ≤ (44596089753531/100000000000000 : ℝ)^3399
        have hw : |(2688193749/5000000000 : ℝ)|=(2688193749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2627921759/5000000000 : ℝ)|^4423 ≤ (10824846684533/25000000000000 : ℝ)^3399
        have hw : |(2627921759/5000000000 : ℝ)|=(2627921759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-394721657/2000000000 : ℝ)|^4423 ≤ (12104523492837/100000000000000 : ℝ)^3399
        have hw : |(-394721657/2000000000 : ℝ)|=(394721657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1463_box_15 (p : ℝ) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2060558041/5000000000 : ℝ)*x 0 + (2193356611/5000000000 : ℝ)*x 1 + (4386713153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2060558041/5000000000 : ℝ)^4423 ≤ (1972024395333/6250000000000 : ℝ)^3399 := by
    have hnat : (2060558041 : ℕ)^4423*6250000000000^3399 ≤ 1972024395333^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060558041 5000000000 1972024395333 6250000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2193356611/5000000000 : ℝ)^4423 ≤ (2138987823787/6250000000000 : ℝ)^3399 := by
    have hnat : (2193356611 : ℕ)^4423*6250000000000^3399 ≤ 2138987823787^3399*5000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193356611 5000000000 2138987823787 6250000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4386713153/10000000000 : ℝ)^4423 ≤ (34223804480099/100000000000000 : ℝ)^3399 := by
    have hnat : (4386713153 : ℕ)^4423*100000000000000^3399 ≤ 34223804480099^3399*10000000000^4423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4386713153 10000000000 34223804480099 100000000000000 4423 3399 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4423/1024 : ℝ)) 4423 3399 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2060558041/5000000000 : ℝ), (2193356611/5000000000 : ℝ), (4386713153/10000000000 : ℝ)] ![(1972024395333/6250000000000 : ℝ), (2138987823787/6250000000000 : ℝ), (34223804480099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2060558041/5000000000 : ℝ)|^4423 ≤ (1972024395333/6250000000000 : ℝ)^3399
        have hw : |(2060558041/5000000000 : ℝ)|=(2060558041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2193356611/5000000000 : ℝ)|^4423 ≤ (2138987823787/6250000000000 : ℝ)^3399
        have hw : |(2193356611/5000000000 : ℝ)|=(2193356611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4386713153/10000000000 : ℝ)|^4423 ≤ (34223804480099/100000000000000 : ℝ)^3399
        have hw : |(4386713153/10000000000 : ℝ)|=(4386713153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1463_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (713/6250 : ℝ)*pair X i i ≤ pair X i h) :
    -(31461/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29591/50000 : ℝ) ∧ (40317/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84811/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (713/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (713/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (713/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (713/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (713/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (713/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (713/6250 : ℝ) ^ (2211/512 : ℝ) ≤ (8485781787840201/100000000000000000000 : ℝ) := by
    have hpowers : (713/6250 : ℝ)^2211 ≤ (8485781787840201/100000000000000000000 : ℝ)^512 := by
      have hnat : (713 : ℕ)^2211*100000000000000000000^512 ≤ 8485781787840201^512*6250^2211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        713 6250 8485781787840201 100000000000000000000 2211 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (713/6250 : ℝ)) (X := (8485781787840201/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14773/100000 : ℝ) ^ (2211/512 : ℝ) ≤ (25909997138957229/100000000000000000000 : ℝ) := by
    have hpowers : (14773/100000 : ℝ)^2211 ≤ (25909997138957229/100000000000000000000 : ℝ)^512 := by
      have hnat : (14773 : ℕ)^2211*100000000000000000000^512 ≤ 25909997138957229^512*100000^2211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14773 100000 25909997138957229 100000000000000000000 2211 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14773/100000 : ℝ)) (X := (25909997138957229/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008485781787840201/50000000000000000000 : ℝ) ≤ (2500098245974583/2500000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (50008485781787840201/50000000000000000000 : ℝ)^512 ≤ (2500098245974583/2500000000000000 : ℝ)^2211 := by
      have hnat : (50008485781787840201 : ℕ)^512*2500000000000000^2211 ≤ 2500098245974583^2211*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008485781787840201 50000000000000000000 2500098245974583 2500000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500098245974583/2500000000000000 : ℝ)) (X := (50008485781787840201/50000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003439577892679743/10000000000000000000 : ℝ) ≤ (10000796395837573/10000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (10003439577892679743/10000000000000000000 : ℝ)^512 ≤ (10000796395837573/10000000000000000 : ℝ)^2211 := by
      have hnat : (10003439577892679743 : ℕ)^512*10000000000000000^2211 ≤ 10000796395837573^2211*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003439577892679743 10000000000000000000 10000796395837573 10000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000796395837573/10000000000000000 : ℝ)) (X := (10003439577892679743/10000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50025909997138957229/50000000000000000000 : ℝ) ≤ (5000599903888407/5000000000000000 : ℝ) ^ (2211/512 : ℝ) := by
    have hpowers : (50025909997138957229/50000000000000000000 : ℝ)^512 ≤ (5000599903888407/5000000000000000 : ℝ)^2211 := by
      have hnat : (50025909997138957229 : ℕ)^512*5000000000000000^2211 ≤ 5000599903888407^2211*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025909997138957229 50000000000000000000 5000599903888407 5000000000000000 512 2211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000599903888407/5000000000000000 : ℝ)) (X := (50025909997138957229/50000000000000000000 : ℝ)) (by norm_num) 2211 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8485781787840201/100000000000000000000 : ℝ) ≤ ((8410529536003041131/8412500000000000000 : ℝ)+2*(403411939241/336500000000000 : ℝ)*(713/6250 : ℝ))^(2211/512 : ℝ) := by
    rw [show (8410529536003041131/8412500000000000000 : ℝ)+2*(403411939241/336500000000000 : ℝ)*(713/6250 : ℝ)=(2500098245974583/2500000000000000 : ℝ) by norm_num, show 1+2*(8485781787840201/100000000000000000000 : ℝ)=(50008485781787840201/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(25909997138957229/100000000000000000000 : ℝ)+(8485781787840201/100000000000000000000 : ℝ) ≤ ((8410529536003041131/8412500000000000000 : ℝ)+(403411939241/336500000000000 : ℝ)*((14773/100000 : ℝ)+(713/6250 : ℝ)))^(2211/512 : ℝ) := by
    rw [show (8410529536003041131/8412500000000000000 : ℝ)+(403411939241/336500000000000 : ℝ)*((14773/100000 : ℝ)+(713/6250 : ℝ))=(10000796395837573/10000000000000000 : ℝ) by norm_num, show 1+(25909997138957229/100000000000000000000 : ℝ)+(8485781787840201/100000000000000000000 : ℝ)=(10003439577892679743/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(25909997138957229/100000000000000000000 : ℝ) ≤ ((8410529536003041131/8412500000000000000 : ℝ)+2*(403411939241/336500000000000 : ℝ)*(14773/100000 : ℝ))^(2211/512 : ℝ) := by
    rw [show (8410529536003041131/8412500000000000000 : ℝ)+2*(403411939241/336500000000000 : ℝ)*(14773/100000 : ℝ)=(5000599903888407/5000000000000000 : ℝ) by norm_num, show 1+2*(25909997138957229/100000000000000000000 : ℝ)=(50025909997138957229/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8410529536003041131/8412500000000000000 : ℝ)*(X 1 0+X 2 0)+(403411939241/336500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (713/6250 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (8410529536003041131/8412500000000000000 : ℝ)) (alpha := (403411939241/336500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8410529536003041131/8412500000000000000 : ℝ)*(X 0 1+X 2 1)+(403411939241/336500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (713/6250 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (8410529536003041131/8412500000000000000 : ℝ)) (alpha := (403411939241/336500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8410529536003041131/8412500000000000000 : ℝ)*(X 0 2+X 1 2)+(403411939241/336500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2211/512 : ℝ)) (lo := (713/6250 : ℝ)) (hi := (14773/100000 : ℝ)) (c := (8410529536003041131/8412500000000000000 : ℝ)) (alpha := (403411939241/336500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-892815899/5000000000 : ℝ)*X 0 0+(2692396633/5000000000 : ℝ)*X 0 1+(5384792997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2643133687/5000000000 : ℝ)*X 1 0+(-960562067/5000000000 : ℝ)*X 1 1+(5384792937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5286267231/10000000000 : ℝ)*X 2 0+(1346198303/2500000000 : ℝ)*X 2 1+(-120070247/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4441581907/10000000000 : ℝ)*X 0 0+(1056692879/2500000000 : ℝ)*X 0 1+(264173207/625000000 : ℝ)*X 0 2+(4441581907/10000000000 : ℝ)*X 1 0+(1056692879/2500000000 : ℝ)*X 1 1+(264173207/625000000 : ℝ)*X 1 2+(4441581907/10000000000 : ℝ)*X 2 0+(1056692879/2500000000 : ℝ)*X 2 1+(264173207/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2104851/10000000 : ℝ)*X 0 0+(1316746053/2500000000 : ℝ)*X 0 1+(329186479/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2684301307/5000000000 : ℝ)*X 1 0+(-984581989/5000000000 : ℝ)*X 1 1+(5266984033/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2684301153/5000000000 : ℝ)*X 2 0+(5266984027/10000000000 : ℝ)*X 2 1+(-492291101/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1037303861/2500000000 : ℝ)*X 0 0+(4372904709/10000000000 : ℝ)*X 0 1+(4372904693/10000000000 : ℝ)*X 0 2+(1037303861/2500000000 : ℝ)*X 1 0+(4372904709/10000000000 : ℝ)*X 1 1+(4372904693/10000000000 : ℝ)*X 1 2+(1037303861/2500000000 : ℝ)*X 2 0+(4372904709/10000000000 : ℝ)*X 2 1+(4372904693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2037542053/10000000000 : ℝ)*X 0 0+(2592674373/5000000000 : ℝ)*X 0 1+(539874473/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276511883/10000000000 : ℝ)*X 1 0+(-1915310073/10000000000 : ℝ)*X 1 1+(43189971/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1319127807/2500000000 : ℝ)*X 2 0+(5398745017/10000000000 : ℝ)*X 2 1+(-1915312817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2237825893/5000000000 : ℝ)*X 0 0+(4209448291/10000000000 : ℝ)*X 0 1+(841890147/2000000000 : ℝ)*X 0 2+(2237825893/5000000000 : ℝ)*X 1 0+(4209448291/10000000000 : ℝ)*X 1 1+(841890147/2000000000 : ℝ)*X 1 2+(2237825893/5000000000 : ℝ)*X 2 0+(4209448291/10000000000 : ℝ)*X 2 1+(841890147/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1853063903/10000000000 : ℝ)*X 0 0+(136611737/250000000 : ℝ)*X 0 1+(5255843713/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2688193741/5000000000 : ℝ)*X 1 0+(-1973608811/10000000000 : ℝ)*X 1 1+(5255843143/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2688193749/5000000000 : ℝ)*X 2 0+(2627921759/5000000000 : ℝ)*X 2 1+(-394721657/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2060558041/5000000000 : ℝ)*X 0 0+(2193356611/5000000000 : ℝ)*X 0 1+(4386713153/10000000000 : ℝ)*X 0 2+(2060558041/5000000000 : ℝ)*X 1 0+(2193356611/5000000000 : ℝ)*X 1 1+(4386713153/10000000000 : ℝ)*X 1 2+(2060558041/5000000000 : ℝ)*X 2 0+(2193356611/5000000000 : ℝ)*X 2 1+(4386713153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1463_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31461/50000 : ℝ) ≤ (-10586162805903239969749270257/16825000000000000000000000000 : ℝ) := by norm_num
    linear_combination (791657/5000000000000 : ℝ)*(upper0) + (30125659/25000000000000 : ℝ)*(upper2) + (189405853/100000000000000 : ℝ)*(upper3) + (31957751/100000000000000 : ℝ)*(lower4) + (527697/12500000000000 : ℝ)*(upper5) + (381709459184377/12500000000000 : ℝ)*(major0) + (381709459184377/12500000000000 : ℝ)*(major1) + (381709459184377/12500000000000 : ℝ)*(major2) + (719596063/25000000000000 : ℝ)*(sp1) + (5631742751/100000000000000 : ℝ)*(sp2) + (421398168704631/10000000000000 : ℝ)*(sp4) + (2106989404331029/50000000000000 : ℝ)*(sp5) + (2106988027651779/50000000000000 : ℝ)*(sp6) + (1914342741242797/100000000000000 : ℝ)*(sp7) + (1914342741242797/100000000000000 : ℝ)*(f.failure) + (421398168704631/10000000000000 : ℝ)*(f.sum) + (19511278137811/4206250000000000000000000000 : ℝ)*base66 + (862847080276129137/105156250000000000000000000000000 : ℝ)*base67 + (804544525797379137/105156250000000000000000000000000 : ℝ)*base69 + (36426238826214613/105156250000000000000000000000000 : ℝ)*base72 + (314556172277531/16825000000000000000000000000 : ℝ)*base73 + (116920635601441637/105156250000000000000000000000000 : ℝ)*base75 + (187586599347620863/105156250000000000000000000000000 : ℝ)*base78 + (4001093910901058363/105156250000000000000000000000000 : ℝ)*base80 + (127860203562169/16825000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (7253657/10000000000000000000000 : ℝ)*base90 + (7253657/10000000000000000000000 : ℝ)*base92 + (7253657/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29591/50000 : ℝ) ≤ (62236110518549197945416760639587/105156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1296563/50000000000000 : ℝ)*(upper3) + (5200819/10000000000000 : ℝ)*(upper4) + (202649/781250000000 : ℝ)*(lower5) + (1563216166778359/50000000000000 : ℝ)*(major0) + (1563216166778359/50000000000000 : ℝ)*(major1) + (1563216166778359/50000000000000 : ℝ)*(major2) + (42731766667471/1000000000000 : ℝ)*(sp0) + (2136578217164941/50000000000000 : ℝ)*(sp1) + (26707326113867/625000000000 : ℝ)*(sp2) + (489987846694309/25000000000000 : ℝ)*(sp3) + (10615177129/100000000000000 : ℝ)*(sp6) + (2348885927/100000000000000 : ℝ)*(sp7) + (1531662187/25000000000000 : ℝ)*(sp8) + (26359065967/100000000000000 : ℝ)*(sp9) + (1959953735663163/100000000000000 : ℝ)*(f.failure) + (534147849174481/12500000000000 : ℝ)*(f.sum) + (25527326463331/8412500000000000000000000000 : ℝ)*base66 + (1468677790506215971/420625000000000000000000000000000 : ℝ)*base68 + (1201227974501284029/420625000000000000000000000000000 : ℝ)*base69 + (3299381956359965971/420625000000000000000000000000000 : ℝ)*base72 + (46951896091519/8412500000000000000000000000 : ℝ)*base73 + (49124558428090971/420625000000000000000000000000000 : ℝ)*base76 + (1788651773700590971/420625000000000000000000000000000 : ℝ)*base78 + (4453747634628090971/420625000000000000000000000000000 : ℝ)*base80 + (41057657602263/16825000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (21442897/10000000000000000000000 : ℝ)*base89 + (21442897/10000000000000000000000 : ℝ)*base91 + (21442897/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40317/50000 : ℝ) ≤ (339176305077917592254491778654691/420625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (169650417/50000000000000 : ℝ)*(upper0) + (95022217/20000000000000 : ℝ)*(upper1) + (1354193213/100000000000000 : ℝ)*(upper2) + (858100974165397/25000000000000 : ℝ)*(major0) + (858100974165397/25000000000000 : ℝ)*(major1) + (3432403896661589/100000000000000 : ℝ)*(major2) + (789228894401/50000000000000 : ℝ)*(sp1) + (504933729337/100000000000000 : ℝ)*(sp2) + (113520865047/25000000000000 : ℝ)*(sp3) + (72594015901/100000000000000 : ℝ)*(sp4) + (4686089789650669/100000000000000 : ℝ)*(sp8) + (4684583925877767/100000000000000 : ℝ)*(sp9) + (292853590621077/6250000000000 : ℝ)*(sp10) + (134457035623393/6250000000000 : ℝ)*(sp11) + (537941663358619/25000000000000 : ℝ)*(f.failure) + (4686162383666569/100000000000000 : ℝ)*(f.sum) + (44955799579893/33650000000000000000000000000 : ℝ)*base66 + (2406268403651749743/210312500000000000000000000000000 : ℝ)*base68 + (825512799460017159/841250000000000000000000000000000 : ℝ)*base69 + (1401844336008937243/210312500000000000000000000000000 : ℝ)*base72 + (693295254275607/33650000000000000000000000000 : ℝ)*base73 + (5533425020778767159/841250000000000000000000000000000 : ℝ)*base75 + (221051955748568493/210312500000000000000000000000000 : ℝ)*base78 + (3549623007723880993/210312500000000000000000000000000 : ℝ)*base80 + (2489030915777/4206250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (28770161/2500000000000000000000 : ℝ)*base89 + (28770161/2500000000000000000000 : ℝ)*base91 + (3770161/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-84811/100000 : ℝ) ≤ (-14269082566900100771367883731/16825000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34374049/100000000000000 : ℝ)*(lower1) + (95883927/50000000000000 : ℝ)*(lower2) + (58517153/100000000000000 : ℝ)*(lower3) + (39112477/100000000000000 : ℝ)*(upper5) + (433781280508253/12500000000000 : ℝ)*(major0) + (433781280508253/12500000000000 : ℝ)*(major1) + (433781280508253/12500000000000 : ℝ)*(major2) + (6458278263/50000000000000 : ℝ)*(sp4) + (236482635273/100000000000000 : ℝ)*(sp5) + (35623699983/25000000000000 : ℝ)*(sp7) + (4793264727885693/100000000000000 : ℝ)*(sp12) + (2396520580903473/50000000000000 : ℝ)*(sp13) + (4793277644442219/100000000000000 : ℝ)*(sp14) + (2175349952786673/100000000000000 : ℝ)*(sp15) + (435098489517321/20000000000000 : ℝ)*(f.failure) + (4793277644442219/100000000000000 : ℝ)*(f.sum) + (13343384155409/16825000000000000000000000000 : ℝ)*base65 + (202628202234533357/105156250000000000000000000000000 : ℝ)*base68 + (26634203569216643/105156250000000000000000000000000 : ℝ)*base69 + (464031796848904143/105156250000000000000000000000000 : ℝ)*base71 + (35310249911867/8412500000000000000000000000 : ℝ)*base73 + (222184192699845857/105156250000000000000000000000000 : ℝ)*base76 + (232317427010779143/105156250000000000000000000000000 : ℝ)*base77 + (758060285386095857/105156250000000000000000000000000 : ℝ)*base80 + (8986414881517/8412500000000000000000000000 : ℝ)*base81 + (9463301/2000000000000000000000 : ℝ)*base90 + (9463301/2000000000000000000000 : ℝ)*base92 + (9463301/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1463_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (713/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31461/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29591/50000 : ℝ) else (40317/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84811/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1463_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1463_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2281/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31461/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29591/50000 : ℝ) else (40317/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84811/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1463_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1463_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1463_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2211/512 : ℝ) ≤ p) (hpb : p ≤ (4423/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (159515619/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2281/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31461/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(29591/50000 : ℝ) else (40317/50000 : ℝ) ≤ X j i ∧ X j i ≤ (84811/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1463_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

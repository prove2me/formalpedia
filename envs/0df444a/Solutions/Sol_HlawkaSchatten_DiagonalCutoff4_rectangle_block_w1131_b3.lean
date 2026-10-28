-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1131_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:26:54.213724+00:00
-- url     : https://prove2.me/submissions/64a5d7e5-c3c2-49c4-9c9e-7bc34c9eafda

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
theorem support_rectangle_w1131_s9_0 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-271520381/1250000000 : ℝ)*x 0 + (674147249/1250000000 : ℝ)*x 1 + (658201293/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271520381/1250000000 : ℝ)^2081 ≤ (1649740030657/12500000000000 : ℝ)^1569 := by
    have hnat : (271520381 : ℕ)^2081*12500000000000^1569 ≤ 1649740030657^1569*1250000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271520381 1250000000 1649740030657 12500000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674147249/1250000000 : ℝ)^2081 ≤ (44089955821787/100000000000000 : ℝ)^1569 := by
    have hnat : (674147249 : ℕ)^2081*100000000000000^1569 ≤ 44089955821787^1569*1250000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674147249 1250000000 44089955821787 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658201293/1250000000 : ℝ)^2081 ≤ (42712123919103/100000000000000 : ℝ)^1569 := by
    have hnat : (658201293 : ℕ)^2081*100000000000000^1569 ≤ 42712123919103^1569*1250000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658201293 1250000000 42712123919103 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-271520381/1250000000 : ℝ), (674147249/1250000000 : ℝ), (658201293/1250000000 : ℝ)] ![(1649740030657/12500000000000 : ℝ), (44089955821787/100000000000000 : ℝ), (42712123919103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-271520381/1250000000 : ℝ)|^2081 ≤ (1649740030657/12500000000000 : ℝ)^1569
        have hw : |(-271520381/1250000000 : ℝ)|=(271520381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674147249/1250000000 : ℝ)|^2081 ≤ (44089955821787/100000000000000 : ℝ)^1569
        have hw : |(674147249/1250000000 : ℝ)|=(674147249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658201293/1250000000 : ℝ)|^2081 ≤ (42712123919103/100000000000000 : ℝ)^1569
        have hw : |(658201293/1250000000 : ℝ)|=(658201293/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s9_1 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672391743/5000000000 : ℝ)*x 0 + (-139804349/625000000 : ℝ)*x 1 + (42124883/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672391743/5000000000 : ℝ)^2081 ≤ (10891497636379/25000000000000 : ℝ)^1569 := by
    have hnat : (2672391743 : ℕ)^2081*25000000000000^1569 ≤ 10891497636379^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672391743 5000000000 10891497636379 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (139804349/625000000 : ℝ)^2081 ≤ (6860942588507/50000000000000 : ℝ)^1569 := by
    have hnat : (139804349 : ℕ)^2081*50000000000000^1569 ≤ 6860942588507^1569*625000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139804349 625000000 6860942588507 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42124883/80000000 : ℝ)^2081 ≤ (5339015531577/12500000000000 : ℝ)^1569 := by
    have hnat : (42124883 : ℕ)^2081*12500000000000^1569 ≤ 5339015531577^1569*80000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42124883 80000000 5339015531577 12500000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672391743/5000000000 : ℝ), (-139804349/625000000 : ℝ), (42124883/80000000 : ℝ)] ![(10891497636379/25000000000000 : ℝ), (6860942588507/50000000000000 : ℝ), (5339015531577/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672391743/5000000000 : ℝ)|^2081 ≤ (10891497636379/25000000000000 : ℝ)^1569
        have hw : |(2672391743/5000000000 : ℝ)|=(2672391743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-139804349/625000000 : ℝ)|^2081 ≤ (6860942588507/50000000000000 : ℝ)^1569
        have hw : |(-139804349/625000000 : ℝ)|=(139804349/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42124883/80000000 : ℝ)|^2081 ≤ (5339015531577/12500000000000 : ℝ)^1569
        have hw : |(42124883/80000000 : ℝ)|=(42124883/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s9_2 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336195871/2500000000 : ℝ)*x 0 + (526561031/1000000000 : ℝ)*x 1 + (-89474787/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336195871/2500000000 : ℝ)^2081 ≤ (21782995261947/50000000000000 : ℝ)^1569 := by
    have hnat : (1336195871 : ℕ)^2081*50000000000000^1569 ≤ 21782995261947^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336195871 2500000000 21782995261947 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526561031/1000000000 : ℝ)^2081 ≤ (21356061776657/50000000000000 : ℝ)^1569 := by
    have hnat : (526561031 : ℕ)^2081*50000000000000^1569 ≤ 21356061776657^1569*1000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526561031 1000000000 21356061776657 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89474787/400000000 : ℝ)^2081 ≤ (1372188591741/10000000000000 : ℝ)^1569 := by
    have hnat : (89474787 : ℕ)^2081*10000000000000^1569 ≤ 1372188591741^1569*400000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89474787 400000000 1372188591741 10000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336195871/2500000000 : ℝ), (526561031/1000000000 : ℝ), (-89474787/400000000 : ℝ)] ![(21782995261947/50000000000000 : ℝ), (21356061776657/50000000000000 : ℝ), (1372188591741/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336195871/2500000000 : ℝ)|^2081 ≤ (21782995261947/50000000000000 : ℝ)^1569
        have hw : |(1336195871/2500000000 : ℝ)|=(1336195871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526561031/1000000000 : ℝ)|^2081 ≤ (21356061776657/50000000000000 : ℝ)^1569
        have hw : |(526561031/1000000000 : ℝ)|=(526561031/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-89474787/400000000 : ℝ)|^2081 ≤ (1372188591741/10000000000000 : ℝ)^1569
        have hw : |(-89474787/400000000 : ℝ)|=(89474787/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s9_3 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4366227769/10000000000 : ℝ)*x 0 + (4241436783/10000000000 : ℝ)*x 1 + (2247341077/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366227769/10000000000 : ℝ)^2081 ≤ (33316932164911/100000000000000 : ℝ)^1569 := by
    have hnat : (4366227769 : ℕ)^2081*100000000000000^1569 ≤ 33316932164911^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366227769 10000000000 33316932164911 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4241436783/10000000000 : ℝ)^2081 ≤ (3205989601499/10000000000000 : ℝ)^1569 := by
    have hnat : (4241436783 : ℕ)^2081*10000000000000^1569 ≤ 3205989601499^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241436783 10000000000 3205989601499 10000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247341077/5000000000 : ℝ)^2081 ≤ (17311585905509/50000000000000 : ℝ)^1569 := by
    have hnat : (2247341077 : ℕ)^2081*50000000000000^1569 ≤ 17311585905509^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247341077 5000000000 17311585905509 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366227769/10000000000 : ℝ), (4241436783/10000000000 : ℝ), (2247341077/5000000000 : ℝ)] ![(33316932164911/100000000000000 : ℝ), (3205989601499/10000000000000 : ℝ), (17311585905509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366227769/10000000000 : ℝ)|^2081 ≤ (33316932164911/100000000000000 : ℝ)^1569
        have hw : |(4366227769/10000000000 : ℝ)|=(4366227769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4241436783/10000000000 : ℝ)|^2081 ≤ (3205989601499/10000000000000 : ℝ)^1569
        have hw : |(4241436783/10000000000 : ℝ)|=(4241436783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247341077/5000000000 : ℝ)|^2081 ≤ (17311585905509/50000000000000 : ℝ)^1569
        have hw : |(2247341077/5000000000 : ℝ)|=(2247341077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s9_4 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2172167739/10000000000 : ℝ)*x 0 + (2632964921/5000000000 : ℝ)*x 1 + (337053593/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2172167739/10000000000 : ℝ)^2081 ≤ (1319795804839/10000000000000 : ℝ)^1569 := by
    have hnat : (2172167739 : ℕ)^2081*10000000000000^1569 ≤ 1319795804839^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172167739 10000000000 1319795804839 10000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632964921/5000000000 : ℝ)^2081 ≤ (21357780635637/50000000000000 : ℝ)^1569 := by
    have hnat : (2632964921 : ℕ)^2081*50000000000000^1569 ≤ 21357780635637^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632964921 5000000000 21357780635637 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337053593/625000000 : ℝ)^2081 ≤ (44086480673911/100000000000000 : ℝ)^1569 := by
    have hnat : (337053593 : ℕ)^2081*100000000000000^1569 ≤ 44086480673911^1569*625000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337053593 625000000 44086480673911 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2172167739/10000000000 : ℝ), (2632964921/5000000000 : ℝ), (337053593/625000000 : ℝ)] ![(1319795804839/10000000000000 : ℝ), (21357780635637/50000000000000 : ℝ), (44086480673911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2172167739/10000000000 : ℝ)|^2081 ≤ (1319795804839/10000000000000 : ℝ)^1569
        have hw : |(-2172167739/10000000000 : ℝ)|=(2172167739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632964921/5000000000 : ℝ)|^2081 ≤ (21357780635637/50000000000000 : ℝ)^1569
        have hw : |(2632964921/5000000000 : ℝ)|=(2632964921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337053593/625000000 : ℝ)|^2081 ≤ (44086480673911/100000000000000 : ℝ)^1569
        have hw : |(337053593/625000000 : ℝ)|=(337053593/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_s9_5 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2183118937/5000000000 : ℝ)*x 0 + (2247023147/5000000000 : ℝ)*x 1 + (2121037279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183118937/5000000000 : ℝ)^2081 ≤ (8329258608491/25000000000000 : ℝ)^1569 := by
    have hnat : (2183118937 : ℕ)^2081*25000000000000^1569 ≤ 8329258608491^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183118937 5000000000 8329258608491 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247023147/5000000000 : ℝ)^2081 ≤ (17308337737483/50000000000000 : ℝ)^1569 := by
    have hnat : (2247023147 : ℕ)^2081*50000000000000^1569 ≤ 17308337737483^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247023147 5000000000 17308337737483 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2121037279/5000000000 : ℝ)^2081 ≤ (32066290070373/100000000000000 : ℝ)^1569 := by
    have hnat : (2121037279 : ℕ)^2081*100000000000000^1569 ≤ 32066290070373^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121037279 5000000000 32066290070373 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183118937/5000000000 : ℝ), (2247023147/5000000000 : ℝ), (2121037279/5000000000 : ℝ)] ![(8329258608491/25000000000000 : ℝ), (17308337737483/50000000000000 : ℝ), (32066290070373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183118937/5000000000 : ℝ)|^2081 ≤ (8329258608491/25000000000000 : ℝ)^1569
        have hw : |(2183118937/5000000000 : ℝ)|=(2183118937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247023147/5000000000 : ℝ)|^2081 ≤ (17308337737483/50000000000000 : ℝ)^1569
        have hw : |(2247023147/5000000000 : ℝ)|=(2247023147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2121037279/5000000000 : ℝ)|^2081 ≤ (32066290070373/100000000000000 : ℝ)^1569
        have hw : |(2121037279/5000000000 : ℝ)|=(2121037279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1131_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (567/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7021/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7021/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7021/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11339/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7021/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7021/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11339/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7021/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11339/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7021/50000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (11339/100000 : ℝ) ^ (8323/2048 : ℝ) ≤ (14382190705335633/100000000000000000000 : ℝ) := by
    have hpowers : (11339/100000 : ℝ)^8323 ≤ (14382190705335633/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11339 : ℕ)^8323*100000000000000000000^2048 ≤ 14382190705335633^2048*100000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11339 100000 14382190705335633 100000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11339/100000 : ℝ)) (X := (14382190705335633/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7021/50000 : ℝ) ^ (8323/2048 : ℝ) ≤ (8572772734434173/25000000000000000000 : ℝ) := by
    have hpowers : (7021/50000 : ℝ)^8323 ≤ (8572772734434173/25000000000000000000 : ℝ)^2048 := by
      have hnat : (7021 : ℕ)^8323*25000000000000000000^2048 ≤ 8572772734434173^2048*50000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7021 50000 8572772734434173 25000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7021/50000 : ℝ)) (X := (8572772734434173/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014382190705335633/50000000000000000000 : ℝ) ≤ (5000353857181981/5000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (50014382190705335633/50000000000000000000 : ℝ)^2048 ≤ (5000353857181981/5000000000000000 : ℝ)^8323 := by
      have hnat : (50014382190705335633 : ℕ)^2048*5000000000000000^8323 ≤ 5000353857181981^8323*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014382190705335633 50000000000000000000 5000353857181981 5000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000353857181981/5000000000000000 : ℝ)) (X := (50014382190705335633/50000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001946931265722893/4000000000000000000 : ℝ) ≤ (500059873000091/500000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (4001946931265722893/4000000000000000000 : ℝ)^2048 ≤ (500059873000091/500000000000000 : ℝ)^8323 := by
      have hnat : (4001946931265722893 : ℕ)^2048*500000000000000^8323 ≤ 500059873000091^8323*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001946931265722893 4000000000000000000 500059873000091 500000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500059873000091/500000000000000 : ℝ)) (X := (4001946931265722893/4000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508572772734434173/12500000000000000000 : ℝ) ≤ (5000843602819839/5000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (12508572772734434173/12500000000000000000 : ℝ)^2048 ≤ (5000843602819839/5000000000000000 : ℝ)^8323 := by
      have hnat : (12508572772734434173 : ℕ)^2048*5000000000000000^8323 ≤ 5000843602819839^8323*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508572772734434173 12500000000000000000 5000843602819839 5000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000843602819839/5000000000000000 : ℝ)) (X := (12508572772734434173/12500000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14382190705335633/100000000000000000000 : ℝ) ≤ ((794729602951483693/795000000000000000 : ℝ)+2*(244872818929/135150000000000 : ℝ)*(11339/100000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (794729602951483693/795000000000000000 : ℝ)+2*(244872818929/135150000000000 : ℝ)*(11339/100000 : ℝ)=(5000353857181981/5000000000000000 : ℝ) by norm_num, show 1+2*(14382190705335633/100000000000000000000 : ℝ)=(50014382190705335633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8572772734434173/25000000000000000000 : ℝ)+(14382190705335633/100000000000000000000 : ℝ) ≤ ((794729602951483693/795000000000000000 : ℝ)+(244872818929/135150000000000 : ℝ)*((7021/50000 : ℝ)+(11339/100000 : ℝ)))^(8323/2048 : ℝ) := by
    rw [show (794729602951483693/795000000000000000 : ℝ)+(244872818929/135150000000000 : ℝ)*((7021/50000 : ℝ)+(11339/100000 : ℝ))=(500059873000091/500000000000000 : ℝ) by norm_num, show 1+(8572772734434173/25000000000000000000 : ℝ)+(14382190705335633/100000000000000000000 : ℝ)=(4001946931265722893/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8572772734434173/25000000000000000000 : ℝ) ≤ ((794729602951483693/795000000000000000 : ℝ)+2*(244872818929/135150000000000 : ℝ)*(7021/50000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (794729602951483693/795000000000000000 : ℝ)+2*(244872818929/135150000000000 : ℝ)*(7021/50000 : ℝ)=(5000843602819839/5000000000000000 : ℝ) by norm_num, show 1+2*(8572772734434173/25000000000000000000 : ℝ)=(12508572772734434173/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (794729602951483693/795000000000000000 : ℝ)*(X 1 0+X 2 0)+(244872818929/135150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (11339/100000 : ℝ)) (hi := (7021/50000 : ℝ)) (c := (794729602951483693/795000000000000000 : ℝ)) (alpha := (244872818929/135150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (794729602951483693/795000000000000000 : ℝ)*(X 0 1+X 2 1)+(244872818929/135150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (11339/100000 : ℝ)) (hi := (7021/50000 : ℝ)) (c := (794729602951483693/795000000000000000 : ℝ)) (alpha := (244872818929/135150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (794729602951483693/795000000000000000 : ℝ)*(X 0 2+X 1 2)+(244872818929/135150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (11339/100000 : ℝ)) (hi := (7021/50000 : ℝ)) (c := (794729602951483693/795000000000000000 : ℝ)) (alpha := (244872818929/135150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-271520381/1250000000 : ℝ)*X 0 0+(674147249/1250000000 : ℝ)*X 0 1+(658201293/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672391743/5000000000 : ℝ)*X 1 0+(-139804349/625000000 : ℝ)*X 1 1+(42124883/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336195871/2500000000 : ℝ)*X 2 0+(526561031/1000000000 : ℝ)*X 2 1+(-89474787/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4366227769/10000000000 : ℝ)*X 0 0+(4241436783/10000000000 : ℝ)*X 0 1+(2247341077/5000000000 : ℝ)*X 0 2+(4366227769/10000000000 : ℝ)*X 1 0+(4241436783/10000000000 : ℝ)*X 1 1+(2247341077/5000000000 : ℝ)*X 1 2+(4366227769/10000000000 : ℝ)*X 2 0+(4241436783/10000000000 : ℝ)*X 2 1+(2247341077/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2172167739/10000000000 : ℝ)*X 0 0+(2632964921/5000000000 : ℝ)*X 0 1+(337053593/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2183118937/5000000000 : ℝ)*X 0 0+(2247023147/5000000000 : ℝ)*X 0 1+(2121037279/5000000000 : ℝ)*X 0 2+(2183118937/5000000000 : ℝ)*X 1 0+(2247023147/5000000000 : ℝ)*X 1 1+(2121037279/5000000000 : ℝ)*X 1 2+(2183118937/5000000000 : ℝ)*X 2 0+(2247023147/5000000000 : ℝ)*X 2 1+(2121037279/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (371606870729558787069038961/112625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2257677/400000000000 : ℝ)*(base19) + (75700047/12500000000000 : ℝ)*(base23) + (16423259/50000000000000 : ℝ)*(lower2) + (22395517/20000000000000 : ℝ)*(upper3) + (2821237/5000000000000 : ℝ)*(lower4) + (2946943551945927/50000000000000 : ℝ)*(major0) + (2946943551945927/50000000000000 : ℝ)*(major1) + (2946943551945927/50000000000000 : ℝ)*(major2) + (1567799691836807/20000000000000 : ℝ)*(sp0) + (1567802400885327/20000000000000 : ℝ)*(sp1) + (783901196324551/10000000000000 : ℝ)*(sp2) + (1974374750297259/50000000000000 : ℝ)*(sp3) + (14109661851/100000000000000 : ℝ)*(sp4) + (12028359761/100000000000000 : ℝ)*(sp5) + (3948761528954279/100000000000000 : ℝ)*(f.failure) + (1567802513769177/20000000000000 : ℝ)*(f.sum) + (16642865770309/4505000000000000000000000000 : ℝ)*base65 + (3416894139894545671/225250000000000000000000000000000 : ℝ)*base68 + (547635796731545671/225250000000000000000000000000000 : ℝ)*base70 + (586889512363545671/225250000000000000000000000000000 : ℝ)*base72 + (144096058201/1126250000000000000000000000 : ℝ)*base73 + (1082241848505795671/225250000000000000000000000000000 : ℝ)*base76 + (415385790921045671/225250000000000000000000000000000 : ℝ)*base78 + (5436844426654045671/225250000000000000000000000000000 : ℝ)*base80 + (432343099889/1126250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (9331727/1000000000000000000000 : ℝ)*base89 + (9331727/1000000000000000000000 : ℝ)*base91 + (9331727/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1131_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (567/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1131_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1131_box_0 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2044904963/10000000000 : ℝ)*x 0 + (5376465389/10000000000 : ℝ)*x 1 + (2688232819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2044904963/10000000000 : ℝ)^2081 ≤ (12182327265597/100000000000000 : ℝ)^1569 := by
    have hnat : (2044904963 : ℕ)^2081*100000000000000^1569 ≤ 12182327265597^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2044904963 10000000000 12182327265597 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376465389/10000000000 : ℝ)^2081 ≤ (5488604376517/12500000000000 : ℝ)^1569 := by
    have hnat : (5376465389 : ℕ)^2081*12500000000000^1569 ≤ 5488604376517^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376465389 10000000000 5488604376517 12500000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688232819/5000000000 : ℝ)^2081 ≤ (43908837709277/100000000000000 : ℝ)^1569 := by
    have hnat : (2688232819 : ℕ)^2081*100000000000000^1569 ≤ 43908837709277^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688232819 5000000000 43908837709277 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2044904963/10000000000 : ℝ), (5376465389/10000000000 : ℝ), (2688232819/5000000000 : ℝ)] ![(12182327265597/100000000000000 : ℝ), (5488604376517/12500000000000 : ℝ), (43908837709277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2044904963/10000000000 : ℝ)|^2081 ≤ (12182327265597/100000000000000 : ℝ)^1569
        have hw : |(-2044904963/10000000000 : ℝ)|=(2044904963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376465389/10000000000 : ℝ)|^2081 ≤ (5488604376517/12500000000000 : ℝ)^1569
        have hw : |(5376465389/10000000000 : ℝ)|=(5376465389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688232819/5000000000 : ℝ)|^2081 ≤ (43908837709277/100000000000000 : ℝ)^1569
        have hw : |(2688232819/5000000000 : ℝ)|=(2688232819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_box_1 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1323970683/2500000000 : ℝ)*x 0 + (-2154162147/10000000000 : ℝ)*x 1 + (84007267/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323970683/2500000000 : ℝ)^2081 ≤ (43038114410023/100000000000000 : ℝ)^1569 := by
    have hnat : (1323970683 : ℕ)^2081*100000000000000^1569 ≤ 43038114410023^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323970683 2500000000 43038114410023 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2154162147/10000000000 : ℝ)^2081 ≤ (13053053821283/100000000000000 : ℝ)^1569 := by
    have hnat : (2154162147 : ℕ)^2081*100000000000000^1569 ≤ 13053053821283^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154162147 10000000000 13053053821283 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84007267/156250000 : ℝ)^2081 ≤ (21954415875869/50000000000000 : ℝ)^1569 := by
    have hnat : (84007267 : ℕ)^2081*50000000000000^1569 ≤ 21954415875869^1569*156250000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84007267 156250000 21954415875869 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323970683/2500000000 : ℝ), (-2154162147/10000000000 : ℝ), (84007267/156250000 : ℝ)] ![(43038114410023/100000000000000 : ℝ), (13053053821283/100000000000000 : ℝ), (21954415875869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323970683/2500000000 : ℝ)|^2081 ≤ (43038114410023/100000000000000 : ℝ)^1569
        have hw : |(1323970683/2500000000 : ℝ)|=(1323970683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2154162147/10000000000 : ℝ)|^2081 ≤ (13053053821283/100000000000000 : ℝ)^1569
        have hw : |(-2154162147/10000000000 : ℝ)|=(2154162147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84007267/156250000 : ℝ)|^2081 ≤ (21954415875869/50000000000000 : ℝ)^1569
        have hw : |(84007267/156250000 : ℝ)|=(84007267/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_box_2 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2647940969/5000000000 : ℝ)*x 0 + (5376465819/10000000000 : ℝ)*x 1 + (-2154162227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647940969/5000000000 : ℝ)^2081 ≤ (21519052925891/50000000000000 : ℝ)^1569 := by
    have hnat : (2647940969 : ℕ)^2081*50000000000000^1569 ≤ 21519052925891^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647940969 5000000000 21519052925891 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376465819/10000000000 : ℝ)^2081 ≤ (43908839669849/100000000000000 : ℝ)^1569 := by
    have hnat : (5376465819 : ℕ)^2081*100000000000000^1569 ≤ 43908839669849^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376465819 10000000000 43908839669849 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2154162227/10000000000 : ℝ)^2081 ≤ (13053054464227/100000000000000 : ℝ)^1569 := by
    have hnat : (2154162227 : ℕ)^2081*100000000000000^1569 ≤ 13053054464227^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154162227 10000000000 13053054464227 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647940969/5000000000 : ℝ), (5376465819/10000000000 : ℝ), (-2154162227/10000000000 : ℝ)] ![(21519052925891/50000000000000 : ℝ), (43908839669849/100000000000000 : ℝ), (13053054464227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647940969/5000000000 : ℝ)|^2081 ≤ (21519052925891/50000000000000 : ℝ)^1569
        have hw : |(2647940969/5000000000 : ℝ)|=(2647940969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376465819/10000000000 : ℝ)|^2081 ≤ (43908839669849/100000000000000 : ℝ)^1569
        have hw : |(5376465819/10000000000 : ℝ)|=(5376465819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2154162227/10000000000 : ℝ)|^2081 ≤ (13053054464227/100000000000000 : ℝ)^1569
        have hw : |(-2154162227/10000000000 : ℝ)|=(2154162227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_box_3 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (559235999/1250000000 : ℝ)*x 0 + (107862829/250000000 : ℝ)*x 1 + (2157256341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (559235999/1250000000 : ℝ)^2081 ≤ (2150680094969/6250000000000 : ℝ)^1569 := by
    have hnat : (559235999 : ℕ)^2081*6250000000000^1569 ≤ 2150680094969^1569*1250000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559235999 1250000000 2150680094969 6250000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107862829/250000000 : ℝ)^2081 ≤ (1639728082401/5000000000000 : ℝ)^1569 := by
    have hnat : (107862829 : ℕ)^2081*5000000000000^1569 ≤ 1639728082401^1569*250000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107862829 250000000 1639728082401 5000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2157256341/5000000000 : ℝ)^2081 ≤ (3279455682913/10000000000000 : ℝ)^1569 := by
    have hnat : (2157256341 : ℕ)^2081*10000000000000^1569 ≤ 3279455682913^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157256341 5000000000 3279455682913 10000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(559235999/1250000000 : ℝ), (107862829/250000000 : ℝ), (2157256341/5000000000 : ℝ)] ![(2150680094969/6250000000000 : ℝ), (1639728082401/5000000000000 : ℝ), (3279455682913/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(559235999/1250000000 : ℝ)|^2081 ≤ (2150680094969/6250000000000 : ℝ)^1569
        have hw : |(559235999/1250000000 : ℝ)|=(559235999/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107862829/250000000 : ℝ)|^2081 ≤ (1639728082401/5000000000000 : ℝ)^1569
        have hw : |(107862829/250000000 : ℝ)|=(107862829/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2157256341/5000000000 : ℝ)|^2081 ≤ (3279455682913/10000000000000 : ℝ)^1569
        have hw : |(2157256341/5000000000 : ℝ)|=(2157256341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_box_4 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2300799011/10000000000 : ℝ)*x 0 + (1056200149/2000000000 : ℝ)*x 1 + (660125099/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2300799011/10000000000 : ℝ)^2081 ≤ (7122219327841/50000000000000 : ℝ)^1569 := by
    have hnat : (2300799011 : ℕ)^2081*50000000000000^1569 ≤ 7122219327841^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2300799011 10000000000 7122219327841 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056200149/2000000000 : ℝ)^2081 ≤ (42877780406249/100000000000000 : ℝ)^1569 := by
    have hnat : (1056200149 : ℕ)^2081*100000000000000^1569 ≤ 42877780406249^1569*2000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056200149 2000000000 42877780406249 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660125099/1250000000 : ℝ)^2081 ≤ (2143889045619/5000000000000 : ℝ)^1569 := by
    have hnat : (660125099 : ℕ)^2081*5000000000000^1569 ≤ 2143889045619^1569*1250000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660125099 1250000000 2143889045619 5000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2300799011/10000000000 : ℝ), (1056200149/2000000000 : ℝ), (660125099/1250000000 : ℝ)] ![(7122219327841/50000000000000 : ℝ), (42877780406249/100000000000000 : ℝ), (2143889045619/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2300799011/10000000000 : ℝ)|^2081 ≤ (7122219327841/50000000000000 : ℝ)^1569
        have hw : |(-2300799011/10000000000 : ℝ)|=(2300799011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056200149/2000000000 : ℝ)|^2081 ≤ (42877780406249/100000000000000 : ℝ)^1569
        have hw : |(1056200149/2000000000 : ℝ)|=(1056200149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660125099/1250000000 : ℝ)|^2081 ≤ (2143889045619/5000000000000 : ℝ)^1569
        have hw : |(660125099/1250000000 : ℝ)|=(660125099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_box_5 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5363344929/10000000000 : ℝ)*x 0 + (-273960277/1250000000 : ℝ)*x 1 + (5281000633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363344929/10000000000 : ℝ)^2081 ≤ (43766772265931/100000000000000 : ℝ)^1569 := by
    have hnat : (5363344929 : ℕ)^2081*100000000000000^1569 ≤ 43766772265931^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363344929 10000000000 43766772265931 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273960277/1250000000 : ℝ)^2081 ≤ (834715532671/6250000000000 : ℝ)^1569 := by
    have hnat : (273960277 : ℕ)^2081*6250000000000^1569 ≤ 834715532671^1569*1250000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273960277 1250000000 834715532671 6250000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281000633/10000000000 : ℝ)^2081 ≤ (42877779200149/100000000000000 : ℝ)^1569 := by
    have hnat : (5281000633 : ℕ)^2081*100000000000000^1569 ≤ 42877779200149^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281000633 10000000000 42877779200149 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363344929/10000000000 : ℝ), (-273960277/1250000000 : ℝ), (5281000633/10000000000 : ℝ)] ![(43766772265931/100000000000000 : ℝ), (834715532671/6250000000000 : ℝ), (42877779200149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363344929/10000000000 : ℝ)|^2081 ≤ (43766772265931/100000000000000 : ℝ)^1569
        have hw : |(5363344929/10000000000 : ℝ)|=(5363344929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273960277/1250000000 : ℝ)|^2081 ≤ (834715532671/6250000000000 : ℝ)^1569
        have hw : |(-273960277/1250000000 : ℝ)|=(273960277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281000633/10000000000 : ℝ)|^2081 ≤ (42877779200149/100000000000000 : ℝ)^1569
        have hw : |(5281000633/10000000000 : ℝ)|=(5281000633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_box_6 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2681672409/5000000000 : ℝ)*x 0 + (1056200153/2000000000 : ℝ)*x 1 + (-2191682189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681672409/5000000000 : ℝ)^2081 ≤ (875335421291/2000000000000 : ℝ)^1569 := by
    have hnat : (2681672409 : ℕ)^2081*2000000000000^1569 ≤ 875335421291^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681672409 5000000000 875335421291 2000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056200153/2000000000 : ℝ)^2081 ≤ (5359722577703/12500000000000 : ℝ)^1569 := by
    have hnat : (1056200153 : ℕ)^2081*12500000000000^1569 ≤ 5359722577703^1569*2000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056200153 2000000000 5359722577703 12500000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2191682189/10000000000 : ℝ)^2081 ≤ (3338862076129/25000000000000 : ℝ)^1569 := by
    have hnat : (2191682189 : ℕ)^2081*25000000000000^1569 ≤ 3338862076129^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191682189 10000000000 3338862076129 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681672409/5000000000 : ℝ), (1056200153/2000000000 : ℝ), (-2191682189/10000000000 : ℝ)] ![(875335421291/2000000000000 : ℝ), (5359722577703/12500000000000 : ℝ), (3338862076129/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681672409/5000000000 : ℝ)|^2081 ≤ (875335421291/2000000000000 : ℝ)^1569
        have hw : |(2681672409/5000000000 : ℝ)|=(2681672409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056200153/2000000000 : ℝ)|^2081 ≤ (5359722577703/12500000000000 : ℝ)^1569
        have hw : |(1056200153/2000000000 : ℝ)|=(1056200153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2191682189/10000000000 : ℝ)|^2081 ≤ (3338862076129/25000000000000 : ℝ)^1569
        have hw : |(-2191682189/10000000000 : ℝ)|=(2191682189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_box_7 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4258210831/10000000000 : ℝ)*x 0 + (2211165251/5000000000 : ℝ)*x 1 + (2211165327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4258210831/10000000000 : ℝ)^2081 ≤ (16114084815607/50000000000000 : ℝ)^1569 := by
    have hnat : (4258210831 : ℕ)^2081*50000000000000^1569 ≤ 16114084815607^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4258210831 10000000000 16114084815607 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2211165251/5000000000 : ℝ)^2081 ≤ (16942957201369/50000000000000 : ℝ)^1569 := by
    have hnat : (2211165251 : ℕ)^2081*50000000000000^1569 ≤ 16942957201369^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211165251 5000000000 16942957201369 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2211165327/5000000000 : ℝ)^2081 ≤ (33885915947497/100000000000000 : ℝ)^1569 := by
    have hnat : (2211165327 : ℕ)^2081*100000000000000^1569 ≤ 33885915947497^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211165327 5000000000 33885915947497 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4258210831/10000000000 : ℝ), (2211165251/5000000000 : ℝ), (2211165327/5000000000 : ℝ)] ![(16114084815607/50000000000000 : ℝ), (16942957201369/50000000000000 : ℝ), (33885915947497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4258210831/10000000000 : ℝ)|^2081 ≤ (16114084815607/50000000000000 : ℝ)^1569
        have hw : |(4258210831/10000000000 : ℝ)|=(4258210831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2211165251/5000000000 : ℝ)|^2081 ≤ (16942957201369/50000000000000 : ℝ)^1569
        have hw : |(2211165251/5000000000 : ℝ)|=(2211165251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2211165327/5000000000 : ℝ)|^2081 ≤ (33885915947497/100000000000000 : ℝ)^1569
        have hw : |(2211165327/5000000000 : ℝ)|=(2211165327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_box_8 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-561825089/2500000000 : ℝ)*x 0 + (2608048231/5000000000 : ℝ)*x 1 + (5386073129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (561825089/2500000000 : ℝ)^2081 ≤ (107865755089/781250000000 : ℝ)^1569 := by
    have hnat : (561825089 : ℕ)^2081*781250000000^1569 ≤ 107865755089^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561825089 2500000000 107865755089 781250000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608048231/5000000000 : ℝ)^2081 ≤ (42180248006841/100000000000000 : ℝ)^1569 := by
    have hnat : (2608048231 : ℕ)^2081*100000000000000^1569 ≤ 42180248006841^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608048231 5000000000 42180248006841 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386073129/10000000000 : ℝ)^2081 ≤ (11003233828947/25000000000000 : ℝ)^1569 := by
    have hnat : (5386073129 : ℕ)^2081*25000000000000^1569 ≤ 11003233828947^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386073129 10000000000 11003233828947 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-561825089/2500000000 : ℝ), (2608048231/5000000000 : ℝ), (5386073129/10000000000 : ℝ)] ![(107865755089/781250000000 : ℝ), (42180248006841/100000000000000 : ℝ), (11003233828947/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-561825089/2500000000 : ℝ)|^2081 ≤ (107865755089/781250000000 : ℝ)^1569
        have hw : |(-561825089/2500000000 : ℝ)|=(561825089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608048231/5000000000 : ℝ)|^2081 ≤ (42180248006841/100000000000000 : ℝ)^1569
        have hw : |(2608048231/5000000000 : ℝ)|=(2608048231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386073129/10000000000 : ℝ)|^2081 ≤ (11003233828947/25000000000000 : ℝ)^1569
        have hw : |(5386073129/10000000000 : ℝ)|=(5386073129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_box_9 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5289089407/10000000000 : ℝ)*x 0 + (-1075158363/5000000000 : ℝ)*x 1 + (1346518277/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289089407/10000000000 : ℝ)^2081 ≤ (10741226731859/25000000000000 : ℝ)^1569 := by
    have hnat : (5289089407 : ℕ)^2081*25000000000000^1569 ≤ 10741226731859^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289089407 10000000000 10741226731859 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075158363/5000000000 : ℝ)^2081 ≤ (13022157967113/100000000000000 : ℝ)^1569 := by
    have hnat : (1075158363 : ℕ)^2081*100000000000000^1569 ≤ 13022157967113^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075158363 5000000000 13022157967113 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346518277/2500000000 : ℝ)^2081 ≤ (22006467544093/50000000000000 : ℝ)^1569 := by
    have hnat : (1346518277 : ℕ)^2081*50000000000000^1569 ≤ 22006467544093^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346518277 2500000000 22006467544093 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289089407/10000000000 : ℝ), (-1075158363/5000000000 : ℝ), (1346518277/2500000000 : ℝ)] ![(10741226731859/25000000000000 : ℝ), (13022157967113/100000000000000 : ℝ), (22006467544093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289089407/10000000000 : ℝ)|^2081 ≤ (10741226731859/25000000000000 : ℝ)^1569
        have hw : |(5289089407/10000000000 : ℝ)|=(5289089407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1075158363/5000000000 : ℝ)|^2081 ≤ (13022157967113/100000000000000 : ℝ)^1569
        have hw : |(-1075158363/5000000000 : ℝ)|=(1075158363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346518277/2500000000 : ℝ)|^2081 ≤ (22006467544093/50000000000000 : ℝ)^1569
        have hw : |(1346518277/2500000000 : ℝ)|=(1346518277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_box_10 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1322272343/2500000000 : ℝ)*x 0 + (1077214641/2000000000 : ℝ)*x 1 + (-2150316641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322272343/2500000000 : ℝ)^2081 ≤ (21482453275171/50000000000000 : ℝ)^1569 := by
    have hnat : (1322272343 : ℕ)^2081*50000000000000^1569 ≤ 21482453275171^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322272343 2500000000 21482453275171 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077214641/2000000000 : ℝ)^2081 ≤ (44012936139491/100000000000000 : ℝ)^1569 := by
    have hnat : (1077214641 : ℕ)^2081*100000000000000^1569 ≤ 44012936139491^1569*2000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077214641 2000000000 44012936139491 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2150316641/10000000000 : ℝ)^2081 ≤ (13022157284383/100000000000000 : ℝ)^1569 := by
    have hnat : (2150316641 : ℕ)^2081*100000000000000^1569 ≤ 13022157284383^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150316641 10000000000 13022157284383 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322272343/2500000000 : ℝ), (1077214641/2000000000 : ℝ), (-2150316641/10000000000 : ℝ)] ![(21482453275171/50000000000000 : ℝ), (44012936139491/100000000000000 : ℝ), (13022157284383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322272343/2500000000 : ℝ)|^2081 ≤ (21482453275171/50000000000000 : ℝ)^1569
        have hw : |(1322272343/2500000000 : ℝ)|=(1322272343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1077214641/2000000000 : ℝ)|^2081 ≤ (44012936139491/100000000000000 : ℝ)^1569
        have hw : |(1077214641/2000000000 : ℝ)|=(1077214641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2150316641/10000000000 : ℝ)|^2081 ≤ (13022157284383/100000000000000 : ℝ)^1569
        have hw : |(-2150316641/10000000000 : ℝ)|=(2150316641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_box_11 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (899064057/2000000000 : ℝ)*x 0 + (4303656213/10000000000 : ℝ)*x 1 + (1075914071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (899064057/2000000000 : ℝ)^2081 ≤ (34629691650517/100000000000000 : ℝ)^1569 := by
    have hnat : (899064057 : ℕ)^2081*100000000000000^1569 ≤ 34629691650517^1569*2000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899064057 2000000000 34629691650517 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4303656213/10000000000 : ℝ)^2081 ≤ (32685153809417/100000000000000 : ℝ)^1569 := by
    have hnat : (4303656213 : ℕ)^2081*100000000000000^1569 ≤ 32685153809417^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303656213 10000000000 32685153809417 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075914071/2500000000 : ℝ)^2081 ≤ (6537030904921/20000000000000 : ℝ)^1569 := by
    have hnat : (1075914071 : ℕ)^2081*20000000000000^1569 ≤ 6537030904921^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075914071 2500000000 6537030904921 20000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(899064057/2000000000 : ℝ), (4303656213/10000000000 : ℝ), (1075914071/2500000000 : ℝ)] ![(34629691650517/100000000000000 : ℝ), (32685153809417/100000000000000 : ℝ), (6537030904921/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(899064057/2000000000 : ℝ)|^2081 ≤ (34629691650517/100000000000000 : ℝ)^1569
        have hw : |(899064057/2000000000 : ℝ)|=(899064057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4303656213/10000000000 : ℝ)|^2081 ≤ (32685153809417/100000000000000 : ℝ)^1569
        have hw : |(4303656213/10000000000 : ℝ)|=(4303656213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075914071/2500000000 : ℝ)|^2081 ≤ (6537030904921/20000000000000 : ℝ)^1569
        have hw : |(1075914071/2500000000 : ℝ)|=(1075914071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_box_12 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1049364989/5000000000 : ℝ)*x 0 + (5440083881/10000000000 : ℝ)*x 1 + (1318241817/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049364989/5000000000 : ℝ)^2081 ≤ (3152359557791/25000000000000 : ℝ)^1569 := by
    have hnat : (1049364989 : ℕ)^2081*25000000000000^1569 ≤ 3152359557791^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049364989 5000000000 3152359557791 25000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440083881/10000000000 : ℝ)^2081 ≤ (139372719871/312500000000 : ℝ)^1569 := by
    have hnat : (5440083881 : ℕ)^2081*312500000000^1569 ≤ 139372719871^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440083881 10000000000 139372719871 312500000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318241817/2500000000 : ℝ)^2081 ≤ (8558258279667/20000000000000 : ℝ)^1569 := by
    have hnat : (1318241817 : ℕ)^2081*20000000000000^1569 ≤ 8558258279667^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318241817 2500000000 8558258279667 20000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1049364989/5000000000 : ℝ), (5440083881/10000000000 : ℝ), (1318241817/2500000000 : ℝ)] ![(3152359557791/25000000000000 : ℝ), (139372719871/312500000000 : ℝ), (8558258279667/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1049364989/5000000000 : ℝ)|^2081 ≤ (3152359557791/25000000000000 : ℝ)^1569
        have hw : |(-1049364989/5000000000 : ℝ)|=(1049364989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440083881/10000000000 : ℝ)|^2081 ≤ (139372719871/312500000000 : ℝ)^1569
        have hw : |(5440083881/10000000000 : ℝ)|=(5440083881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318241817/2500000000 : ℝ)|^2081 ≤ (8558258279667/20000000000000 : ℝ)^1569
        have hw : |(1318241817/2500000000 : ℝ)|=(1318241817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_box_13 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5369020203/10000000000 : ℝ)*x 0 + (-1097391203/5000000000 : ℝ)*x 1 + (1318241587/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369020203/10000000000 : ℝ)^2081 ≤ (43828207811369/100000000000000 : ℝ)^1569 := by
    have hnat : (5369020203 : ℕ)^2081*100000000000000^1569 ≤ 43828207811369^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369020203 10000000000 43828207811369 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097391203/5000000000 : ℝ)^2081 ≤ (13380510684667/100000000000000 : ℝ)^1569 := by
    have hnat : (1097391203 : ℕ)^2081*100000000000000^1569 ≤ 13380510684667^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097391203 5000000000 13380510684667 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318241587/2500000000 : ℝ)^2081 ≤ (5348910187001/12500000000000 : ℝ)^1569 := by
    have hnat : (1318241587 : ℕ)^2081*12500000000000^1569 ≤ 5348910187001^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318241587 2500000000 5348910187001 12500000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369020203/10000000000 : ℝ), (-1097391203/5000000000 : ℝ), (1318241587/2500000000 : ℝ)] ![(43828207811369/100000000000000 : ℝ), (13380510684667/100000000000000 : ℝ), (5348910187001/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369020203/10000000000 : ℝ)|^2081 ≤ (43828207811369/100000000000000 : ℝ)^1569
        have hw : |(5369020203/10000000000 : ℝ)|=(5369020203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1097391203/5000000000 : ℝ)|^2081 ≤ (13380510684667/100000000000000 : ℝ)^1569
        have hw : |(-1097391203/5000000000 : ℝ)|=(1097391203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318241587/2500000000 : ℝ)|^2081 ≤ (5348910187001/12500000000000 : ℝ)^1569
        have hw : |(1318241587/2500000000 : ℝ)|=(1318241587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_box_14 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5369019547/10000000000 : ℝ)*x 0 + (2636483809/5000000000 : ℝ)*x 1 + (-2194781593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369019547/10000000000 : ℝ)^2081 ≤ (21914100354431/50000000000000 : ℝ)^1569 := by
    have hnat : (5369019547 : ℕ)^2081*50000000000000^1569 ≤ 21914100354431^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369019547 10000000000 21914100354431 50000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636483809/5000000000 : ℝ)^2081 ≤ (1711651806621/4000000000000 : ℝ)^1569 := by
    have hnat : (2636483809 : ℕ)^2081*4000000000000^1569 ≤ 1711651806621^1569*5000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636483809 5000000000 1711651806621 4000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2194781593/10000000000 : ℝ)^2081 ≤ (13380504110801/100000000000000 : ℝ)^1569 := by
    have hnat : (2194781593 : ℕ)^2081*100000000000000^1569 ≤ 13380504110801^1569*10000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194781593 10000000000 13380504110801 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369019547/10000000000 : ℝ), (2636483809/5000000000 : ℝ), (-2194781593/10000000000 : ℝ)] ![(21914100354431/50000000000000 : ℝ), (1711651806621/4000000000000 : ℝ), (13380504110801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369019547/10000000000 : ℝ)|^2081 ≤ (21914100354431/50000000000000 : ℝ)^1569
        have hw : |(5369019547/10000000000 : ℝ)|=(5369019547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636483809/5000000000 : ℝ)|^2081 ≤ (1711651806621/4000000000000 : ℝ)^1569
        have hw : |(2636483809/5000000000 : ℝ)|=(2636483809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2194781593/10000000000 : ℝ)|^2081 ≤ (13380504110801/100000000000000 : ℝ)^1569
        have hw : |(-2194781593/10000000000 : ℝ)|=(2194781593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1131_box_15 (p : ℝ) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ)) (x : Fin 3 → ℝ) :
    (847966167/2000000000 : ℝ)*x 0 + (1107849681/2500000000 : ℝ)*x 1 + (553924767/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (847966167/2000000000 : ℝ)^2081 ≤ (32043796866969/100000000000000 : ℝ)^1569 := by
    have hnat : (847966167 : ℕ)^2081*100000000000000^1569 ≤ 32043796866969^1569*2000000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847966167 2000000000 32043796866969 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1107849681/2500000000 : ℝ)^2081 ≤ (33978104549087/100000000000000 : ℝ)^1569 := by
    have hnat : (1107849681 : ℕ)^2081*100000000000000^1569 ≤ 33978104549087^1569*2500000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107849681 2500000000 33978104549087 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553924767/1250000000 : ℝ)^2081 ≤ (33978098569313/100000000000000 : ℝ)^1569 := by
    have hnat : (553924767 : ℕ)^2081*100000000000000^1569 ≤ 33978098569313^1569*1250000000^2081 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553924767 1250000000 33978098569313 100000000000000 2081 1569 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2081/512 : ℝ)) 2081 1569 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(847966167/2000000000 : ℝ), (1107849681/2500000000 : ℝ), (553924767/1250000000 : ℝ)] ![(32043796866969/100000000000000 : ℝ), (33978104549087/100000000000000 : ℝ), (33978098569313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(847966167/2000000000 : ℝ)|^2081 ≤ (32043796866969/100000000000000 : ℝ)^1569
        have hw : |(847966167/2000000000 : ℝ)|=(847966167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1107849681/2500000000 : ℝ)|^2081 ≤ (33978104549087/100000000000000 : ℝ)^1569
        have hw : |(1107849681/2500000000 : ℝ)|=(1107849681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(553924767/1250000000 : ℝ)|^2081 ≤ (33978098569313/100000000000000 : ℝ)^1569
        have hw : |(553924767/1250000000 : ℝ)|=(553924767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1131_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (567/5000 : ℝ)*pair X i i ≤ pair X i h) :
    -(6223/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5929/10000 : ℝ) ∧ (39887/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (831/1000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7021/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (567/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7021/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (567/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7021/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (567/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7021/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (567/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7021/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (567/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7021/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (567/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (567/5000 : ℝ) ^ (8323/2048 : ℝ) ≤ (14387346064250351/100000000000000000000 : ℝ) := by
    have hpowers : (567/5000 : ℝ)^8323 ≤ (14387346064250351/100000000000000000000 : ℝ)^2048 := by
      have hnat : (567 : ℕ)^8323*100000000000000000000^2048 ≤ 14387346064250351^2048*5000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        567 5000 14387346064250351 100000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (567/5000 : ℝ)) (X := (14387346064250351/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7021/50000 : ℝ) ^ (8323/2048 : ℝ) ≤ (8572772734434173/25000000000000000000 : ℝ) := by
    have hpowers : (7021/50000 : ℝ)^8323 ≤ (8572772734434173/25000000000000000000 : ℝ)^2048 := by
      have hnat : (7021 : ℕ)^8323*25000000000000000000^2048 ≤ 8572772734434173^2048*50000^8323 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7021 50000 8572772734434173 25000000000000000000 8323 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7021/50000 : ℝ)) (X := (8572772734434173/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014387346064250351/50000000000000000000 : ℝ) ≤ (2500176992004937/2500000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (50014387346064250351/50000000000000000000 : ℝ)^2048 ≤ (2500176992004937/2500000000000000 : ℝ)^8323 := by
      have hnat : (50014387346064250351 : ℕ)^2048*2500000000000000^8323 ≤ 2500176992004937^8323*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014387346064250351 50000000000000000000 2500176992004937 2500000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500176992004937/2500000000000000 : ℝ)) (X := (50014387346064250351/50000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048678437001987043/100000000000000000000 : ℝ) ≤ (10001197586810687/10000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (100048678437001987043/100000000000000000000 : ℝ)^2048 ≤ (10001197586810687/10000000000000000 : ℝ)^8323 := by
      have hnat : (100048678437001987043 : ℕ)^2048*10000000000000000^8323 ≤ 10001197586810687^8323*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048678437001987043 100000000000000000000 10001197586810687 10000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001197586810687/10000000000000000 : ℝ)) (X := (100048678437001987043/100000000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508572772734434173/12500000000000000000 : ℝ) ≤ (5000843602800813/5000000000000000 : ℝ) ^ (8323/2048 : ℝ) := by
    have hpowers : (12508572772734434173/12500000000000000000 : ℝ)^2048 ≤ (5000843602800813/5000000000000000 : ℝ)^8323 := by
      have hnat : (12508572772734434173 : ℕ)^2048*5000000000000000^8323 ≤ 5000843602800813^8323*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508572772734434173 12500000000000000000 5000843602800813 5000000000000000 2048 8323 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000843602800813/5000000000000000 : ℝ)) (X := (12508572772734434173/12500000000000000000 : ℝ)) (by norm_num) 8323 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14387346064250351/100000000000000000000 : ℝ) ≤ ((241167931923311273/241250000000000000 : ℝ)+2*(489618790939/270200000000000 : ℝ)*(567/5000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (241167931923311273/241250000000000000 : ℝ)+2*(489618790939/270200000000000 : ℝ)*(567/5000 : ℝ)=(2500176992004937/2500000000000000 : ℝ) by norm_num, show 1+2*(14387346064250351/100000000000000000000 : ℝ)=(50014387346064250351/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8572772734434173/25000000000000000000 : ℝ)+(14387346064250351/100000000000000000000 : ℝ) ≤ ((241167931923311273/241250000000000000 : ℝ)+(489618790939/270200000000000 : ℝ)*((7021/50000 : ℝ)+(567/5000 : ℝ)))^(8323/2048 : ℝ) := by
    rw [show (241167931923311273/241250000000000000 : ℝ)+(489618790939/270200000000000 : ℝ)*((7021/50000 : ℝ)+(567/5000 : ℝ))=(10001197586810687/10000000000000000 : ℝ) by norm_num, show 1+(8572772734434173/25000000000000000000 : ℝ)+(14387346064250351/100000000000000000000 : ℝ)=(100048678437001987043/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8572772734434173/25000000000000000000 : ℝ) ≤ ((241167931923311273/241250000000000000 : ℝ)+2*(489618790939/270200000000000 : ℝ)*(7021/50000 : ℝ))^(8323/2048 : ℝ) := by
    rw [show (241167931923311273/241250000000000000 : ℝ)+2*(489618790939/270200000000000 : ℝ)*(7021/50000 : ℝ)=(5000843602800813/5000000000000000 : ℝ) by norm_num, show 1+2*(8572772734434173/25000000000000000000 : ℝ)=(12508572772734434173/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (241167931923311273/241250000000000000 : ℝ)*(X 1 0+X 2 0)+(489618790939/270200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (567/5000 : ℝ)) (hi := (7021/50000 : ℝ)) (c := (241167931923311273/241250000000000000 : ℝ)) (alpha := (489618790939/270200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (241167931923311273/241250000000000000 : ℝ)*(X 0 1+X 2 1)+(489618790939/270200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (567/5000 : ℝ)) (hi := (7021/50000 : ℝ)) (c := (241167931923311273/241250000000000000 : ℝ)) (alpha := (489618790939/270200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (241167931923311273/241250000000000000 : ℝ)*(X 0 2+X 1 2)+(489618790939/270200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8323/2048 : ℝ)) (lo := (567/5000 : ℝ)) (hi := (7021/50000 : ℝ)) (c := (241167931923311273/241250000000000000 : ℝ)) (alpha := (489618790939/270200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2044904963/10000000000 : ℝ)*X 0 0+(5376465389/10000000000 : ℝ)*X 0 1+(2688232819/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1323970683/2500000000 : ℝ)*X 1 0+(-2154162147/10000000000 : ℝ)*X 1 1+(84007267/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647940969/5000000000 : ℝ)*X 2 0+(5376465819/10000000000 : ℝ)*X 2 1+(-2154162227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((559235999/1250000000 : ℝ)*X 0 0+(107862829/250000000 : ℝ)*X 0 1+(2157256341/5000000000 : ℝ)*X 0 2+(559235999/1250000000 : ℝ)*X 1 0+(107862829/250000000 : ℝ)*X 1 1+(2157256341/5000000000 : ℝ)*X 1 2+(559235999/1250000000 : ℝ)*X 2 0+(107862829/250000000 : ℝ)*X 2 1+(2157256341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2300799011/10000000000 : ℝ)*X 0 0+(1056200149/2000000000 : ℝ)*X 0 1+(660125099/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363344929/10000000000 : ℝ)*X 1 0+(-273960277/1250000000 : ℝ)*X 1 1+(5281000633/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2681672409/5000000000 : ℝ)*X 2 0+(1056200153/2000000000 : ℝ)*X 2 1+(-2191682189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4258210831/10000000000 : ℝ)*X 0 0+(2211165251/5000000000 : ℝ)*X 0 1+(2211165327/5000000000 : ℝ)*X 0 2+(4258210831/10000000000 : ℝ)*X 1 0+(2211165251/5000000000 : ℝ)*X 1 1+(2211165327/5000000000 : ℝ)*X 1 2+(4258210831/10000000000 : ℝ)*X 2 0+(2211165251/5000000000 : ℝ)*X 2 1+(2211165327/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-561825089/2500000000 : ℝ)*X 0 0+(2608048231/5000000000 : ℝ)*X 0 1+(5386073129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289089407/10000000000 : ℝ)*X 1 0+(-1075158363/5000000000 : ℝ)*X 1 1+(1346518277/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322272343/2500000000 : ℝ)*X 2 0+(1077214641/2000000000 : ℝ)*X 2 1+(-2150316641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((899064057/2000000000 : ℝ)*X 0 0+(4303656213/10000000000 : ℝ)*X 0 1+(1075914071/2500000000 : ℝ)*X 0 2+(899064057/2000000000 : ℝ)*X 1 0+(4303656213/10000000000 : ℝ)*X 1 1+(1075914071/2500000000 : ℝ)*X 1 2+(899064057/2000000000 : ℝ)*X 2 0+(4303656213/10000000000 : ℝ)*X 2 1+(1075914071/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1049364989/5000000000 : ℝ)*X 0 0+(5440083881/10000000000 : ℝ)*X 0 1+(1318241817/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369020203/10000000000 : ℝ)*X 1 0+(-1097391203/5000000000 : ℝ)*X 1 1+(1318241587/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369019547/10000000000 : ℝ)*X 2 0+(2636483809/5000000000 : ℝ)*X 2 1+(-2194781593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((847966167/2000000000 : ℝ)*X 0 0+(1107849681/2500000000 : ℝ)*X 0 1+(553924767/1250000000 : ℝ)*X 0 2+(847966167/2000000000 : ℝ)*X 1 0+(1107849681/2500000000 : ℝ)*X 1 1+(553924767/1250000000 : ℝ)*X 1 2+(847966167/2000000000 : ℝ)*X 2 0+(1107849681/2500000000 : ℝ)*X 2 1+(553924767/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1131_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6223/10000 : ℝ) ≤ (-136122193183924184958142481583/218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38305383/100000000000000 : ℝ)*(lower3) + (1153213/3125000000000 : ℝ)*(lower4) + (1954567/50000000000000 : ℝ)*(upper5) + (1955700197974319/50000000000000 : ℝ)*(major0) + (1955700197974319/50000000000000 : ℝ)*(major1) + (1955700197974319/50000000000000 : ℝ)*(major2) + (2289271129/50000000000000 : ℝ)*(sp1) + (14549291/1000000000000 : ℝ)*(sp2) + (14268111/10000000000000 : ℝ)*(sp3) + (5222998459722363/100000000000000 : ℝ)*(sp4) + (5222995165185101/100000000000000 : ℝ)*(sp5) + (5222998288798259/100000000000000 : ℝ)*(sp6) + (52410866698527/2000000000000 : ℝ)*(sp7) + (321001249/25000000000000 : ℝ)*(sp12) + (131027173880373/5000000000000 : ℝ)*(f.failure) + (5222999743727359/100000000000000 : ℝ)*(f.sum) + (4192461760173/3377500000000000000000000000 : ℝ)*base65 + (1067880684176294641/84437500000000000000000000000000 : ℝ)*base68 + (507788772718982141/84437500000000000000000000000000 : ℝ)*base70 + (692349500041544641/84437500000000000000000000000000 : ℝ)*base72 + (3328169938749/6755000000000000000000000000 : ℝ)*base74 + (258974698516669641/84437500000000000000000000000000 : ℝ)*base76 + (772267565349482141/84437500000000000000000000000000 : ℝ)*base78 + (947039739709044641/84437500000000000000000000000000 : ℝ)*base80 + (18190164473277/3377500000000000000000000000 : ℝ)*base82 + (805549/50000000000000000000 : ℝ)*base89 + (805549/50000000000000000000 : ℝ)*base91 + (805549/50000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (5929/10000 : ℝ) ≤ (6258137024417539598742267795921/10554687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (27836203/20000000000000 : ℝ)*(lower0) + (23467967/20000000000000 : ℝ)*(upper1) + (52708009/20000000000000 : ℝ)*(upper2) + (1987685788116149/50000000000000 : ℝ)*(major0) + (1987685788116149/50000000000000 : ℝ)*(major1) + (1987685788116149/50000000000000 : ℝ)*(major2) + (1316893481519877/25000000000000 : ℝ)*(sp0) + (1053484659731271/20000000000000 : ℝ)*(sp1) + (658446106628183/12500000000000 : ℝ)*(sp2) + (332924085901529/12500000000000 : ℝ)*(sp3) + (7517985357/100000000000000 : ℝ)*(sp6) + (2482731827/25000000000000 : ℝ)*(sp7) + (153072354467/100000000000000 : ℝ)*(sp9) + (1222465657/50000000000000 : ℝ)*(sp12) + (133170130906977/5000000000000 : ℝ)*(f.failure) + (5267576371010821/100000000000000 : ℝ)*(f.sum) + (4531861658069/6755000000000000000000000000 : ℝ)*base66 + (567653490757847511/84437500000000000000000000000000 : ℝ)*base68 + (870191527472222511/84437500000000000000000000000000 : ℝ)*base70 + (224766654300910011/84437500000000000000000000000000 : ℝ)*base72 + (5371694071113/211093750000000000000000000 : ℝ)*base73 + (437114242998472511/84437500000000000000000000000000 : ℝ)*base76 + (436882632455847511/84437500000000000000000000000000 : ℝ)*base78 + (2569983646984339989/84437500000000000000000000000000 : ℝ)*base79 + (2505426175807/3377500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (795001/50000000000000000000 : ℝ)*base89 + (795001/50000000000000000000 : ℝ)*base91 + (795001/50000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (39887/50000 : ℝ) ≤ (75180465300765626764667286801/94238281250000000000000000000 : ℝ) := by norm_num
    linear_combination (23235687/100000000000000 : ℝ)*(upper0) + (21798287/100000000000000 : ℝ)*(lower3) + (12760847/50000000000000 : ℝ)*(upper4) + (1110835880587203/25000000000000 : ℝ)*(major0) + (1110835880587203/25000000000000 : ℝ)*(major1) + (1110835880587203/25000000000000 : ℝ)*(major2) + (25308001329/100000000000000 : ℝ)*(sp1) + (18639586423/20000000000000 : ℝ)*(sp2) + (9549137149/50000000000000 : ℝ)*(sp3) + (707718693/50000000000000 : ℝ)*(sp4) + (2941580408762563/50000000000000 : ℝ)*(sp8) + (183848028905037/3125000000000 : ℝ)*(sp9) + (5883069035030397/100000000000000 : ℝ)*(sp10) + (46514271610541/1562500000000 : ℝ)*(sp11) + (1488466240674461/50000000000000 : ℝ)*(f.failure) + (5883162232962513/100000000000000 : ℝ)*(f.sum) + (3597494957741/1688750000000000000000000000 : ℝ)*base65 + (320343217552619683/42218750000000000000000000000000 : ℝ)*base67 + (257301152305005317/42218750000000000000000000000000 : ℝ)*base70 + (164292095762942817/42218750000000000000000000000000 : ℝ)*base72 + (159776924185259/6755000000000000000000000000 : ℝ)*base73 + (239948944528692817/42218750000000000000000000000000 : ℝ)*base76 + (307141382704755317/42218750000000000000000000000000 : ℝ)*base78 + (821457286409244683/42218750000000000000000000000000 : ℝ)*base79 + (5345188969327/844375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (6207893/500000000000000000000 : ℝ)*base89 + (6207893/500000000000000000000 : ℝ)*base91 + (6207893/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-831/1000 : ℝ) ≤ (-2740829540067269738147091219/3298339843750000000000000000 : ℝ) := by norm_num
    linear_combination (103323271/100000000000000 : ℝ)*(lower0) + (221375139/100000000000000 : ℝ)*(lower2) + (38701701/100000000000000 : ℝ)*(upper3) + (116742537/100000000000000 : ℝ)*(upper5) + (89564625511033/2000000000000 : ℝ)*(major0) + (89564625511033/2000000000000 : ℝ)*(major1) + (89564625511033/2000000000000 : ℝ)*(major2) + (13521125013/50000000000000 : ℝ)*(sp0) + (540869075463/50000000000000 : ℝ)*(sp5) + (25450331099/25000000000000 : ℝ)*(sp7) + (2991914079987937/50000000000000 : ℝ)*(sp12) + (2991386732037487/50000000000000 : ℝ)*(sp13) + (59838552022259/1000000000000 : ℝ)*(sp14) + (300020462921131/10000000000000 : ℝ)*(sp15) + (1500153215267853/50000000000000 : ℝ)*(f.failure) + (59838552022259/1000000000000 : ℝ)*(f.sum) + (1194984603781/1351000000000000000000000000 : ℝ)*base66 + (11685607082506187/3377500000000000000000000000000 : ℝ)*base68 + (37006055387433813/3377500000000000000000000000000 : ℝ)*base69 + (13488256274338813/3377500000000000000000000000000 : ℝ)*base71 + (17088160298037/1351000000000000000000000000 : ℝ)*base74 + (19979360877958813/3377500000000000000000000000000 : ℝ)*base75 + (13156540772528813/3377500000000000000000000000000 : ℝ)*base77 + (38128231559263813/3377500000000000000000000000000 : ℝ)*base79 + (5722882056091/1351000000000000000000000000 : ℝ)*base81 + (4425211/500000000000000000000 : ℝ)*base90 + (4425211/500000000000000000000 : ℝ)*base92 + (4425211/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1131_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (567/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5929/10000 : ℝ) else (39887/50000 : ℝ) ≤ X j i ∧ X j i ≤ (831/1000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1131_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1131_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5929/10000 : ℝ) else (39887/50000 : ℝ) ≤ X j i ∧ X j i ≤ (831/1000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1131_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1131_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8323/2048 : ℝ) ≤ p) (hpb : p ≤ (2081/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (14925913/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7021/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11339/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6223/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(5929/10000 : ℝ) else (39887/50000 : ℝ) ≤ X j i ∧ X j i ≤ (831/1000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1131_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

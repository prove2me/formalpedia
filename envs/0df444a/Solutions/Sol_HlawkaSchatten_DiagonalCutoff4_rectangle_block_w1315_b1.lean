-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1315_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:41:39.836397+00:00
-- url     : https://prove2.me/submissions/73f57480-8267-4084-a065-fb5dd29c708e

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
theorem support_rectangle_w1315_s3_0 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-51636769/250000000 : ℝ)*x 0 + (339422959/625000000 : ℝ)*x 1 + (1307105697/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51636769/250000000 : ℝ)^4275 ≤ (2513585968979/20000000000000 : ℝ)^3251 := by
    have hnat : (51636769 : ℕ)^4275*20000000000000^3251 ≤ 2513585968979^3251*250000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51636769 250000000 2513585968979 20000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339422959/625000000 : ℝ)^4275 ≤ (2800449810519/6250000000000 : ℝ)^3251 := by
    have hnat : (339422959 : ℕ)^4275*6250000000000^3251 ≤ 2800449810519^3251*625000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339422959 625000000 2800449810519 6250000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307105697/2500000000 : ℝ)^4275 ≤ (532810914727/1250000000000 : ℝ)^3251 := by
    have hnat : (1307105697 : ℕ)^4275*1250000000000^3251 ≤ 532810914727^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307105697 2500000000 532810914727 1250000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51636769/250000000 : ℝ), (339422959/625000000 : ℝ), (1307105697/2500000000 : ℝ)] ![(2513585968979/20000000000000 : ℝ), (2800449810519/6250000000000 : ℝ), (532810914727/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51636769/250000000 : ℝ)|^4275 ≤ (2513585968979/20000000000000 : ℝ)^3251
        have hw : |(-51636769/250000000 : ℝ)|=(51636769/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339422959/625000000 : ℝ)|^4275 ≤ (2800449810519/6250000000000 : ℝ)^3251
        have hw : |(339422959/625000000 : ℝ)|=(339422959/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307105697/2500000000 : ℝ)|^4275 ≤ (532810914727/1250000000000 : ℝ)^3251
        have hw : |(1307105697/2500000000 : ℝ)|=(1307105697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s3_1 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353677487/10000000000 : ℝ)*x 0 + (-433791687/2000000000 : ℝ)*x 1 + (5228422777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353677487/10000000000 : ℝ)^4275 ≤ (43972694144129/100000000000000 : ℝ)^3251 := by
    have hnat : (5353677487 : ℕ)^4275*100000000000000^3251 ≤ 43972694144129^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353677487 10000000000 43972694144129 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (433791687/2000000000 : ℝ)^4275 ≤ (6701216388989/50000000000000 : ℝ)^3251 := by
    have hnat : (433791687 : ℕ)^4275*50000000000000^3251 ≤ 6701216388989^3251*2000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433791687 2000000000 6701216388989 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228422777/10000000000 : ℝ)^4275 ≤ (8524974612047/20000000000000 : ℝ)^3251 := by
    have hnat : (5228422777 : ℕ)^4275*20000000000000^3251 ≤ 8524974612047^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228422777 10000000000 8524974612047 20000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353677487/10000000000 : ℝ), (-433791687/2000000000 : ℝ), (5228422777/10000000000 : ℝ)] ![(43972694144129/100000000000000 : ℝ), (6701216388989/50000000000000 : ℝ), (8524974612047/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353677487/10000000000 : ℝ)|^4275 ≤ (43972694144129/100000000000000 : ℝ)^3251
        have hw : |(5353677487/10000000000 : ℝ)|=(5353677487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-433791687/2000000000 : ℝ)|^4275 ≤ (6701216388989/50000000000000 : ℝ)^3251
        have hw : |(-433791687/2000000000 : ℝ)|=(433791687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228422777/10000000000 : ℝ)|^4275 ≤ (8524974612047/20000000000000 : ℝ)^3251
        have hw : |(5228422777/10000000000 : ℝ)|=(5228422777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s3_2 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353677571/10000000000 : ℝ)*x 0 + (522842251/1000000000 : ℝ)*x 1 + (-542239669/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353677571/10000000000 : ℝ)^4275 ≤ (5496586881423/12500000000000 : ℝ)^3251 := by
    have hnat : (5353677571 : ℕ)^4275*12500000000000^3251 ≤ 5496586881423^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353677571 10000000000 5496586881423 12500000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522842251/1000000000 : ℝ)^4275 ≤ (8524974039577/20000000000000 : ℝ)^3251 := by
    have hnat : (522842251 : ℕ)^4275*20000000000000^3251 ≤ 8524974039577^3251*1000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522842251 1000000000 8524974039577 20000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542239669/2500000000 : ℝ)^4275 ≤ (1340243473623/10000000000000 : ℝ)^3251 := by
    have hnat : (542239669 : ℕ)^4275*10000000000000^3251 ≤ 1340243473623^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542239669 2500000000 1340243473623 10000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353677571/10000000000 : ℝ), (522842251/1000000000 : ℝ), (-542239669/2500000000 : ℝ)] ![(5496586881423/12500000000000 : ℝ), (8524974039577/20000000000000 : ℝ), (1340243473623/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353677571/10000000000 : ℝ)|^4275 ≤ (5496586881423/12500000000000 : ℝ)^3251
        have hw : |(5353677571/10000000000 : ℝ)|=(5353677571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522842251/1000000000 : ℝ)|^4275 ≤ (8524974039577/20000000000000 : ℝ)^3251
        have hw : |(522842251/1000000000 : ℝ)|=(522842251/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-542239669/2500000000 : ℝ)|^4275 ≤ (1340243473623/10000000000000 : ℝ)^3251
        have hw : |(-542239669/2500000000 : ℝ)|=(542239669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s3_3 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083121651/2500000000 : ℝ)*x 0 + (2063762409/5000000000 : ℝ)*x 1 + (2273524513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083121651/2500000000 : ℝ)^4275 ≤ (16645112044649/50000000000000 : ℝ)^3251 := by
    have hnat : (1083121651 : ℕ)^4275*50000000000000^3251 ≤ 16645112044649^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083121651 2500000000 16645112044649 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063762409/5000000000 : ℝ)^4275 ≤ (3904358100437/12500000000000 : ℝ)^3251 := by
    have hnat : (2063762409 : ℕ)^4275*12500000000000^3251 ≤ 3904358100437^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063762409 5000000000 3904358100437 12500000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273524513/5000000000 : ℝ)^4275 ≤ (35474911088489/100000000000000 : ℝ)^3251 := by
    have hnat : (2273524513 : ℕ)^4275*100000000000000^3251 ≤ 35474911088489^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273524513 5000000000 35474911088489 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083121651/2500000000 : ℝ), (2063762409/5000000000 : ℝ), (2273524513/5000000000 : ℝ)] ![(16645112044649/50000000000000 : ℝ), (3904358100437/12500000000000 : ℝ), (35474911088489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083121651/2500000000 : ℝ)|^4275 ≤ (16645112044649/50000000000000 : ℝ)^3251
        have hw : |(1083121651/2500000000 : ℝ)|=(1083121651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2063762409/5000000000 : ℝ)|^4275 ≤ (3904358100437/12500000000000 : ℝ)^3251
        have hw : |(2063762409/5000000000 : ℝ)|=(2063762409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2273524513/5000000000 : ℝ)|^4275 ≤ (35474911088489/100000000000000 : ℝ)^3251
        have hw : |(2273524513/5000000000 : ℝ)|=(2273524513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s3_4 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2065491717/10000000000 : ℝ)*x 0 + (209171211/400000000 : ℝ)*x 1 + (5429904551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2065491717/10000000000 : ℝ)^4275 ≤ (6284048764839/50000000000000 : ℝ)^3251 := by
    have hnat : (2065491717 : ℕ)^4275*50000000000000^3251 ≤ 6284048764839^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065491717 10000000000 6284048764839 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209171211/400000000 : ℝ)^4275 ≤ (42634066031087/100000000000000 : ℝ)^3251 := by
    have hnat : (209171211 : ℕ)^4275*100000000000000^3251 ≤ 42634066031087^3251*400000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209171211 400000000 42634066031087 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429904551/10000000000 : ℝ)^4275 ≤ (8959567283201/20000000000000 : ℝ)^3251 := by
    have hnat : (5429904551 : ℕ)^4275*20000000000000^3251 ≤ 8959567283201^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429904551 10000000000 8959567283201 20000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2065491717/10000000000 : ℝ), (209171211/400000000 : ℝ), (5429904551/10000000000 : ℝ)] ![(6284048764839/50000000000000 : ℝ), (42634066031087/100000000000000 : ℝ), (8959567283201/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2065491717/10000000000 : ℝ)|^4275 ≤ (6284048764839/50000000000000 : ℝ)^3251
        have hw : |(-2065491717/10000000000 : ℝ)|=(2065491717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209171211/400000000 : ℝ)|^4275 ≤ (42634066031087/100000000000000 : ℝ)^3251
        have hw : |(209171211/400000000 : ℝ)|=(209171211/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429904551/10000000000 : ℝ)|^4275 ≤ (8959567283201/20000000000000 : ℝ)^3251
        have hw : |(5429904551/10000000000 : ℝ)|=(5429904551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s3_5 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106034433/200000000 : ℝ)*x 0 + (-30741823/156250000 : ℝ)*x 1 + (5429904513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106034433/200000000 : ℝ)^4275 ≤ (43412396746507/100000000000000 : ℝ)^3251 := by
    have hnat : (106034433 : ℕ)^4275*100000000000000^3251 ≤ 43412396746507^3251*200000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106034433 200000000 43412396746507 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30741823/156250000 : ℝ)^4275 ≤ (11789767225511/100000000000000 : ℝ)^3251 := by
    have hnat : (30741823 : ℕ)^4275*100000000000000^3251 ≤ 11789767225511^3251*156250000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30741823 156250000 11789767225511 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5429904513/10000000000 : ℝ)^4275 ≤ (11199459000937/25000000000000 : ℝ)^3251 := by
    have hnat : (5429904513 : ℕ)^4275*25000000000000^3251 ≤ 11199459000937^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429904513 10000000000 11199459000937 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106034433/200000000 : ℝ), (-30741823/156250000 : ℝ), (5429904513/10000000000 : ℝ)] ![(43412396746507/100000000000000 : ℝ), (11789767225511/100000000000000 : ℝ), (11199459000937/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106034433/200000000 : ℝ)|^4275 ≤ (43412396746507/100000000000000 : ℝ)^3251
        have hw : |(106034433/200000000 : ℝ)|=(106034433/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30741823/156250000 : ℝ)|^4275 ≤ (11789767225511/100000000000000 : ℝ)^3251
        have hw : |(-30741823/156250000 : ℝ)|=(30741823/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5429904513/10000000000 : ℝ)|^4275 ≤ (11199459000937/25000000000000 : ℝ)^3251
        have hw : |(5429904513/10000000000 : ℝ)|=(5429904513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s3_6 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301721791/10000000000 : ℝ)*x 0 + (2714952193/5000000000 : ℝ)*x 1 + (-393495331/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301721791/10000000000 : ℝ)^4275 ≤ (5426549783091/12500000000000 : ℝ)^3251 := by
    have hnat : (5301721791 : ℕ)^4275*12500000000000^3251 ≤ 5426549783091^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301721791 10000000000 5426549783091 12500000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714952193/5000000000 : ℝ)^4275 ≤ (44797834625943/100000000000000 : ℝ)^3251 := by
    have hnat : (2714952193 : ℕ)^4275*100000000000000^3251 ≤ 44797834625943^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714952193 5000000000 44797834625943 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (393495331/2000000000 : ℝ)^4275 ≤ (2357953418311/20000000000000 : ℝ)^3251 := by
    have hnat : (393495331 : ℕ)^4275*20000000000000^3251 ≤ 2357953418311^3251*2000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393495331 2000000000 2357953418311 20000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301721791/10000000000 : ℝ), (2714952193/5000000000 : ℝ), (-393495331/2000000000 : ℝ)] ![(5426549783091/12500000000000 : ℝ), (44797834625943/100000000000000 : ℝ), (2357953418311/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301721791/10000000000 : ℝ)|^4275 ≤ (5426549783091/12500000000000 : ℝ)^3251
        have hw : |(5301721791/10000000000 : ℝ)|=(5301721791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714952193/5000000000 : ℝ)|^4275 ≤ (44797834625943/100000000000000 : ℝ)^3251
        have hw : |(2714952193/5000000000 : ℝ)|=(2714952193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-393495331/2000000000 : ℝ)|^4275 ≤ (2357953418311/20000000000000 : ℝ)^3251
        have hw : |(-393495331/2000000000 : ℝ)|=(393495331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s3_7 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4332529771/10000000000 : ℝ)*x 0 + (909054197/2000000000 : ℝ)*x 1 + (4129313841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4332529771/10000000000 : ℝ)^4275 ≤ (1331626410187/4000000000000 : ℝ)^3251 := by
    have hnat : (4332529771 : ℕ)^4275*4000000000000^3251 ≤ 1331626410187^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4332529771 10000000000 1331626410187 4000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (909054197/2000000000 : ℝ)^4275 ≤ (1418266841831/4000000000000 : ℝ)^3251 := by
    have hnat : (909054197 : ℕ)^4275*4000000000000^3251 ≤ 1418266841831^3251*2000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909054197 2000000000 1418266841831 4000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4129313841/10000000000 : ℝ)^4275 ≤ (31252668683259/100000000000000 : ℝ)^3251 := by
    have hnat : (4129313841 : ℕ)^4275*100000000000000^3251 ≤ 31252668683259^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129313841 10000000000 31252668683259 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4332529771/10000000000 : ℝ), (909054197/2000000000 : ℝ), (4129313841/10000000000 : ℝ)] ![(1331626410187/4000000000000 : ℝ), (1418266841831/4000000000000 : ℝ), (31252668683259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4332529771/10000000000 : ℝ)|^4275 ≤ (1331626410187/4000000000000 : ℝ)^3251
        have hw : |(4332529771/10000000000 : ℝ)|=(4332529771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(909054197/2000000000 : ℝ)|^4275 ≤ (1418266841831/4000000000000 : ℝ)^3251
        have hw : |(909054197/2000000000 : ℝ)|=(909054197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4129313841/10000000000 : ℝ)|^4275 ≤ (31252668683259/100000000000000 : ℝ)^3251
        have hw : |(4129313841/10000000000 : ℝ)|=(4129313841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1315_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3243/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9669/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10757/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7519/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3243/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9669/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3243/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9669/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3243/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9669/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3243/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9669/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3243/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9669/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3243/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9669/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9669/100000 : ℝ) ^ (2137/512 : ℝ) ≤ (5823137162891867/100000000000000000000 : ℝ) := by
    have hpowers : (9669/100000 : ℝ)^2137 ≤ (5823137162891867/100000000000000000000 : ℝ)^512 := by
      have hnat : (9669 : ℕ)^2137*100000000000000000000^512 ≤ 5823137162891867^512*100000^2137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9669 100000 5823137162891867 100000000000000000000 2137 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9669/100000 : ℝ)) (X := (5823137162891867/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3243/20000 : ℝ) ^ (2137/512 : ℝ) ≤ (50388236303630393/100000000000000000000 : ℝ) := by
    have hpowers : (3243/20000 : ℝ)^2137 ≤ (50388236303630393/100000000000000000000 : ℝ)^512 := by
      have hnat : (3243 : ℕ)^2137*100000000000000000000^512 ≤ 50388236303630393^512*20000^2137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3243 20000 50388236303630393 100000000000000000000 2137 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3243/20000 : ℝ)) (X := (50388236303630393/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005823137162891867/50000000000000000000 : ℝ) ≤ (10000279018644691/10000000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (50005823137162891867/50000000000000000000 : ℝ)^512 ≤ (10000279018644691/10000000000000000 : ℝ)^2137 := by
      have hnat : (50005823137162891867 : ℕ)^512*10000000000000000^2137 ≤ 10000279018644691^2137*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005823137162891867 50000000000000000000 10000279018644691 10000000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000279018644691/10000000000000000 : ℝ)) (X := (50005823137162891867/50000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002810568673326113/5000000000000000000 : ℝ) ≤ (2500336617622411/2500000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (5002810568673326113/5000000000000000000 : ℝ)^512 ≤ (2500336617622411/2500000000000000 : ℝ)^2137 := by
      have hnat : (5002810568673326113 : ℕ)^512*2500000000000000^2137 ≤ 2500336617622411^2137*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002810568673326113 5000000000000000000 2500336617622411 2500000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500336617622411/2500000000000000 : ℝ)) (X := (5002810568673326113/5000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50050388236303630393/50000000000000000000 : ℝ) ≤ (10002413922334597/10000000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (50050388236303630393/50000000000000000000 : ℝ)^512 ≤ (10002413922334597/10000000000000000 : ℝ)^2137 := by
      have hnat : (50050388236303630393 : ℕ)^512*10000000000000000^2137 ≤ 10002413922334597^2137*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50050388236303630393 50000000000000000000 10002413922334597 10000000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002413922334597/10000000000000000 : ℝ)) (X := (50050388236303630393/50000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5823137162891867/100000000000000000000 : ℝ) ≤ ((5453432006022537181/5455000000000000000 : ℝ)+2*(355817281651/218200000000000 : ℝ)*(9669/100000 : ℝ))^(2137/512 : ℝ) := by
    rw [show (5453432006022537181/5455000000000000000 : ℝ)+2*(355817281651/218200000000000 : ℝ)*(9669/100000 : ℝ)=(10000279018644691/10000000000000000 : ℝ) by norm_num, show 1+2*(5823137162891867/100000000000000000000 : ℝ)=(50005823137162891867/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(50388236303630393/100000000000000000000 : ℝ)+(5823137162891867/100000000000000000000 : ℝ) ≤ ((5453432006022537181/5455000000000000000 : ℝ)+(355817281651/218200000000000 : ℝ)*((3243/20000 : ℝ)+(9669/100000 : ℝ)))^(2137/512 : ℝ) := by
    rw [show (5453432006022537181/5455000000000000000 : ℝ)+(355817281651/218200000000000 : ℝ)*((3243/20000 : ℝ)+(9669/100000 : ℝ))=(2500336617622411/2500000000000000 : ℝ) by norm_num, show 1+(50388236303630393/100000000000000000000 : ℝ)+(5823137162891867/100000000000000000000 : ℝ)=(5002810568673326113/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(50388236303630393/100000000000000000000 : ℝ) ≤ ((5453432006022537181/5455000000000000000 : ℝ)+2*(355817281651/218200000000000 : ℝ)*(3243/20000 : ℝ))^(2137/512 : ℝ) := by
    rw [show (5453432006022537181/5455000000000000000 : ℝ)+2*(355817281651/218200000000000 : ℝ)*(3243/20000 : ℝ)=(10002413922334597/10000000000000000 : ℝ) by norm_num, show 1+2*(50388236303630393/100000000000000000000 : ℝ)=(50050388236303630393/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5453432006022537181/5455000000000000000 : ℝ)*(X 1 0+X 2 0)+(355817281651/218200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (9669/100000 : ℝ)) (hi := (3243/20000 : ℝ)) (c := (5453432006022537181/5455000000000000000 : ℝ)) (alpha := (355817281651/218200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5453432006022537181/5455000000000000000 : ℝ)*(X 0 1+X 2 1)+(355817281651/218200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (9669/100000 : ℝ)) (hi := (3243/20000 : ℝ)) (c := (5453432006022537181/5455000000000000000 : ℝ)) (alpha := (355817281651/218200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5453432006022537181/5455000000000000000 : ℝ)*(X 0 2+X 1 2)+(355817281651/218200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (9669/100000 : ℝ)) (hi := (3243/20000 : ℝ)) (c := (5453432006022537181/5455000000000000000 : ℝ)) (alpha := (355817281651/218200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-51636769/250000000 : ℝ)*X 0 0+(339422959/625000000 : ℝ)*X 0 1+(1307105697/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353677487/10000000000 : ℝ)*X 1 0+(-433791687/2000000000 : ℝ)*X 1 1+(5228422777/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353677571/10000000000 : ℝ)*X 2 0+(522842251/1000000000 : ℝ)*X 2 1+(-542239669/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1083121651/2500000000 : ℝ)*X 0 0+(2063762409/5000000000 : ℝ)*X 0 1+(2273524513/5000000000 : ℝ)*X 0 2+(1083121651/2500000000 : ℝ)*X 1 0+(2063762409/5000000000 : ℝ)*X 1 1+(2273524513/5000000000 : ℝ)*X 1 2+(1083121651/2500000000 : ℝ)*X 2 0+(2063762409/5000000000 : ℝ)*X 2 1+(2273524513/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2065491717/10000000000 : ℝ)*X 0 0+(209171211/400000000 : ℝ)*X 0 1+(5429904551/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((106034433/200000000 : ℝ)*X 1 0+(-30741823/156250000 : ℝ)*X 1 1+(5429904513/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301721791/10000000000 : ℝ)*X 2 0+(2714952193/5000000000 : ℝ)*X 2 1+(-393495331/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4332529771/10000000000 : ℝ)*X 0 0+(909054197/2000000000 : ℝ)*X 0 1+(4129313841/10000000000 : ℝ)*X 0 2+(4332529771/10000000000 : ℝ)*X 1 0+(909054197/2000000000 : ℝ)*X 1 1+(4129313841/10000000000 : ℝ)*X 1 2+(4332529771/10000000000 : ℝ)*X 2 0+(909054197/2000000000 : ℝ)*X 2 1+(4129313841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2103212153537166930423/681875000000000000000000000 : ℝ) := by norm_num
    linear_combination (694440297/100000000000000 : ℝ)*(base19) + (853978711/100000000000000 : ℝ)*(base23) + (13725899/100000000000000 : ℝ)*(lower2) + (172553853/100000000000000 : ℝ)*(upper3) + (7203013/12500000000000 : ℝ)*(lower4) + (228929721025049/6250000000000 : ℝ)*(major0) + (228929721025049/6250000000000 : ℝ)*(major1) + (228929721025049/6250000000000 : ℝ)*(major2) + (2471039286074159/50000000000000 : ℝ)*(sp0) + (1235521372420589/25000000000000 : ℝ)*(sp1) + (2471042665071971/50000000000000 : ℝ)*(sp2) + (2383657649911389/100000000000000 : ℝ)*(sp3) + (1522394867/20000000000000 : ℝ)*(sp4) + (7135952383/100000000000000 : ℝ)*(sp7) + (595916196465943/25000000000000 : ℝ)*(f.failure) + (4942086184122653/100000000000000 : ℝ)*(f.sum) + (22820116571489/2727500000000000000000000000 : ℝ)*base66 + (194731457225009369/34093750000000000000000000000000 : ℝ)*base67 + (352932239115884369/34093750000000000000000000000000 : ℝ)*base69 + (210289256927396881/34093750000000000000000000000000 : ℝ)*base72 + (5479530720557/5455000000000000000000000000 : ℝ)*base73 + (224842726706396881/34093750000000000000000000000000 : ℝ)*base76 + (291725776033959381/34093750000000000000000000000000 : ℝ)*base78 + (169083925688353119/34093750000000000000000000000000 : ℝ)*base79 + (16526653993817/5455000000000000000000000000 : ℝ)*base81 + (848849/500000000000000000000 : ℝ)*base89 + (848849/500000000000000000000 : ℝ)*base91 + (848849/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (136571478015971254833491547/17046875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1789558289/100000000000000 : ℝ)*(base19) + (503253743/25000000000000 : ℝ)*(base23) + (192624291/100000000000000 : ℝ)*(upper3) + (37543983/100000000000000 : ℝ)*(lower4) + (99329497/50000000000000 : ℝ)*(upper5) + (461783518688621/12500000000000 : ℝ)*(major0) + (461783518688621/12500000000000 : ℝ)*(major1) + (461783518688621/12500000000000 : ℝ)*(major2) + (30091067731/100000000000000 : ℝ)*(sp1) + (6428027311/20000000000000 : ℝ)*(sp2) + (39875536697543/800000000000 : ℝ)*(sp4) + (996882041313371/20000000000000 : ℝ)*(sp5) + (4984407934041347/100000000000000 : ℝ)*(sp6) + (150255871548387/6250000000000 : ℝ)*(sp7) + (150255871548387/6250000000000 : ℝ)*(f.failure) + (39875536697543/800000000000 : ℝ)*(f.sum) + (6642892974149/5455000000000000000000000000 : ℝ)*base65 + (789124618053704901/68187500000000000000000000000000 : ℝ)*base67 + (172831956520454901/68187500000000000000000000000000 : ℝ)*base69 + (200227800702170099/68187500000000000000000000000000 : ℝ)*base72 + (39775483331459/5455000000000000000000000000 : ℝ)*base73 + (1097894165182517401/68187500000000000000000000000000 : ℝ)*base75 + (148018196811267401/68187500000000000000000000000000 : ℝ)*base77 + (1057888351778892401/68187500000000000000000000000000 : ℝ)*base79 + (5511622254899/5455000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (909659/125000000000000000000 : ℝ)*base90 + (909659/125000000000000000000 : ℝ)*base92 + (909659/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1315_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3243/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9669/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10757/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7519/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1315_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1315_s4_0 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-258395197/1250000000 : ℝ)*x 0 + (5417198521/10000000000 : ℝ)*x 1 + (5240882657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258395197/1250000000 : ℝ)^4275 ≤ (3145365104339/25000000000000 : ℝ)^3251 := by
    have hnat : (258395197 : ℕ)^4275*25000000000000^3251 ≤ 3145365104339^3251*1250000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258395197 1250000000 3145365104339 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417198521/10000000000 : ℝ)^4275 ≤ (44660041337937/100000000000000 : ℝ)^3251 := by
    have hnat : (5417198521 : ℕ)^4275*100000000000000^3251 ≤ 44660041337937^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417198521 10000000000 44660041337937 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240882657/10000000000 : ℝ)^4275 ≤ (10689624558897/25000000000000 : ℝ)^3251 := by
    have hnat : (5240882657 : ℕ)^4275*25000000000000^3251 ≤ 10689624558897^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240882657 10000000000 10689624558897 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-258395197/1250000000 : ℝ), (5417198521/10000000000 : ℝ), (5240882657/10000000000 : ℝ)] ![(3145365104339/25000000000000 : ℝ), (44660041337937/100000000000000 : ℝ), (10689624558897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-258395197/1250000000 : ℝ)|^4275 ≤ (3145365104339/25000000000000 : ℝ)^3251
        have hw : |(-258395197/1250000000 : ℝ)|=(258395197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417198521/10000000000 : ℝ)|^4275 ≤ (44660041337937/100000000000000 : ℝ)^3251
        have hw : |(5417198521/10000000000 : ℝ)|=(5417198521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240882657/10000000000 : ℝ)|^4275 ≤ (10689624558897/25000000000000 : ℝ)^3251
        have hw : |(5240882657/10000000000 : ℝ)|=(5240882657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s4_1 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350235769/10000000000 : ℝ)*x 0 + (-2157077821/10000000000 : ℝ)*x 1 + (2620441177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350235769/10000000000 : ℝ)^4275 ≤ (2745970319119/6250000000000 : ℝ)^3251 := by
    have hnat : (5350235769 : ℕ)^4275*6250000000000^3251 ≤ 2745970319119^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350235769 10000000000 2745970319119 6250000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2157077821/10000000000 : ℝ)^4275 ≤ (2661195981251/20000000000000 : ℝ)^3251 := by
    have hnat : (2157077821 : ℕ)^4275*20000000000000^3251 ≤ 2661195981251^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157077821 10000000000 2661195981251 20000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620441177/5000000000 : ℝ)^4275 ≤ (21379247492433/50000000000000 : ℝ)^3251 := by
    have hnat : (2620441177 : ℕ)^4275*50000000000000^3251 ≤ 21379247492433^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620441177 5000000000 21379247492433 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350235769/10000000000 : ℝ), (-2157077821/10000000000 : ℝ), (2620441177/5000000000 : ℝ)] ![(2745970319119/6250000000000 : ℝ), (2661195981251/20000000000000 : ℝ), (21379247492433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350235769/10000000000 : ℝ)|^4275 ≤ (2745970319119/6250000000000 : ℝ)^3251
        have hw : |(5350235769/10000000000 : ℝ)|=(5350235769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2157077821/10000000000 : ℝ)|^4275 ≤ (2661195981251/20000000000000 : ℝ)^3251
        have hw : |(-2157077821/10000000000 : ℝ)|=(2157077821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620441177/5000000000 : ℝ)|^4275 ≤ (21379247492433/50000000000000 : ℝ)^3251
        have hw : |(2620441177/5000000000 : ℝ)|=(2620441177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s4_2 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675117811/5000000000 : ℝ)*x 0 + (2620440967/5000000000 : ℝ)*x 1 + (-2157078571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675117811/5000000000 : ℝ)^4275 ≤ (4393552351853/10000000000000 : ℝ)^3251 := by
    have hnat : (2675117811 : ℕ)^4275*10000000000000^3251 ≤ 4393552351853^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675117811 5000000000 4393552351853 10000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620440967/5000000000 : ℝ)^4275 ≤ (10689622619729/25000000000000 : ℝ)^3251 := by
    have hnat : (2620440967 : ℕ)^4275*25000000000000^3251 ≤ 10689622619729^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620440967 5000000000 10689622619729 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2157078571/10000000000 : ℝ)^4275 ≤ (13305985989867/100000000000000 : ℝ)^3251 := by
    have hnat : (2157078571 : ℕ)^4275*100000000000000^3251 ≤ 13305985989867^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157078571 10000000000 13305985989867 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675117811/5000000000 : ℝ), (2620440967/5000000000 : ℝ), (-2157078571/10000000000 : ℝ)] ![(4393552351853/10000000000000 : ℝ), (10689622619729/25000000000000 : ℝ), (13305985989867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675117811/5000000000 : ℝ)|^4275 ≤ (4393552351853/10000000000000 : ℝ)^3251
        have hw : |(2675117811/5000000000 : ℝ)|=(2675117811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620440967/5000000000 : ℝ)|^4275 ≤ (10689622619729/25000000000000 : ℝ)^3251
        have hw : |(2620440967/5000000000 : ℝ)|=(2620440967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2157078571/10000000000 : ℝ)|^4275 ≤ (13305985989867/100000000000000 : ℝ)^3251
        have hw : |(-2157078571/10000000000 : ℝ)|=(2157078571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s4_3 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4333512641/10000000000 : ℝ)*x 0 + (4154378993/10000000000 : ℝ)*x 1 + (1129984643/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4333512641/10000000000 : ℝ)^4275 ≤ (33300591680361/100000000000000 : ℝ)^3251 := by
    have hnat : (4333512641 : ℕ)^4275*100000000000000^3251 ≤ 33300591680361^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4333512641 10000000000 33300591680361 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4154378993/10000000000 : ℝ)^4275 ≤ (31502365559957/100000000000000 : ℝ)^3251 := by
    have hnat : (4154378993 : ℕ)^4275*100000000000000^3251 ≤ 31502365559957^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154378993 10000000000 31502365559957 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129984643/2500000000 : ℝ)^4275 ≤ (17598521372243/50000000000000 : ℝ)^3251 := by
    have hnat : (1129984643 : ℕ)^4275*50000000000000^3251 ≤ 17598521372243^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129984643 2500000000 17598521372243 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4333512641/10000000000 : ℝ), (4154378993/10000000000 : ℝ), (1129984643/2500000000 : ℝ)] ![(33300591680361/100000000000000 : ℝ), (31502365559957/100000000000000 : ℝ), (17598521372243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4333512641/10000000000 : ℝ)|^4275 ≤ (33300591680361/100000000000000 : ℝ)^3251
        have hw : |(4333512641/10000000000 : ℝ)|=(4333512641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4154378993/10000000000 : ℝ)|^4275 ≤ (31502365559957/100000000000000 : ℝ)^3251
        have hw : |(4154378993/10000000000 : ℝ)|=(4154378993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1129984643/2500000000 : ℝ)|^4275 ≤ (17598521372243/50000000000000 : ℝ)^3251
        have hw : |(1129984643/2500000000 : ℝ)|=(1129984643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s4_4 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-413435049/2000000000 : ℝ)*x 0 + (1048306891/2000000000 : ℝ)*x 1 + (1354135841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (413435049/2000000000 : ℝ)^4275 ≤ (6290784908131/50000000000000 : ℝ)^3251 := by
    have hnat : (413435049 : ℕ)^4275*50000000000000^3251 ≤ 6290784908131^3251*2000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413435049 2000000000 6290784908131 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048306891/2000000000 : ℝ)^4275 ≤ (4276549115763/10000000000000 : ℝ)^3251 := by
    have hnat : (1048306891 : ℕ)^4275*10000000000000^3251 ≤ 4276549115763^3251*2000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048306891 2000000000 4276549115763 10000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354135841/2500000000 : ℝ)^4275 ≤ (11163234752863/25000000000000 : ℝ)^3251 := by
    have hnat : (1354135841 : ℕ)^4275*25000000000000^3251 ≤ 11163234752863^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354135841 2500000000 11163234752863 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-413435049/2000000000 : ℝ), (1048306891/2000000000 : ℝ), (1354135841/2500000000 : ℝ)] ![(6290784908131/50000000000000 : ℝ), (4276549115763/10000000000000 : ℝ), (11163234752863/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-413435049/2000000000 : ℝ)|^4275 ≤ (6290784908131/50000000000000 : ℝ)^3251
        have hw : |(-413435049/2000000000 : ℝ)|=(413435049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048306891/2000000000 : ℝ)|^4275 ≤ (4276549115763/10000000000000 : ℝ)^3251
        have hw : |(1048306891/2000000000 : ℝ)|=(1048306891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354135841/2500000000 : ℝ)|^4275 ≤ (11163234752863/25000000000000 : ℝ)^3251
        have hw : |(1354135841/2500000000 : ℝ)|=(1354135841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s4_5 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304965589/10000000000 : ℝ)*x 0 + (-990708683/5000000000 : ℝ)*x 1 + (5416542651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304965589/10000000000 : ℝ)^4275 ≤ (8689465862869/20000000000000 : ℝ)^3251 := by
    have hnat : (5304965589 : ℕ)^4275*20000000000000^3251 ≤ 8689465862869^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304965589 10000000000 8689465862869 20000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (990708683/5000000000 : ℝ)^4275 ≤ (5949869693841/50000000000000 : ℝ)^3251 := by
    have hnat : (990708683 : ℕ)^4275*50000000000000^3251 ≤ 5949869693841^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990708683 5000000000 5949869693841 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416542651/10000000000 : ℝ)^4275 ≤ (44652931282217/100000000000000 : ℝ)^3251 := by
    have hnat : (5416542651 : ℕ)^4275*100000000000000^3251 ≤ 44652931282217^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416542651 10000000000 44652931282217 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304965589/10000000000 : ℝ), (-990708683/5000000000 : ℝ), (5416542651/10000000000 : ℝ)] ![(8689465862869/20000000000000 : ℝ), (5949869693841/50000000000000 : ℝ), (44652931282217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304965589/10000000000 : ℝ)|^4275 ≤ (8689465862869/20000000000000 : ℝ)^3251
        have hw : |(5304965589/10000000000 : ℝ)|=(5304965589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-990708683/5000000000 : ℝ)|^4275 ≤ (5949869693841/50000000000000 : ℝ)^3251
        have hw : |(-990708683/5000000000 : ℝ)|=(990708683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416542651/10000000000 : ℝ)|^4275 ≤ (44652931282217/100000000000000 : ℝ)^3251
        have hw : |(5416542651/10000000000 : ℝ)|=(5416542651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s4_6 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663120571/1250000000 : ℝ)*x 0 + (54165439/100000000 : ℝ)*x 1 + (-495354261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663120571/1250000000 : ℝ)^4275 ≤ (21723659159291/50000000000000 : ℝ)^3251 := by
    have hnat : (663120571 : ℕ)^4275*50000000000000^3251 ≤ 21723659159291^3251*1250000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663120571 1250000000 21723659159291 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54165439/100000000 : ℝ)^4275 ≤ (5581618102741/12500000000000 : ℝ)^3251 := by
    have hnat : (54165439 : ℕ)^4275*12500000000000^3251 ≤ 5581618102741^3251*100000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54165439 100000000 5581618102741 12500000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (495354261/2500000000 : ℝ)^4275 ≤ (594986842237/5000000000000 : ℝ)^3251 := by
    have hnat : (495354261 : ℕ)^4275*5000000000000^3251 ≤ 594986842237^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495354261 2500000000 594986842237 5000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663120571/1250000000 : ℝ), (54165439/100000000 : ℝ), (-495354261/2500000000 : ℝ)] ![(21723659159291/50000000000000 : ℝ), (5581618102741/12500000000000 : ℝ), (594986842237/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663120571/1250000000 : ℝ)|^4275 ≤ (21723659159291/50000000000000 : ℝ)^3251
        have hw : |(663120571/1250000000 : ℝ)|=(663120571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54165439/100000000 : ℝ)|^4275 ≤ (5581618102741/12500000000000 : ℝ)^3251
        have hw : |(54165439/100000000 : ℝ)|=(54165439/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-495354261/2500000000 : ℝ)|^4275 ≤ (594986842237/5000000000000 : ℝ)^3251
        have hw : |(-495354261/2500000000 : ℝ)|=(495354261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s4_7 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4333541383/10000000000 : ℝ)*x 0 + (4518587279/10000000000 : ℝ)*x 1 + (4155737401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4333541383/10000000000 : ℝ)^4275 ≤ (208130513219/625000000000 : ℝ)^3251 := by
    have hnat : (4333541383 : ℕ)^4275*625000000000^3251 ≤ 208130513219^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4333541383 10000000000 208130513219 625000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4518587279/10000000000 : ℝ)^4275 ≤ (35183206383963/100000000000000 : ℝ)^3251 := by
    have hnat : (4518587279 : ℕ)^4275*100000000000000^3251 ≤ 35183206383963^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518587279 10000000000 35183206383963 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4155737401/10000000000 : ℝ)^4275 ≤ (3939488936123/12500000000000 : ℝ)^3251 := by
    have hnat : (4155737401 : ℕ)^4275*12500000000000^3251 ≤ 3939488936123^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155737401 10000000000 3939488936123 12500000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4333541383/10000000000 : ℝ), (4518587279/10000000000 : ℝ), (4155737401/10000000000 : ℝ)] ![(208130513219/625000000000 : ℝ), (35183206383963/100000000000000 : ℝ), (3939488936123/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4333541383/10000000000 : ℝ)|^4275 ≤ (208130513219/625000000000 : ℝ)^3251
        have hw : |(4333541383/10000000000 : ℝ)|=(4333541383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4518587279/10000000000 : ℝ)|^4275 ≤ (35183206383963/100000000000000 : ℝ)^3251
        have hw : |(4518587279/10000000000 : ℝ)|=(4518587279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4155737401/10000000000 : ℝ)|^4275 ≤ (3939488936123/12500000000000 : ℝ)^3251
        have hw : |(4155737401/10000000000 : ℝ)|=(4155737401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1315_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7519/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10757/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11023/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7377/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7519/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10757/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7519/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10757/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7519/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10757/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7519/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10757/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7519/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10757/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7519/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10757/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10757/100000 : ℝ) ^ (2137/512 : ℝ) ≤ (2271879928068027/25000000000000000000 : ℝ) := by
    have hpowers : (10757/100000 : ℝ)^2137 ≤ (2271879928068027/25000000000000000000 : ℝ)^512 := by
      have hnat : (10757 : ℕ)^2137*25000000000000000000^512 ≤ 2271879928068027^512*100000^2137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10757 100000 2271879928068027 25000000000000000000 2137 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10757/100000 : ℝ)) (X := (2271879928068027/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7519/50000 : ℝ) ^ (2137/512 : ℝ) ≤ (18395128279455829/50000000000000000000 : ℝ) := by
    have hpowers : (7519/50000 : ℝ)^2137 ≤ (18395128279455829/50000000000000000000 : ℝ)^512 := by
      have hnat : (7519 : ℕ)^2137*50000000000000000000^512 ≤ 18395128279455829^512*50000^2137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7519 50000 18395128279455829 50000000000000000000 2137 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7519/50000 : ℝ)) (X := (18395128279455829/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502271879928068027/12500000000000000000 : ℝ) ≤ (2000087084484901/2000000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (12502271879928068027/12500000000000000000 : ℝ)^512 ≤ (2000087084484901/2000000000000000 : ℝ)^2137 := by
      have hnat : (12502271879928068027 : ℕ)^512*2000000000000000^2137 ≤ 2000087084484901^2137*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502271879928068027 12500000000000000000 2000087084484901 2000000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000087084484901/2000000000000000 : ℝ)) (X := (12502271879928068027/12500000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022938888135591883/50000000000000000000 : ℝ) ≤ (1000109898574139/1000000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (50022938888135591883/50000000000000000000 : ℝ)^512 ≤ (1000109898574139/1000000000000000 : ℝ)^2137 := by
      have hnat : (50022938888135591883 : ℕ)^512*1000000000000000^2137 ≤ 1000109898574139^2137*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022938888135591883 50000000000000000000 1000109898574139 1000000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000109898574139/1000000000000000 : ℝ)) (X := (50022938888135591883/50000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018395128279455829/25000000000000000000 : ℝ) ≤ (400070501962331/400000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (25018395128279455829/25000000000000000000 : ℝ)^512 ≤ (400070501962331/400000000000000 : ℝ)^2137 := by
      have hnat : (25018395128279455829 : ℕ)^512*400000000000000^2137 ≤ 400070501962331^2137*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018395128279455829 25000000000000000000 400070501962331 400000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400070501962331/400000000000000 : ℝ)) (X := (25018395128279455829/25000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2271879928068027/25000000000000000000 : ℝ) ≤ ((2853172542813322801/2854000000000000000 : ℝ)+2*(44237554459/28540000000000 : ℝ)*(10757/100000 : ℝ))^(2137/512 : ℝ) := by
    rw [show (2853172542813322801/2854000000000000000 : ℝ)+2*(44237554459/28540000000000 : ℝ)*(10757/100000 : ℝ)=(2000087084484901/2000000000000000 : ℝ) by norm_num, show 1+2*(2271879928068027/25000000000000000000 : ℝ)=(12502271879928068027/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18395128279455829/50000000000000000000 : ℝ)+(2271879928068027/25000000000000000000 : ℝ) ≤ ((2853172542813322801/2854000000000000000 : ℝ)+(44237554459/28540000000000 : ℝ)*((7519/50000 : ℝ)+(10757/100000 : ℝ)))^(2137/512 : ℝ) := by
    rw [show (2853172542813322801/2854000000000000000 : ℝ)+(44237554459/28540000000000 : ℝ)*((7519/50000 : ℝ)+(10757/100000 : ℝ))=(1000109898574139/1000000000000000 : ℝ) by norm_num, show 1+(18395128279455829/50000000000000000000 : ℝ)+(2271879928068027/25000000000000000000 : ℝ)=(50022938888135591883/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18395128279455829/50000000000000000000 : ℝ) ≤ ((2853172542813322801/2854000000000000000 : ℝ)+2*(44237554459/28540000000000 : ℝ)*(7519/50000 : ℝ))^(2137/512 : ℝ) := by
    rw [show (2853172542813322801/2854000000000000000 : ℝ)+2*(44237554459/28540000000000 : ℝ)*(7519/50000 : ℝ)=(400070501962331/400000000000000 : ℝ) by norm_num, show 1+2*(18395128279455829/50000000000000000000 : ℝ)=(25018395128279455829/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2853172542813322801/2854000000000000000 : ℝ)*(X 1 0+X 2 0)+(44237554459/28540000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (10757/100000 : ℝ)) (hi := (7519/50000 : ℝ)) (c := (2853172542813322801/2854000000000000000 : ℝ)) (alpha := (44237554459/28540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2853172542813322801/2854000000000000000 : ℝ)*(X 0 1+X 2 1)+(44237554459/28540000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (10757/100000 : ℝ)) (hi := (7519/50000 : ℝ)) (c := (2853172542813322801/2854000000000000000 : ℝ)) (alpha := (44237554459/28540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2853172542813322801/2854000000000000000 : ℝ)*(X 0 2+X 1 2)+(44237554459/28540000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (10757/100000 : ℝ)) (hi := (7519/50000 : ℝ)) (c := (2853172542813322801/2854000000000000000 : ℝ)) (alpha := (44237554459/28540000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-258395197/1250000000 : ℝ)*X 0 0+(5417198521/10000000000 : ℝ)*X 0 1+(5240882657/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350235769/10000000000 : ℝ)*X 1 0+(-2157077821/10000000000 : ℝ)*X 1 1+(2620441177/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675117811/5000000000 : ℝ)*X 2 0+(2620440967/5000000000 : ℝ)*X 2 1+(-2157078571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4333512641/10000000000 : ℝ)*X 0 0+(4154378993/10000000000 : ℝ)*X 0 1+(1129984643/2500000000 : ℝ)*X 0 2+(4333512641/10000000000 : ℝ)*X 1 0+(4154378993/10000000000 : ℝ)*X 1 1+(1129984643/2500000000 : ℝ)*X 1 2+(4333512641/10000000000 : ℝ)*X 2 0+(4154378993/10000000000 : ℝ)*X 2 1+(1129984643/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-413435049/2000000000 : ℝ)*X 0 0+(1048306891/2000000000 : ℝ)*X 0 1+(1354135841/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304965589/10000000000 : ℝ)*X 1 0+(-990708683/5000000000 : ℝ)*X 1 1+(5416542651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663120571/1250000000 : ℝ)*X 2 0+(54165439/100000000 : ℝ)*X 2 1+(-495354261/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4333541383/10000000000 : ℝ)*X 0 0+(4518587279/10000000000 : ℝ)*X 0 1+(4155737401/10000000000 : ℝ)*X 0 2+(4333541383/10000000000 : ℝ)*X 1 0+(4518587279/10000000000 : ℝ)*X 1 1+(4155737401/10000000000 : ℝ)*X 1 2+(4333541383/10000000000 : ℝ)*X 2 0+(4518587279/10000000000 : ℝ)*X 2 1+(4155737401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101422596035257848519784083/35675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1455599151/100000000000000 : ℝ)*(base19) + (1147429579/100000000000000 : ℝ)*(base23) + (70529279/100000000000000 : ℝ)*(upper3) + (12040801/50000000000000 : ℝ)*(lower4) + (2101816445170561/50000000000000 : ℝ)*(major0) + (2101816445170561/50000000000000 : ℝ)*(major1) + (2101816445170561/50000000000000 : ℝ)*(major2) + (5671670249535607/100000000000000 : ℝ)*(sp0) + (1417923607929703/25000000000000 : ℝ)*(sp1) + (5671671416889113/100000000000000 : ℝ)*(sp2) + (1367775544924359/50000000000000 : ℝ)*(sp3) + (6409445589/25000000000000 : ℝ)*(sp4) + (2915374909/12500000000000 : ℝ)*(sp6) + (18708750223/100000000000000 : ℝ)*(sp7) + (2735569798598941/100000000000000 : ℝ)*(f.failure) + (1417923971829491/25000000000000 : ℝ)*(f.sum) + (6376366812533/1427000000000000000000000000 : ℝ)*base65 + (1082531754803438639/142700000000000000000000000000000 : ℝ)*base68 + (1762552491690238639/142700000000000000000000000000000 : ℝ)*base70 + (297496481257338639/142700000000000000000000000000000 : ℝ)*base72 + (98447236231/285400000000000000000000000 : ℝ)*base74 + (149300716034261361/142700000000000000000000000000000 : ℝ)*base75 + (1172788507473138639/142700000000000000000000000000000 : ℝ)*base78 + (1270426573613938639/142700000000000000000000000000000 : ℝ)*base80 + (2369155955079/713500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (13401563/2000000000000000000000 : ℝ)*base89 + (13401563/2000000000000000000000 : ℝ)*base91 + (13401563/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107285776800443583940022019/71350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (979122439/100000000000000 : ℝ)*(base19) + (219646027/100000000000000 : ℝ)*(base23) + (125608097/100000000000000 : ℝ)*(lower4) + (45271089/100000000000000 : ℝ)*(lower5) + (2117487373677909/50000000000000 : ℝ)*(major0) + (2117487373677909/50000000000000 : ℝ)*(major1) + (2117487373677909/50000000000000 : ℝ)*(major2) + (117754467/5000000000000 : ℝ)*(sp1) + (904986477/6250000000000 : ℝ)*(sp2) + (4451572241/100000000000000 : ℝ)*(sp3) + (22855934069123/400000000000 : ℝ)*(sp4) + (5713980183068971/100000000000000 : ℝ)*(sp5) + (1428492204462773/25000000000000 : ℝ)*(sp6) + (2755961475736799/100000000000000 : ℝ)*(sp7) + (34449574091363/1250000000000 : ℝ)*(f.failure) + (22855934069123/400000000000 : ℝ)*(f.sum) + (2393205516967/713500000000000000000000000 : ℝ)*base66 + (1599842458376003109/142700000000000000000000000000000 : ℝ)*base67 + (2468145164025103109/142700000000000000000000000000000 : ℝ)*base69 + (2280701489694903109/142700000000000000000000000000000 : ℝ)*base71 + (1949135217927/713500000000000000000000000 : ℝ)*base74 + (2773773533886403109/142700000000000000000000000000000 : ℝ)*base75 + (1123146776206203109/142700000000000000000000000000000 : ℝ)*base77 + (226297616093403109/142700000000000000000000000000000 : ℝ)*base79 + (8919356169/11416000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (356091/25000000000000000000 : ℝ)*base90 + (356091/25000000000000000000 : ℝ)*base92 + (356091/25000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1315_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7519/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10757/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11023/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1315_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1315_s5_0 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1033734337/5000000000 : ℝ)*x 0 + (5414588439/10000000000 : ℝ)*x 1 + (5243290609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033734337/5000000000 : ℝ)^4275 ≤ (2516783662023/20000000000000 : ℝ)^3251 := by
    have hnat : (1033734337 : ℕ)^4275*20000000000000^3251 ≤ 2516783662023^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033734337 5000000000 2516783662023 20000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414588439/10000000000 : ℝ)^4275 ≤ (44631747965841/100000000000000 : ℝ)^3251 := by
    have hnat : (5414588439 : ℕ)^4275*100000000000000^3251 ≤ 44631747965841^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414588439 10000000000 44631747965841 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243290609/10000000000 : ℝ)^4275 ≤ (42784333707781/100000000000000 : ℝ)^3251 := by
    have hnat : (5243290609 : ℕ)^4275*100000000000000^3251 ≤ 42784333707781^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243290609 10000000000 42784333707781 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1033734337/5000000000 : ℝ), (5414588439/10000000000 : ℝ), (5243290609/10000000000 : ℝ)] ![(2516783662023/20000000000000 : ℝ), (44631747965841/100000000000000 : ℝ), (42784333707781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1033734337/5000000000 : ℝ)|^4275 ≤ (2516783662023/20000000000000 : ℝ)^3251
        have hw : |(-1033734337/5000000000 : ℝ)|=(1033734337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414588439/10000000000 : ℝ)|^4275 ≤ (44631747965841/100000000000000 : ℝ)^3251
        have hw : |(5414588439/10000000000 : ℝ)|=(5414588439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243290609/10000000000 : ℝ)|^4275 ≤ (42784333707781/100000000000000 : ℝ)^3251
        have hw : |(5243290609/10000000000 : ℝ)|=(5243290609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s5_1 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674785273/5000000000 : ℝ)*x 0 + (-215477749/1000000000 : ℝ)*x 1 + (5243290653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674785273/5000000000 : ℝ)^4275 ≤ (43928341858867/100000000000000 : ℝ)^3251 := by
    have hnat : (2674785273 : ℕ)^4275*100000000000000^3251 ≤ 43928341858867^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674785273 5000000000 43928341858867 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215477749/1000000000 : ℝ)^4275 ≤ (13287323947699/100000000000000 : ℝ)^3251 := by
    have hnat : (215477749 : ℕ)^4275*100000000000000^3251 ≤ 13287323947699^3251*1000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215477749 1000000000 13287323947699 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243290653/10000000000 : ℝ)^4275 ≤ (42784334179901/100000000000000 : ℝ)^3251 := by
    have hnat : (5243290653 : ℕ)^4275*100000000000000^3251 ≤ 42784334179901^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243290653 10000000000 42784334179901 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674785273/5000000000 : ℝ), (-215477749/1000000000 : ℝ), (5243290653/10000000000 : ℝ)] ![(43928341858867/100000000000000 : ℝ), (13287323947699/100000000000000 : ℝ), (42784334179901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674785273/5000000000 : ℝ)|^4275 ≤ (43928341858867/100000000000000 : ℝ)^3251
        have hw : |(2674785273/5000000000 : ℝ)|=(2674785273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215477749/1000000000 : ℝ)|^4275 ≤ (13287323947699/100000000000000 : ℝ)^3251
        have hw : |(-215477749/1000000000 : ℝ)|=(215477749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243290653/10000000000 : ℝ)|^4275 ≤ (42784334179901/100000000000000 : ℝ)^3251
        have hw : |(5243290653/10000000000 : ℝ)|=(5243290653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s5_2 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349570523/10000000000 : ℝ)*x 0 + (5243290657/10000000000 : ℝ)*x 1 + (-538694379/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349570523/10000000000 : ℝ)^4275 ≤ (2745521350657/6250000000000 : ℝ)^3251 := by
    have hnat : (5349570523 : ℕ)^4275*6250000000000^3251 ≤ 2745521350657^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349570523 10000000000 2745521350657 6250000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243290657/10000000000 : ℝ)^4275 ≤ (42784334222821/100000000000000 : ℝ)^3251 := by
    have hnat : (5243290657 : ℕ)^4275*100000000000000^3251 ≤ 42784334222821^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243290657 10000000000 42784334222821 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538694379/2500000000 : ℝ)^4275 ≤ (6643662079263/50000000000000 : ℝ)^3251 := by
    have hnat : (538694379 : ℕ)^4275*50000000000000^3251 ≤ 6643662079263^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538694379 2500000000 6643662079263 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349570523/10000000000 : ℝ), (5243290657/10000000000 : ℝ), (-538694379/2500000000 : ℝ)] ![(2745521350657/6250000000000 : ℝ), (42784334222821/100000000000000 : ℝ), (6643662079263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349570523/10000000000 : ℝ)|^4275 ≤ (2745521350657/6250000000000 : ℝ)^3251
        have hw : |(5349570523/10000000000 : ℝ)|=(5349570523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243290657/10000000000 : ℝ)|^4275 ≤ (42784334222821/100000000000000 : ℝ)^3251
        have hw : |(5243290657/10000000000 : ℝ)|=(5243290657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-538694379/2500000000 : ℝ)|^4275 ≤ (6643662079263/50000000000000 : ℝ)^3251
        have hw : |(-538694379/2500000000 : ℝ)|=(538694379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s5_3 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4333694393/10000000000 : ℝ)*x 0 + (2079779479/5000000000 : ℝ)*x 1 + (564339137/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4333694393/10000000000 : ℝ)^4275 ≤ (16651214137049/50000000000000 : ℝ)^3251 := by
    have hnat : (4333694393 : ℕ)^4275*50000000000000^3251 ≤ 16651214137049^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4333694393 10000000000 16651214137049 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2079779479/5000000000 : ℝ)^4275 ≤ (6310805442107/20000000000000 : ℝ)^3251 := by
    have hnat : (2079779479 : ℕ)^4275*20000000000000^3251 ≤ 6310805442107^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2079779479 5000000000 6310805442107 20000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564339137/1250000000 : ℝ)^4275 ≤ (35143544497867/100000000000000 : ℝ)^3251 := by
    have hnat : (564339137 : ℕ)^4275*100000000000000^3251 ≤ 35143544497867^3251*1250000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564339137 1250000000 35143544497867 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4333694393/10000000000 : ℝ), (2079779479/5000000000 : ℝ), (564339137/1250000000 : ℝ)] ![(16651214137049/50000000000000 : ℝ), (6310805442107/20000000000000 : ℝ), (35143544497867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4333694393/10000000000 : ℝ)|^4275 ≤ (16651214137049/50000000000000 : ℝ)^3251
        have hw : |(4333694393/10000000000 : ℝ)|=(4333694393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2079779479/5000000000 : ℝ)|^4275 ≤ (6310805442107/20000000000000 : ℝ)^3251
        have hw : |(2079779479/5000000000 : ℝ)|=(2079779479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(564339137/1250000000 : ℝ)|^4275 ≤ (35143544497867/100000000000000 : ℝ)^3251
        have hw : |(564339137/1250000000 : ℝ)|=(564339137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s5_4 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2067481383/10000000000 : ℝ)*x 0 + (2621952981/5000000000 : ℝ)*x 1 + (5413969879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2067481383/10000000000 : ℝ)^4275 ≤ (6292010015239/50000000000000 : ℝ)^3251 := by
    have hnat : (2067481383 : ℕ)^4275*50000000000000^3251 ≤ 6292010015239^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067481383 10000000000 6292010015239 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621952981/5000000000 : ℝ)^4275 ≤ (42790936571633/100000000000000 : ℝ)^3251 := by
    have hnat : (2621952981 : ℕ)^4275*100000000000000^3251 ≤ 42790936571633^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621952981 5000000000 42790936571633 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413969879/10000000000 : ℝ)^4275 ≤ (44625043385299/100000000000000 : ℝ)^3251 := by
    have hnat : (5413969879 : ℕ)^4275*100000000000000^3251 ≤ 44625043385299^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413969879 10000000000 44625043385299 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2067481383/10000000000 : ℝ), (2621952981/5000000000 : ℝ), (5413969879/10000000000 : ℝ)] ![(6292010015239/50000000000000 : ℝ), (42790936571633/100000000000000 : ℝ), (44625043385299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2067481383/10000000000 : ℝ)|^4275 ≤ (6292010015239/50000000000000 : ℝ)^3251
        have hw : |(-2067481383/10000000000 : ℝ)|=(2067481383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621952981/5000000000 : ℝ)|^4275 ≤ (42790936571633/100000000000000 : ℝ)^3251
        have hw : |(2621952981/5000000000 : ℝ)|=(2621952981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413969879/10000000000 : ℝ)|^4275 ≤ (44625043385299/100000000000000 : ℝ)^3251
        have hw : |(5413969879/10000000000 : ℝ)|=(5413969879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s5_5 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265279433/500000000 : ℝ)*x 0 + (-992049141/5000000000 : ℝ)*x 1 + (2706984983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265279433/500000000 : ℝ)^4275 ≤ (4345403966531/10000000000000 : ℝ)^3251 := by
    have hnat : (265279433 : ℕ)^4275*10000000000000^3251 ≤ 4345403966531^3251*500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265279433 500000000 4345403966531 10000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (992049141/5000000000 : ℝ)^4275 ≤ (5960457996589/50000000000000 : ℝ)^3251 := by
    have hnat : (992049141 : ℕ)^4275*50000000000000^3251 ≤ 5960457996589^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992049141 5000000000 5960457996589 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706984983/5000000000 : ℝ)^4275 ≤ (11156261082069/25000000000000 : ℝ)^3251 := by
    have hnat : (2706984983 : ℕ)^4275*25000000000000^3251 ≤ 11156261082069^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706984983 5000000000 11156261082069 25000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265279433/500000000 : ℝ), (-992049141/5000000000 : ℝ), (2706984983/5000000000 : ℝ)] ![(4345403966531/10000000000000 : ℝ), (5960457996589/50000000000000 : ℝ), (11156261082069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265279433/500000000 : ℝ)|^4275 ≤ (4345403966531/10000000000000 : ℝ)^3251
        have hw : |(265279433/500000000 : ℝ)|=(265279433/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-992049141/5000000000 : ℝ)|^4275 ≤ (5960457996589/50000000000000 : ℝ)^3251
        have hw : |(-992049141/5000000000 : ℝ)|=(992049141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706984983/5000000000 : ℝ)|^4275 ≤ (11156261082069/25000000000000 : ℝ)^3251
        have hw : |(2706984983/5000000000 : ℝ)|=(2706984983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s5_6 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652794531/5000000000 : ℝ)*x 0 + (541396971/1000000000 : ℝ)*x 1 + (-992049043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652794531/5000000000 : ℝ)^4275 ≤ (869080879897/2000000000000 : ℝ)^3251 := by
    have hnat : (2652794531 : ℕ)^4275*2000000000000^3251 ≤ 869080879897^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652794531 5000000000 869080879897 2000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541396971/1000000000 : ℝ)^4275 ≤ (22312520776769/50000000000000 : ℝ)^3251 := by
    have hnat : (541396971 : ℕ)^4275*50000000000000^3251 ≤ 22312520776769^3251*1000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541396971 1000000000 22312520776769 50000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (992049043/5000000000 : ℝ)^4275 ≤ (74505715279/625000000000 : ℝ)^3251 := by
    have hnat : (992049043 : ℕ)^4275*625000000000^3251 ≤ 74505715279^3251*5000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992049043 5000000000 74505715279 625000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652794531/5000000000 : ℝ), (541396971/1000000000 : ℝ), (-992049043/5000000000 : ℝ)] ![(869080879897/2000000000000 : ℝ), (22312520776769/50000000000000 : ℝ), (74505715279/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652794531/5000000000 : ℝ)|^4275 ≤ (869080879897/2000000000000 : ℝ)^3251
        have hw : |(2652794531/5000000000 : ℝ)|=(2652794531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541396971/1000000000 : ℝ)|^4275 ≤ (22312520776769/50000000000000 : ℝ)^3251
        have hw : |(541396971/1000000000 : ℝ)|=(541396971/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-992049043/5000000000 : ℝ)|^4275 ≤ (74505715279/625000000000 : ℝ)^3251
        have hw : |(-992049043/5000000000 : ℝ)|=(992049043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1315_s5_7 (p : ℝ) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083430221/2500000000 : ℝ)*x 0 + (1128359301/2500000000 : ℝ)*x 1 + (4160841251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083430221/2500000000 : ℝ)^4275 ≤ (33302695966189/100000000000000 : ℝ)^3251 := by
    have hnat : (1083430221 : ℕ)^4275*100000000000000^3251 ≤ 33302695966189^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083430221 2500000000 33302695966189 100000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128359301/2500000000 : ℝ)^4275 ≤ (7026096984011/20000000000000 : ℝ)^3251 := by
    have hnat : (1128359301 : ℕ)^4275*20000000000000^3251 ≤ 7026096984011^3251*2500000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128359301 2500000000 7026096984011 20000000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4160841251/10000000000 : ℝ)^4275 ≤ (3945852388669/12500000000000 : ℝ)^3251 := by
    have hnat : (4160841251 : ℕ)^4275*12500000000000^3251 ≤ 3945852388669^3251*10000000000^4275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4160841251 10000000000 3945852388669 12500000000000 4275 3251 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4275/1024 : ℝ)) 4275 3251 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083430221/2500000000 : ℝ), (1128359301/2500000000 : ℝ), (4160841251/10000000000 : ℝ)] ![(33302695966189/100000000000000 : ℝ), (7026096984011/20000000000000 : ℝ), (3945852388669/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083430221/2500000000 : ℝ)|^4275 ≤ (33302695966189/100000000000000 : ℝ)^3251
        have hw : |(1083430221/2500000000 : ℝ)|=(1083430221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1128359301/2500000000 : ℝ)|^4275 ≤ (7026096984011/20000000000000 : ℝ)^3251
        have hw : |(1128359301/2500000000 : ℝ)|=(1128359301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4160841251/10000000000 : ℝ)|^4275 ≤ (3945852388669/12500000000000 : ℝ)^3251
        have hw : |(4160841251/10000000000 : ℝ)|=(4160841251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1315_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11023/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5537/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (147/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11023/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11023/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11023/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11023/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11023/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11023/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11023/100000 : ℝ) ^ (2137/512 : ℝ) ≤ (10062919554969409/100000000000000000000 : ℝ) := by
    have hpowers : (11023/100000 : ℝ)^2137 ≤ (10062919554969409/100000000000000000000 : ℝ)^512 := by
      have hnat : (11023 : ℕ)^2137*100000000000000000000^512 ≤ 10062919554969409^512*100000^2137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11023 100000 10062919554969409 100000000000000000000 2137 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11023/100000 : ℝ)) (X := (10062919554969409/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7377/50000 : ℝ) ^ (2137/512 : ℝ) ≤ (33976001072242709/100000000000000000000 : ℝ) := by
    have hpowers : (7377/50000 : ℝ)^2137 ≤ (33976001072242709/100000000000000000000 : ℝ)^512 := by
      have hnat : (7377 : ℕ)^2137*100000000000000000000^512 ≤ 33976001072242709^512*50000^2137 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7377 50000 33976001072242709 100000000000000000000 2137 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7377/50000 : ℝ)) (X := (33976001072242709/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010062919554969409/50000000000000000000 : ℝ) ≤ (10000482154479471/10000000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (50010062919554969409/50000000000000000000 : ℝ)^512 ≤ (10000482154479471/10000000000000000 : ℝ)^2137 := by
      have hnat : (50010062919554969409 : ℕ)^512*10000000000000000^2137 ≤ 10000482154479471^2137*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010062919554969409 50000000000000000000 10000482154479471 10000000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000482154479471/10000000000000000 : ℝ)) (X := (50010062919554969409/50000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022019460313606059/50000000000000000000 : ℝ) ≤ (1250131867998033/1250000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (50022019460313606059/50000000000000000000 : ℝ)^512 ≤ (1250131867998033/1250000000000000 : ℝ)^2137 := by
      have hnat : (50022019460313606059 : ℕ)^512*1250000000000000^2137 ≤ 1250131867998033^2137*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022019460313606059 50000000000000000000 1250131867998033 1250000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250131867998033/1250000000000000 : ℝ)) (X := (50022019460313606059/50000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033976001072242709/50000000000000000000 : ℝ) ≤ (10001627733489057/10000000000000000 : ℝ) ^ (2137/512 : ℝ) := by
    have hpowers : (50033976001072242709/50000000000000000000 : ℝ)^512 ≤ (10001627733489057/10000000000000000 : ℝ)^2137 := by
      have hnat : (50033976001072242709 : ℕ)^512*10000000000000000^2137 ≤ 10001627733489057^2137*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033976001072242709 50000000000000000000 10001627733489057 10000000000000000 512 2137 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001627733489057/10000000000000000 : ℝ)) (X := (50033976001072242709/50000000000000000000 : ℝ)) (by norm_num) 2137 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10062919554969409/100000000000000000000 : ℝ) ≤ ((37299171200940239823/37310000000000000000 : ℝ)+2*(572789504793/373100000000000 : ℝ)*(11023/100000 : ℝ))^(2137/512 : ℝ) := by
    rw [show (37299171200940239823/37310000000000000000 : ℝ)+2*(572789504793/373100000000000 : ℝ)*(11023/100000 : ℝ)=(10000482154479471/10000000000000000 : ℝ) by norm_num, show 1+2*(10062919554969409/100000000000000000000 : ℝ)=(50010062919554969409/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33976001072242709/100000000000000000000 : ℝ)+(10062919554969409/100000000000000000000 : ℝ) ≤ ((37299171200940239823/37310000000000000000 : ℝ)+(572789504793/373100000000000 : ℝ)*((7377/50000 : ℝ)+(11023/100000 : ℝ)))^(2137/512 : ℝ) := by
    rw [show (37299171200940239823/37310000000000000000 : ℝ)+(572789504793/373100000000000 : ℝ)*((7377/50000 : ℝ)+(11023/100000 : ℝ))=(1250131867998033/1250000000000000 : ℝ) by norm_num, show 1+(33976001072242709/100000000000000000000 : ℝ)+(10062919554969409/100000000000000000000 : ℝ)=(50022019460313606059/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33976001072242709/100000000000000000000 : ℝ) ≤ ((37299171200940239823/37310000000000000000 : ℝ)+2*(572789504793/373100000000000 : ℝ)*(7377/50000 : ℝ))^(2137/512 : ℝ) := by
    rw [show (37299171200940239823/37310000000000000000 : ℝ)+2*(572789504793/373100000000000 : ℝ)*(7377/50000 : ℝ)=(10001627733489057/10000000000000000 : ℝ) by norm_num, show 1+2*(33976001072242709/100000000000000000000 : ℝ)=(50033976001072242709/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37299171200940239823/37310000000000000000 : ℝ)*(X 1 0+X 2 0)+(572789504793/373100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (11023/100000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (37299171200940239823/37310000000000000000 : ℝ)) (alpha := (572789504793/373100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37299171200940239823/37310000000000000000 : ℝ)*(X 0 1+X 2 1)+(572789504793/373100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (11023/100000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (37299171200940239823/37310000000000000000 : ℝ)) (alpha := (572789504793/373100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37299171200940239823/37310000000000000000 : ℝ)*(X 0 2+X 1 2)+(572789504793/373100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2137/512 : ℝ)) (lo := (11023/100000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (37299171200940239823/37310000000000000000 : ℝ)) (alpha := (572789504793/373100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1033734337/5000000000 : ℝ)*X 0 0+(5414588439/10000000000 : ℝ)*X 0 1+(5243290609/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674785273/5000000000 : ℝ)*X 1 0+(-215477749/1000000000 : ℝ)*X 1 1+(5243290653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349570523/10000000000 : ℝ)*X 2 0+(5243290657/10000000000 : ℝ)*X 2 1+(-538694379/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4333694393/10000000000 : ℝ)*X 0 0+(2079779479/5000000000 : ℝ)*X 0 1+(564339137/1250000000 : ℝ)*X 0 2+(4333694393/10000000000 : ℝ)*X 1 0+(2079779479/5000000000 : ℝ)*X 1 1+(564339137/1250000000 : ℝ)*X 1 2+(4333694393/10000000000 : ℝ)*X 2 0+(2079779479/5000000000 : ℝ)*X 2 1+(564339137/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2067481383/10000000000 : ℝ)*X 0 0+(2621952981/5000000000 : ℝ)*X 0 1+(5413969879/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265279433/500000000 : ℝ)*X 1 0+(-992049141/5000000000 : ℝ)*X 1 1+(2706984983/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652794531/5000000000 : ℝ)*X 2 0+(541396971/1000000000 : ℝ)*X 2 1+(-992049043/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1083430221/2500000000 : ℝ)*X 0 0+(1128359301/2500000000 : ℝ)*X 0 1+(4160841251/10000000000 : ℝ)*X 0 2+(1083430221/2500000000 : ℝ)*X 1 0+(1128359301/2500000000 : ℝ)*X 1 1+(4160841251/10000000000 : ℝ)*X 1 2+(1083430221/2500000000 : ℝ)*X 2 0+(1128359301/2500000000 : ℝ)*X 2 1+(4160841251/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1315_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (226733808109166764832259129/26650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32697729/2000000000000 : ℝ)*(base19) + (1511058039/100000000000000 : ℝ)*(base23) + (26407909/50000000000000 : ℝ)*(lower2) + (57596487/25000000000000 : ℝ)*(upper3) + (121753011/100000000000000 : ℝ)*(upper5) + (432678385557013/10000000000000 : ℝ)*(major0) + (432678385557013/10000000000000 : ℝ)*(major1) + (432678385557013/10000000000000 : ℝ)*(major2) + (233512877470429/4000000000000 : ℝ)*(sp0) + (2918926935886511/50000000000000 : ℝ)*(sp1) + (729731749450179/12500000000000 : ℝ)*(sp2) + (56313887789973/2000000000000 : ℝ)*(sp3) + (33569898747/100000000000000 : ℝ)*(sp4) + (8765693813/50000000000000 : ℝ)*(sp7) + (703927980221569/25000000000000 : ℝ)*(f.failure) + (5837855506659471/100000000000000 : ℝ)*(f.sum) + (2216863005611/746200000000000000000000000 : ℝ)*base66 + (1266494519472128699/373100000000000000000000000000000 : ℝ)*base67 + (2853691255952028699/373100000000000000000000000000000 : ℝ)*base69 + (663898223652171301/373100000000000000000000000000000 : ℝ)*base72 + (5310809329737/1865500000000000000000000000 : ℝ)*base73 + (198188478114771301/373100000000000000000000000000000 : ℝ)*base76 + (1949600519803428699/373100000000000000000000000000000 : ℝ)*base77 + (3625406981423628699/373100000000000000000000000000000 : ℝ)*base79 + (1243343559299/233187500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1761367/500000000000000000000 : ℝ)*base89 + (1761367/500000000000000000000 : ℝ)*base91 + (1761367/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (235953611937051201264932979/35875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83834607/6250000000000 : ℝ)*(base19) + (1018059009/50000000000000 : ℝ)*(base23) + (21681249/12500000000000 : ℝ)*(upper3) + (79524031/100000000000000 : ℝ)*(lower4) + (44338243/25000000000000 : ℝ)*(upper5) + (2179063348576283/50000000000000 : ℝ)*(major0) + (2179063348576283/50000000000000 : ℝ)*(major1) + (2179063348576283/50000000000000 : ℝ)*(major2) + (28876147697/100000000000000 : ℝ)*(sp1) + (40860477113/100000000000000 : ℝ)*(sp2) + (2940072242375721/50000000000000 : ℝ)*(sp4) + (2940057133625017/50000000000000 : ℝ)*(sp5) + (735012698519539/12500000000000 : ℝ)*(sp6) + (1418054345158439/50000000000000 : ℝ)*(sp7) + (1418054345158439/50000000000000 : ℝ)*(f.failure) + (2940072242375721/50000000000000 : ℝ)*(f.sum) + (256717476037/44843750000000000000000000 : ℝ)*base66 + (7253736802014007/143500000000000000000000000000000 : ℝ)*base68 + (250067079467985993/143500000000000000000000000000000 : ℝ)*base69 + (875256657055014007/143500000000000000000000000000000 : ℝ)*base72 + (296934037733/179375000000000000000000000 : ℝ)*base74 + (1762698284046514007/143500000000000000000000000000000 : ℝ)*base76 + (232728582338514007/143500000000000000000000000000000 : ℝ)*base78 + (1481952374231514007/143500000000000000000000000000000 : ℝ)*base80 + (676874661751/358750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3443777/1000000000000000000000 : ℝ)*base89 + (3443777/1000000000000000000000 : ℝ)*base91 + (3443777/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1315_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11023/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5537/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (147/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1315_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1315_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3243/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9669/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5537/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (147/1000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1315_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1315_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1315_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2137/512 : ℝ) ≤ p) (hpb : p ≤ (4275/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30733143/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3243/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9669/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5537/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (147/1000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1315_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

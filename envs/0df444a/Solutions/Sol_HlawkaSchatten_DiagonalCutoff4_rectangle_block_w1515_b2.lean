-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1515_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:56:24.346251+00:00
-- url     : https://prove2.me/submissions/57664037-9ea5-4650-8c01-5010e5b170df

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
theorem support_rectangle_w1515_s6_0 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675711407/5000000000 : ℝ)*x 0 + (5217788397/10000000000 : ℝ)*x 1 + (-1973727877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675711407/5000000000 : ℝ)^4527 ≤ (22287695734363/50000000000000 : ℝ)^3503 := by
    have hnat : (2675711407 : ℕ)^4527*50000000000000^3503 ≤ 22287695734363^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675711407 5000000000 22287695734363 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217788397/10000000000 : ℝ)^4527 ≤ (43142157528883/100000000000000 : ℝ)^3503 := by
    have hnat : (5217788397 : ℕ)^4527*100000000000000^3503 ≤ 43142157528883^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217788397 10000000000 43142157528883 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1973727877/10000000000 : ℝ)^4527 ≤ (12282450989563/100000000000000 : ℝ)^3503 := by
    have hnat : (1973727877 : ℕ)^4527*100000000000000^3503 ≤ 12282450989563^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973727877 10000000000 12282450989563 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675711407/5000000000 : ℝ), (5217788397/10000000000 : ℝ), (-1973727877/10000000000 : ℝ)] ![(22287695734363/50000000000000 : ℝ), (43142157528883/100000000000000 : ℝ), (12282450989563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675711407/5000000000 : ℝ)|^4527 ≤ (22287695734363/50000000000000 : ℝ)^3503
        have hw : |(2675711407/5000000000 : ℝ)|=(2675711407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217788397/10000000000 : ℝ)|^4527 ≤ (43142157528883/100000000000000 : ℝ)^3503
        have hw : |(5217788397/10000000000 : ℝ)|=(5217788397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1973727877/10000000000 : ℝ)|^4527 ≤ (12282450989563/100000000000000 : ℝ)^3503
        have hw : |(-1973727877/10000000000 : ℝ)|=(1973727877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s6_1 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-232952953/1250000000 : ℝ)*x 0 + (104377917/200000000 : ℝ)*x 1 + (1357931457/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (232952953/1250000000 : ℝ)^4527 ≤ (11404301357771/100000000000000 : ℝ)^3503 := by
    have hnat : (232952953 : ℕ)^4527*100000000000000^3503 ≤ 11404301357771^3503*1250000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232952953 1250000000 11404301357771 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104377917/200000000 : ℝ)^4527 ≤ (10788497834301/25000000000000 : ℝ)^3503 := by
    have hnat : (104377917 : ℕ)^4527*25000000000000^3503 ≤ 10788497834301^3503*200000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104377917 200000000 10788497834301 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357931457/2500000000 : ℝ)^4527 ≤ (22720853642023/50000000000000 : ℝ)^3503 := by
    have hnat : (1357931457 : ℕ)^4527*50000000000000^3503 ≤ 22720853642023^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357931457 2500000000 22720853642023 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-232952953/1250000000 : ℝ), (104377917/200000000 : ℝ), (1357931457/2500000000 : ℝ)] ![(11404301357771/100000000000000 : ℝ), (10788497834301/25000000000000 : ℝ), (22720853642023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-232952953/1250000000 : ℝ)|^4527 ≤ (11404301357771/100000000000000 : ℝ)^3503
        have hw : |(-232952953/1250000000 : ℝ)|=(232952953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104377917/200000000 : ℝ)|^4527 ≤ (10788497834301/25000000000000 : ℝ)^3503
        have hw : |(104377917/200000000 : ℝ)|=(104377917/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357931457/2500000000 : ℝ)|^4527 ≤ (22720853642023/50000000000000 : ℝ)^3503
        have hw : |(1357931457/2500000000 : ℝ)|=(1357931457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s6_2 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294943397/10000000000 : ℝ)*x 0 + (-109986917/625000000 : ℝ)*x 1 + (678965689/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294943397/10000000000 : ℝ)^4527 ≤ (8793671127029/20000000000000 : ℝ)^3503 := by
    have hnat : (5294943397 : ℕ)^4527*20000000000000^3503 ≤ 8793671127029^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294943397 10000000000 8793671127029 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109986917/625000000 : ℝ)^4527 ≤ (2117988096811/20000000000000 : ℝ)^3503 := by
    have hnat : (109986917 : ℕ)^4527*20000000000000^3503 ≤ 2117988096811^3503*625000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109986917 625000000 2117988096811 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678965689/1250000000 : ℝ)^4527 ≤ (45441703867603/100000000000000 : ℝ)^3503 := by
    have hnat : (678965689 : ℕ)^4527*100000000000000^3503 ≤ 45441703867603^3503*1250000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678965689 1250000000 45441703867603 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294943397/10000000000 : ℝ), (-109986917/625000000 : ℝ), (678965689/1250000000 : ℝ)] ![(8793671127029/20000000000000 : ℝ), (2117988096811/20000000000000 : ℝ), (45441703867603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294943397/10000000000 : ℝ)|^4527 ≤ (8793671127029/20000000000000 : ℝ)^3503
        have hw : |(5294943397/10000000000 : ℝ)|=(5294943397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109986917/625000000 : ℝ)|^4527 ≤ (2117988096811/20000000000000 : ℝ)^3503
        have hw : |(-109986917/625000000 : ℝ)|=(109986917/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678965689/1250000000 : ℝ)|^4527 ≤ (45441703867603/100000000000000 : ℝ)^3503
        have hw : |(678965689/1250000000 : ℝ)|=(678965689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s6_3 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294943437/10000000000 : ℝ)*x 0 + (2715862933/5000000000 : ℝ)*x 1 + (-14078321/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294943437/10000000000 : ℝ)^4527 ≤ (21984178032197/50000000000000 : ℝ)^3503 := by
    have hnat : (5294943437 : ℕ)^4527*50000000000000^3503 ≤ 21984178032197^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294943437 10000000000 21984178032197 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715862933/5000000000 : ℝ)^4527 ≤ (11360426923721/25000000000000 : ℝ)^3503 := by
    have hnat : (2715862933 : ℕ)^4527*25000000000000^3503 ≤ 11360426923721^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715862933 5000000000 11360426923721 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14078321/80000000 : ℝ)^4527 ≤ (10589936230127/100000000000000 : ℝ)^3503 := by
    have hnat : (14078321 : ℕ)^4527*100000000000000^3503 ≤ 10589936230127^3503*80000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14078321 80000000 10589936230127 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294943437/10000000000 : ℝ), (2715862933/5000000000 : ℝ), (-14078321/80000000 : ℝ)] ![(21984178032197/50000000000000 : ℝ), (11360426923721/25000000000000 : ℝ), (10589936230127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294943437/10000000000 : ℝ)|^4527 ≤ (21984178032197/50000000000000 : ℝ)^3503
        have hw : |(5294943437/10000000000 : ℝ)|=(5294943437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715862933/5000000000 : ℝ)|^4527 ≤ (11360426923721/25000000000000 : ℝ)^3503
        have hw : |(2715862933/5000000000 : ℝ)|=(2715862933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14078321/80000000 : ℝ)|^4527 ≤ (10589936230127/100000000000000 : ℝ)^3503
        have hw : |(-14078321/80000000 : ℝ)|=(14078321/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s6_4 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4268443217/10000000000 : ℝ)*x 0 + (4516124877/10000000000 : ℝ)*x 1 + (201624689/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4268443217/10000000000 : ℝ)^4527 ≤ (33280479140191/100000000000000 : ℝ)^3503 := by
    have hnat : (4268443217 : ℕ)^4527*100000000000000^3503 ≤ 33280479140191^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4268443217 10000000000 33280479140191 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4516124877/10000000000 : ℝ)^4527 ≤ (17898507878309/50000000000000 : ℝ)^3503 := by
    have hnat : (4516124877 : ℕ)^4527*50000000000000^3503 ≤ 17898507878309^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516124877 10000000000 17898507878309 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201624689/500000000 : ℝ)^4527 ≤ (30922505089319/100000000000000 : ℝ)^3503 := by
    have hnat : (201624689 : ℕ)^4527*100000000000000^3503 ≤ 30922505089319^3503*500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201624689 500000000 30922505089319 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4268443217/10000000000 : ℝ), (4516124877/10000000000 : ℝ), (201624689/500000000 : ℝ)] ![(33280479140191/100000000000000 : ℝ), (17898507878309/50000000000000 : ℝ), (30922505089319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4268443217/10000000000 : ℝ)|^4527 ≤ (33280479140191/100000000000000 : ℝ)^3503
        have hw : |(4268443217/10000000000 : ℝ)|=(4268443217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4516124877/10000000000 : ℝ)|^4527 ≤ (17898507878309/50000000000000 : ℝ)^3503
        have hw : |(4516124877/10000000000 : ℝ)|=(4516124877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(201624689/500000000 : ℝ)|^4527 ≤ (30922505089319/100000000000000 : ℝ)^3503
        have hw : |(201624689/500000000 : ℝ)|=(201624689/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1515_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10927/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10927/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7741/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10927/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10927/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10927/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10927/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10927/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10927/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10927/100000 : ℝ) ^ (4525/1024 : ℝ) ≤ (5638820233561001/100000000000000000000 : ℝ) := by
    have hpowers : (10927/100000 : ℝ)^4525 ≤ (5638820233561001/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10927 : ℕ)^4525*100000000000000000000^1024 ≤ 5638820233561001^1024*100000^4525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10927 100000 5638820233561001 100000000000000000000 4525 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10927/100000 : ℝ)) (X := (5638820233561001/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4525/1024 : ℝ) ≤ (26303531018725617/100000000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4525 ≤ (26303531018725617/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4525*100000000000000000000^1024 ≤ 26303531018725617^1024*100000^4525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 26303531018725617 100000000000000000000 4525 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (26303531018725617/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005638820233561001/50000000000000000000 : ℝ) ≤ (10000255200001031/10000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (50005638820233561001/50000000000000000000 : ℝ)^1024 ≤ (10000255200001031/10000000000000000 : ℝ)^4525 := by
      have hnat : (50005638820233561001 : ℕ)^1024*10000000000000000^4525 ≤ 10000255200001031^4525*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005638820233561001 50000000000000000000 10000255200001031 10000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000255200001031/10000000000000000 : ℝ)) (X := (50005638820233561001/50000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50015971175626143309/50000000000000000000 : ℝ) ≤ (5000361380404673/5000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (50015971175626143309/50000000000000000000 : ℝ)^1024 ≤ (5000361380404673/5000000000000000 : ℝ)^4525 := by
      have hnat : (50015971175626143309 : ℕ)^1024*5000000000000000^4525 ≤ 5000361380404673^4525*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015971175626143309 50000000000000000000 5000361380404673 5000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000361380404673/5000000000000000 : ℝ)) (X := (50015971175626143309/50000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026303531018725617/50000000000000000000 : ℝ) ≤ (10001190321617661/10000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (50026303531018725617/50000000000000000000 : ℝ)^1024 ≤ (10001190321617661/10000000000000000 : ℝ)^4525 := by
      have hnat : (50026303531018725617 : ℕ)^1024*10000000000000000^4525 ≤ 10001190321617661^4525*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026303531018725617 50000000000000000000 10001190321617661 10000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001190321617661/10000000000000000 : ℝ)) (X := (50026303531018725617/50000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5638820233561001/100000000000000000000 : ℝ) ≤ ((22775472308649890613/22780000000000000000 : ℝ)+2*(93512161663/91120000000000 : ℝ)*(10927/100000 : ℝ))^(4525/1024 : ℝ) := by
    rw [show (22775472308649890613/22780000000000000000 : ℝ)+2*(93512161663/91120000000000 : ℝ)*(10927/100000 : ℝ)=(10000255200001031/10000000000000000 : ℝ) by norm_num, show 1+2*(5638820233561001/100000000000000000000 : ℝ)=(50005638820233561001/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26303531018725617/100000000000000000000 : ℝ)+(5638820233561001/100000000000000000000 : ℝ) ≤ ((22775472308649890613/22780000000000000000 : ℝ)+(93512161663/91120000000000 : ℝ)*((15483/100000 : ℝ)+(10927/100000 : ℝ)))^(4525/1024 : ℝ) := by
    rw [show (22775472308649890613/22780000000000000000 : ℝ)+(93512161663/91120000000000 : ℝ)*((15483/100000 : ℝ)+(10927/100000 : ℝ))=(5000361380404673/5000000000000000 : ℝ) by norm_num, show 1+(26303531018725617/100000000000000000000 : ℝ)+(5638820233561001/100000000000000000000 : ℝ)=(50015971175626143309/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26303531018725617/100000000000000000000 : ℝ) ≤ ((22775472308649890613/22780000000000000000 : ℝ)+2*(93512161663/91120000000000 : ℝ)*(15483/100000 : ℝ))^(4525/1024 : ℝ) := by
    rw [show (22775472308649890613/22780000000000000000 : ℝ)+2*(93512161663/91120000000000 : ℝ)*(15483/100000 : ℝ)=(10001190321617661/10000000000000000 : ℝ) by norm_num, show 1+2*(26303531018725617/100000000000000000000 : ℝ)=(50026303531018725617/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22775472308649890613/22780000000000000000 : ℝ)*(X 1 0+X 2 0)+(93512161663/91120000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (10927/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (22775472308649890613/22780000000000000000 : ℝ)) (alpha := (93512161663/91120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22775472308649890613/22780000000000000000 : ℝ)*(X 0 1+X 2 1)+(93512161663/91120000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (10927/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (22775472308649890613/22780000000000000000 : ℝ)) (alpha := (93512161663/91120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22775472308649890613/22780000000000000000 : ℝ)*(X 0 2+X 1 2)+(93512161663/91120000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (10927/100000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (22775472308649890613/22780000000000000000 : ℝ)) (alpha := (93512161663/91120000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2675711407/5000000000 : ℝ)*X 2 0+(5217788397/10000000000 : ℝ)*X 2 1+(-1973727877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s6_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-232952953/1250000000 : ℝ)*X 0 0+(104377917/200000000 : ℝ)*X 0 1+(1357931457/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s6_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5294943397/10000000000 : ℝ)*X 1 0+(-109986917/625000000 : ℝ)*X 1 1+(678965689/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s6_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5294943437/10000000000 : ℝ)*X 2 0+(2715862933/5000000000 : ℝ)*X 2 1+(-14078321/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s6_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4268443217/10000000000 : ℝ)*X 0 0+(4516124877/10000000000 : ℝ)*X 0 1+(201624689/500000000 : ℝ)*X 0 2+(4268443217/10000000000 : ℝ)*X 1 0+(4516124877/10000000000 : ℝ)*X 1 1+(201624689/500000000 : ℝ)*X 1 2+(4268443217/10000000000 : ℝ)*X 2 0+(4516124877/10000000000 : ℝ)*X 2 1+(201624689/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s6_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (224062234892303589540429807/56950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (240042437/25000000000000 : ℝ)*(base19) + (123552031/10000000000000 : ℝ)*(base23) + (34055377/50000000000000 : ℝ)*(lower1) + (222046009/100000000000000 : ℝ)*(upper3) + (4595671/12500000000000 : ℝ)*(lower4) + (115503789/100000000000000 : ℝ)*(upper5) + (169156805091887/5000000000000 : ℝ)*(major0) + (169156805091887/5000000000000 : ℝ)*(major1) + (169156805091887/5000000000000 : ℝ)*(major2) + (3994240051/25000000000000 : ℝ)*(sp0) + (587322542484343/12500000000000 : ℝ)*(sp1) + (1174644844926249/25000000000000 : ℝ)*(sp2) + (469856312739423/10000000000000 : ℝ)*(sp3) + (1033845866327567/50000000000000 : ℝ)*(sp4) + (1033845866327567/50000000000000 : ℝ)*(f.failure) + (587322542484343/12500000000000 : ℝ)*(f.sum) + (5308046342853/1139000000000000000000000000 : ℝ)*base66 + (958595920576193269/113900000000000000000000000000000 : ℝ)*base68 + (1553038762511206731/113900000000000000000000000000000 : ℝ)*base69 + (3262856314126993269/113900000000000000000000000000000 : ℝ)*base72 + (1704324036771/1139000000000000000000000000 : ℝ)*base73 + (7642432328623206731/113900000000000000000000000000000 : ℝ)*base75 + (982452829432406731/113900000000000000000000000000000 : ℝ)*base77 + (971930059248606731/113900000000000000000000000000000 : ℝ)*base79 + (4434382138587/1139000000000000000000000000 : ℝ)*base81 + (7905907/5000000000000000000000 : ℝ)*base90 + (7905907/5000000000000000000000 : ℝ)*base92 + (7905907/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1515_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10927/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10927/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1515_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1515_s7_0 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1863596417/10000000000 : ℝ)*x 0 + (2716419101/5000000000 : ℝ)*x 1 + (521779047/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1863596417/10000000000 : ℝ)^4527 ≤ (2851021549563/25000000000000 : ℝ)^3503 := by
    have hnat : (1863596417 : ℕ)^4527*25000000000000^3503 ≤ 2851021549563^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863596417 10000000000 2851021549563 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716419101/5000000000 : ℝ)^4527 ≤ (11363433527213/25000000000000 : ℝ)^3503 := by
    have hnat : (2716419101 : ℕ)^4527*25000000000000^3503 ≤ 11363433527213^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716419101 5000000000 11363433527213 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521779047/1000000000 : ℝ)^4527 ≤ (21571089839731/50000000000000 : ℝ)^3503 := by
    have hnat : (521779047 : ℕ)^4527*50000000000000^3503 ≤ 21571089839731^3503*1000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521779047 1000000000 21571089839731 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1863596417/10000000000 : ℝ), (2716419101/5000000000 : ℝ), (521779047/1000000000 : ℝ)] ![(2851021549563/25000000000000 : ℝ), (11363433527213/25000000000000 : ℝ), (21571089839731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1863596417/10000000000 : ℝ)|^4527 ≤ (2851021549563/25000000000000 : ℝ)^3503
        have hw : |(-1863596417/10000000000 : ℝ)|=(1863596417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716419101/5000000000 : ℝ)|^4527 ≤ (11363433527213/25000000000000 : ℝ)^3503
        have hw : |(2716419101/5000000000 : ℝ)|=(2716419101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521779047/1000000000 : ℝ)|^4527 ≤ (21571089839731/50000000000000 : ℝ)^3503
        have hw : |(521779047/1000000000 : ℝ)|=(521779047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s7_1 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351421379/10000000000 : ℝ)*x 0 + (-1973726241/10000000000 : ℝ)*x 1 + (5217791073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351421379/10000000000 : ℝ)^4527 ≤ (2785961001349/6250000000000 : ℝ)^3503 := by
    have hnat : (5351421379 : ℕ)^4527*6250000000000^3503 ≤ 2785961001349^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351421379 10000000000 2785961001349 6250000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1973726241/10000000000 : ℝ)^4527 ≤ (1228243783273/10000000000000 : ℝ)^3503 := by
    have hnat : (1973726241 : ℕ)^4527*10000000000000^3503 ≤ 1228243783273^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973726241 10000000000 1228243783273 10000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217791073/10000000000 : ℝ)^4527 ≤ (10785546530671/25000000000000 : ℝ)^3503 := by
    have hnat : (5217791073 : ℕ)^4527*25000000000000^3503 ≤ 10785546530671^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217791073 10000000000 10785546530671 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351421379/10000000000 : ℝ), (-1973726241/10000000000 : ℝ), (5217791073/10000000000 : ℝ)] ![(2785961001349/6250000000000 : ℝ), (1228243783273/10000000000000 : ℝ), (10785546530671/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351421379/10000000000 : ℝ)|^4527 ≤ (2785961001349/6250000000000 : ℝ)^3503
        have hw : |(5351421379/10000000000 : ℝ)|=(5351421379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1973726241/10000000000 : ℝ)|^4527 ≤ (1228243783273/10000000000000 : ℝ)^3503
        have hw : |(-1973726241/10000000000 : ℝ)|=(1973726241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217791073/10000000000 : ℝ)|^4527 ≤ (10785546530671/25000000000000 : ℝ)^3503
        have hw : |(5217791073/10000000000 : ℝ)|=(5217791073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s7_2 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351421357/10000000000 : ℝ)*x 0 + (652223843/1250000000 : ℝ)*x 1 + (-1973726709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351421357/10000000000 : ℝ)^4527 ≤ (11143843946191/25000000000000 : ℝ)^3503 := by
    have hnat : (5351421357 : ℕ)^4527*25000000000000^3503 ≤ 11143843946191^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351421357 10000000000 11143843946191 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652223843/1250000000 : ℝ)^4527 ≤ (10785545651807/25000000000000 : ℝ)^3503 := by
    have hnat : (652223843 : ℕ)^4527*25000000000000^3503 ≤ 10785545651807^3503*1250000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652223843 1250000000 10785545651807 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1973726709/10000000000 : ℝ)^4527 ≤ (614122079821/5000000000000 : ℝ)^3503 := by
    have hnat : (1973726709 : ℕ)^4527*5000000000000^3503 ≤ 614122079821^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1973726709 10000000000 614122079821 5000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351421357/10000000000 : ℝ), (652223843/1250000000 : ℝ), (-1973726709/10000000000 : ℝ)] ![(11143843946191/25000000000000 : ℝ), (10785545651807/25000000000000 : ℝ), (614122079821/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351421357/10000000000 : ℝ)|^4527 ≤ (11143843946191/25000000000000 : ℝ)^3503
        have hw : |(5351421357/10000000000 : ℝ)|=(5351421357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652223843/1250000000 : ℝ)|^4527 ≤ (10785545651807/25000000000000 : ℝ)^3503
        have hw : |(652223843/1250000000 : ℝ)|=(652223843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1973726709/10000000000 : ℝ)|^4527 ≤ (614122079821/5000000000000 : ℝ)^3503
        have hw : |(-1973726709/10000000000 : ℝ)|=(1973726709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s7_3 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2134188601/5000000000 : ℝ)*x 0 + (1007491511/2500000000 : ℝ)*x 1 + (903726959/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134188601/5000000000 : ℝ)^4527 ≤ (33279813971093/100000000000000 : ℝ)^3503 := by
    have hnat : (2134188601 : ℕ)^4527*100000000000000^3503 ≤ 33279813971093^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134188601 5000000000 33279813971093 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007491511/2500000000 : ℝ)^4527 ≤ (15448728827777/50000000000000 : ℝ)^3503 := by
    have hnat : (1007491511 : ℕ)^4527*50000000000000^3503 ≤ 15448728827777^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007491511 2500000000 15448728827777 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903726959/2000000000 : ℝ)^4527 ≤ (35822728359547/100000000000000 : ℝ)^3503 := by
    have hnat : (903726959 : ℕ)^4527*100000000000000^3503 ≤ 35822728359547^3503*2000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903726959 2000000000 35822728359547 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2134188601/5000000000 : ℝ), (1007491511/2500000000 : ℝ), (903726959/2000000000 : ℝ)] ![(33279813971093/100000000000000 : ℝ), (15448728827777/50000000000000 : ℝ), (35822728359547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2134188601/5000000000 : ℝ)|^4527 ≤ (33279813971093/100000000000000 : ℝ)^3503
        have hw : |(2134188601/5000000000 : ℝ)|=(2134188601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1007491511/2500000000 : ℝ)|^4527 ≤ (15448728827777/50000000000000 : ℝ)^3503
        have hw : |(1007491511/2500000000 : ℝ)|=(1007491511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903726959/2000000000 : ℝ)|^4527 ≤ (35822728359547/100000000000000 : ℝ)^3503
        have hw : |(903726959/2000000000 : ℝ)|=(903726959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s7_4 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1863625767/10000000000 : ℝ)*x 0 + (2609449097/5000000000 : ℝ)*x 1 + (1086344389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1863625767/10000000000 : ℝ)^4527 ≤ (11404318305171/100000000000000 : ℝ)^3503 := by
    have hnat : (1863625767 : ℕ)^4527*100000000000000^3503 ≤ 11404318305171^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863625767 10000000000 11404318305171 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609449097/5000000000 : ℝ)^4527 ≤ (43154016385047/100000000000000 : ℝ)^3503 := by
    have hnat : (2609449097 : ℕ)^4527*100000000000000^3503 ≤ 43154016385047^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609449097 5000000000 43154016385047 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086344389/2000000000 : ℝ)^4527 ≤ (45441665302879/100000000000000 : ℝ)^3503 := by
    have hnat : (1086344389 : ℕ)^4527*100000000000000^3503 ≤ 45441665302879^3503*2000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086344389 2000000000 45441665302879 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1863625767/10000000000 : ℝ), (2609449097/5000000000 : ℝ), (1086344389/2000000000 : ℝ)] ![(11404318305171/100000000000000 : ℝ), (43154016385047/100000000000000 : ℝ), (45441665302879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1863625767/10000000000 : ℝ)|^4527 ≤ (11404318305171/100000000000000 : ℝ)^3503
        have hw : |(-1863625767/10000000000 : ℝ)|=(1863625767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609449097/5000000000 : ℝ)|^4527 ≤ (43154016385047/100000000000000 : ℝ)^3503
        have hw : |(2609449097/5000000000 : ℝ)|=(2609449097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086344389/2000000000 : ℝ)|^4527 ≤ (45441665302879/100000000000000 : ℝ)^3503
        have hw : |(1086344389/2000000000 : ℝ)|=(1086344389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s7_5 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323735867/2500000000 : ℝ)*x 0 + (271586097/500000000 : ℝ)*x 1 + (-1759795539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323735867/2500000000 : ℝ)^4527 ≤ (21984178198531/50000000000000 : ℝ)^3503 := by
    have hnat : (1323735867 : ℕ)^4527*50000000000000^3503 ≤ 21984178198531^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323735867 2500000000 21984178198531 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271586097/500000000 : ℝ)^4527 ≤ (22720832624411/50000000000000 : ℝ)^3503 := by
    have hnat : (271586097 : ℕ)^4527*50000000000000^3503 ≤ 22720832624411^3503*500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271586097 500000000 22720832624411 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1759795539/10000000000 : ℝ)^4527 ≤ (423599133357/4000000000000 : ℝ)^3503 := by
    have hnat : (1759795539 : ℕ)^4527*4000000000000^3503 ≤ 423599133357^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759795539 10000000000 423599133357 4000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323735867/2500000000 : ℝ), (271586097/500000000 : ℝ), (-1759795539/10000000000 : ℝ)] ![(21984178198531/50000000000000 : ℝ), (22720832624411/50000000000000 : ℝ), (423599133357/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323735867/2500000000 : ℝ)|^4527 ≤ (21984178198531/50000000000000 : ℝ)^3503
        have hw : |(1323735867/2500000000 : ℝ)|=(1323735867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271586097/500000000 : ℝ)|^4527 ≤ (22720832624411/50000000000000 : ℝ)^3503
        have hw : |(271586097/500000000 : ℝ)|=(271586097/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1759795539/10000000000 : ℝ)|^4527 ≤ (423599133357/4000000000000 : ℝ)^3503
        have hw : |(-1759795539/10000000000 : ℝ)|=(1759795539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_s7_6 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (426844307/1000000000 : ℝ)*x 0 + (4516117377/10000000000 : ℝ)*x 1 + (4032501683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (426844307/1000000000 : ℝ)^4527 ≤ (33280477659011/100000000000000 : ℝ)^3503 := by
    have hnat : (426844307 : ℕ)^4527*100000000000000^3503 ≤ 33280477659011^3503*1000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426844307 1000000000 33280477659011 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4516117377/10000000000 : ℝ)^4527 ≤ (894923473247/2500000000000 : ℝ)^3503 := by
    have hnat : (4516117377 : ℕ)^4527*2500000000000^3503 ≤ 894923473247^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516117377 10000000000 894923473247 2500000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4032501683/10000000000 : ℝ)^4527 ≤ (30922583407651/100000000000000 : ℝ)^3503 := by
    have hnat : (4032501683 : ℕ)^4527*100000000000000^3503 ≤ 30922583407651^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032501683 10000000000 30922583407651 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(426844307/1000000000 : ℝ), (4516117377/10000000000 : ℝ), (4032501683/10000000000 : ℝ)] ![(33280477659011/100000000000000 : ℝ), (894923473247/2500000000000 : ℝ), (30922583407651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(426844307/1000000000 : ℝ)|^4527 ≤ (33280477659011/100000000000000 : ℝ)^3503
        have hw : |(426844307/1000000000 : ℝ)|=(426844307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4516117377/10000000000 : ℝ)|^4527 ≤ (894923473247/2500000000000 : ℝ)^3503
        have hw : |(4516117377/10000000000 : ℝ)|=(4516117377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4032501683/10000000000 : ℝ)|^4527 ≤ (30922583407651/100000000000000 : ℝ)^3503
        have hw : |(4032501683/10000000000 : ℝ)|=(4032501683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1515_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10927/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (683/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7741/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10927/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10927/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10927/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10927/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10927/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10927/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10927/100000 : ℝ) ^ (4525/1024 : ℝ) ≤ (5638820233561001/100000000000000000000 : ℝ) := by
    have hpowers : (10927/100000 : ℝ)^4525 ≤ (5638820233561001/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10927 : ℕ)^4525*100000000000000000000^1024 ≤ 5638820233561001^1024*100000^4525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10927 100000 5638820233561001 100000000000000000000 4525 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10927/100000 : ℝ)) (X := (5638820233561001/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7741/50000 : ℝ) ^ (4525/1024 : ℝ) ≤ (26296024654815199/100000000000000000000 : ℝ) := by
    have hpowers : (7741/50000 : ℝ)^4525 ≤ (26296024654815199/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7741 : ℕ)^4525*100000000000000000000^1024 ≤ 26296024654815199^1024*50000^4525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7741 50000 26296024654815199 100000000000000000000 4525 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7741/50000 : ℝ)) (X := (26296024654815199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005638820233561001/50000000000000000000 : ℝ) ≤ (10000255200001031/10000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (50005638820233561001/50000000000000000000 : ℝ)^1024 ≤ (10000255200001031/10000000000000000 : ℝ)^4525 := by
      have hnat : (50005638820233561001 : ℕ)^1024*10000000000000000^4525 ≤ 10000255200001031^4525*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005638820233561001 50000000000000000000 10000255200001031 10000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000255200001031/10000000000000000 : ℝ)) (X := (50005638820233561001/50000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (500159674224441881/500000000000000000 : ℝ) ≤ (5000361295491769/5000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (500159674224441881/500000000000000000 : ℝ)^1024 ≤ (5000361295491769/5000000000000000 : ℝ)^4525 := by
      have hnat : (500159674224441881 : ℕ)^1024*5000000000000000^4525 ≤ 5000361295491769^4525*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500159674224441881 500000000000000000 5000361295491769 5000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000361295491769/5000000000000000 : ℝ)) (X := (500159674224441881/500000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026296024654815199/50000000000000000000 : ℝ) ≤ (2000237996393209/2000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (50026296024654815199/50000000000000000000 : ℝ)^1024 ≤ (2000237996393209/2000000000000000 : ℝ)^4525 := by
      have hnat : (50026296024654815199 : ℕ)^1024*2000000000000000^4525 ≤ 2000237996393209^4525*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026296024654815199 50000000000000000000 2000237996393209 2000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000237996393209/2000000000000000 : ℝ)) (X := (50026296024654815199/50000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5638820233561001/100000000000000000000 : ℝ) ≤ ((45540948073472988227/45550000000000000000 : ℝ)+2*(467390982507/455500000000000 : ℝ)*(10927/100000 : ℝ))^(4525/1024 : ℝ) := by
    rw [show (45540948073472988227/45550000000000000000 : ℝ)+2*(467390982507/455500000000000 : ℝ)*(10927/100000 : ℝ)=(10000255200001031/10000000000000000 : ℝ) by norm_num, show 1+2*(5638820233561001/100000000000000000000 : ℝ)=(50005638820233561001/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26296024654815199/100000000000000000000 : ℝ)+(5638820233561001/100000000000000000000 : ℝ) ≤ ((45540948073472988227/45550000000000000000 : ℝ)+(467390982507/455500000000000 : ℝ)*((7741/50000 : ℝ)+(10927/100000 : ℝ)))^(4525/1024 : ℝ) := by
    rw [show (45540948073472988227/45550000000000000000 : ℝ)+(467390982507/455500000000000 : ℝ)*((7741/50000 : ℝ)+(10927/100000 : ℝ))=(5000361295491769/5000000000000000 : ℝ) by norm_num, show 1+(26296024654815199/100000000000000000000 : ℝ)+(5638820233561001/100000000000000000000 : ℝ)=(500159674224441881/500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26296024654815199/100000000000000000000 : ℝ) ≤ ((45540948073472988227/45550000000000000000 : ℝ)+2*(467390982507/455500000000000 : ℝ)*(7741/50000 : ℝ))^(4525/1024 : ℝ) := by
    rw [show (45540948073472988227/45550000000000000000 : ℝ)+2*(467390982507/455500000000000 : ℝ)*(7741/50000 : ℝ)=(2000237996393209/2000000000000000 : ℝ) by norm_num, show 1+2*(26296024654815199/100000000000000000000 : ℝ)=(50026296024654815199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45540948073472988227/45550000000000000000 : ℝ)*(X 1 0+X 2 0)+(467390982507/455500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (10927/100000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (45540948073472988227/45550000000000000000 : ℝ)) (alpha := (467390982507/455500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45540948073472988227/45550000000000000000 : ℝ)*(X 0 1+X 2 1)+(467390982507/455500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (10927/100000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (45540948073472988227/45550000000000000000 : ℝ)) (alpha := (467390982507/455500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45540948073472988227/45550000000000000000 : ℝ)*(X 0 2+X 1 2)+(467390982507/455500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (10927/100000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (45540948073472988227/45550000000000000000 : ℝ)) (alpha := (467390982507/455500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1863596417/10000000000 : ℝ)*X 0 0+(2716419101/5000000000 : ℝ)*X 0 1+(521779047/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351421379/10000000000 : ℝ)*X 1 0+(-1973726241/10000000000 : ℝ)*X 1 1+(5217791073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351421357/10000000000 : ℝ)*X 2 0+(652223843/1250000000 : ℝ)*X 2 1+(-1973726709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2134188601/5000000000 : ℝ)*X 0 0+(1007491511/2500000000 : ℝ)*X 0 1+(903726959/2000000000 : ℝ)*X 0 2+(2134188601/5000000000 : ℝ)*X 1 0+(1007491511/2500000000 : ℝ)*X 1 1+(903726959/2000000000 : ℝ)*X 1 2+(2134188601/5000000000 : ℝ)*X 2 0+(1007491511/2500000000 : ℝ)*X 2 1+(903726959/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1863625767/10000000000 : ℝ)*X 0 0+(2609449097/5000000000 : ℝ)*X 0 1+(1086344389/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323735867/2500000000 : ℝ)*X 2 0+(271586097/500000000 : ℝ)*X 2 1+(-1759795539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s7_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((426844307/1000000000 : ℝ)*X 0 0+(4516117377/10000000000 : ℝ)*X 0 1+(4032501683/10000000000 : ℝ)*X 0 2+(426844307/1000000000 : ℝ)*X 1 0+(4516117377/10000000000 : ℝ)*X 1 1+(4032501683/10000000000 : ℝ)*X 1 2+(426844307/1000000000 : ℝ)*X 2 0+(4516117377/10000000000 : ℝ)*X 2 1+(4032501683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_s7_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2001934533274138598004789987/569375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13363901/10000000000000 : ℝ)*(base23) + (15120289/50000000000000 : ℝ)*(lower2) + (5369243/4000000000000 : ℝ)*(lower4) + (138289147/100000000000000 : ℝ)*(lower5) + (837068440989373/25000000000000 : ℝ)*(major0) + (837068440989373/25000000000000 : ℝ)*(major1) + (837068440989373/25000000000000 : ℝ)*(major2) + (2325074798259003/50000000000000 : ℝ)*(sp0) + (4650162703743641/100000000000000 : ℝ)*(sp1) + (4650158631523679/100000000000000 : ℝ)*(sp2) + (1023190002430383/50000000000000 : ℝ)*(sp3) + (2621445127/20000000000000 : ℝ)*(sp4) + (492322619/12500000000000 : ℝ)*(sp5) + (4702109867/100000000000000 : ℝ)*(sp6) + (2046384706970633/100000000000000 : ℝ)*(f.failure) + (4650162703743641/100000000000000 : ℝ)*(f.sum) + (107327659514319/22775000000000000000000000000 : ℝ)*base65 + (2394095042578461671/1138750000000000000000000000000000 : ℝ)*base67 + (6046394045635288329/1138750000000000000000000000000000 : ℝ)*base70 + (4357103726633461671/1138750000000000000000000000000000 : ℝ)*base71 + (33384477325053/11387500000000000000000000000 : ℝ)*base74 + (2748635421982788329/1138750000000000000000000000000000 : ℝ)*base76 + (3843831522883461671/1138750000000000000000000000000000 : ℝ)*base77 + (8864648304085961671/1138750000000000000000000000000000 : ℝ)*base79 + (220439178839/5693750000000000000000000000 : ℝ)*base82 + (45556293/10000000000000000000000 : ℝ)*base90 + (45556293/10000000000000000000000 : ℝ)*base92 + (45556293/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1515_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10927/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (683/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1515_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1515_box_0 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1650506627/10000000000 : ℝ)*x 0 + (5402508117/10000000000 : ℝ)*x 1 + (5402506047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1650506627/10000000000 : ℝ)^4527 ≤ (974788674031/10000000000000 : ℝ)^3503 := by
    have hnat : (1650506627 : ℕ)^4527*10000000000000^3503 ≤ 974788674031^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1650506627 10000000000 974788674031 10000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402508117/10000000000 : ℝ)^4527 ≤ (45126067795901/100000000000000 : ℝ)^3503 := by
    have hnat : (5402508117 : ℕ)^4527*100000000000000^3503 ≤ 45126067795901^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402508117 10000000000 45126067795901 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402506047/10000000000 : ℝ)^4527 ≤ (45126045451293/100000000000000 : ℝ)^3503 := by
    have hnat : (5402506047 : ℕ)^4527*100000000000000^3503 ≤ 45126045451293^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402506047 10000000000 45126045451293 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1650506627/10000000000 : ℝ), (5402508117/10000000000 : ℝ), (5402506047/10000000000 : ℝ)] ![(974788674031/10000000000000 : ℝ), (45126067795901/100000000000000 : ℝ), (45126045451293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1650506627/10000000000 : ℝ)|^4527 ≤ (974788674031/10000000000000 : ℝ)^3503
        have hw : |(-1650506627/10000000000 : ℝ)|=(1650506627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402508117/10000000000 : ℝ)|^4527 ≤ (45126067795901/100000000000000 : ℝ)^3503
        have hw : |(5402508117/10000000000 : ℝ)|=(5402508117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402506047/10000000000 : ℝ)|^4527 ≤ (45126045451293/100000000000000 : ℝ)^3503
        have hw : |(5402506047/10000000000 : ℝ)|=(5402506047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_box_1 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1317703897/2500000000 : ℝ)*x 0 + (-91660371/500000000 : ℝ)*x 1 + (8441417/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1317703897/2500000000 : ℝ)^4527 ≤ (682962614761/1562500000000 : ℝ)^3503 := by
    have hnat : (1317703897 : ℕ)^4527*1562500000000^3503 ≤ 682962614761^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1317703897 2500000000 682962614761 1562500000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91660371/500000000 : ℝ)^4527 ≤ (11164338193219/100000000000000 : ℝ)^3503 := by
    have hnat : (91660371 : ℕ)^4527*100000000000000^3503 ≤ 11164338193219^3503*500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91660371 500000000 11164338193219 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8441417/15625000 : ℝ)^4527 ≤ (11281513610777/25000000000000 : ℝ)^3503 := by
    have hnat : (8441417 : ℕ)^4527*25000000000000^3503 ≤ 11281513610777^3503*15625000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8441417 15625000 11281513610777 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1317703897/2500000000 : ℝ), (-91660371/500000000 : ℝ), (8441417/15625000 : ℝ)] ![(682962614761/1562500000000 : ℝ), (11164338193219/100000000000000 : ℝ), (11281513610777/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1317703897/2500000000 : ℝ)|^4527 ≤ (682962614761/1562500000000 : ℝ)^3503
        have hw : |(1317703897/2500000000 : ℝ)|=(1317703897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-91660371/500000000 : ℝ)|^4527 ≤ (11164338193219/100000000000000 : ℝ)^3503
        have hw : |(-91660371/500000000 : ℝ)|=(91660371/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8441417/15625000 : ℝ)|^4527 ≤ (11281513610777/25000000000000 : ℝ)^3503
        have hw : |(8441417/15625000 : ℝ)|=(8441417/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_box_2 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270816691/10000000000 : ℝ)*x 0 + (2701253509/5000000000 : ℝ)*x 1 + (-1833205729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270816691/10000000000 : ℝ)^4527 ≤ (10927404791363/25000000000000 : ℝ)^3503 := by
    have hnat : (5270816691 : ℕ)^4527*25000000000000^3503 ≤ 10927404791363^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270816691 10000000000 10927404791363 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701253509/5000000000 : ℝ)^4527 ≤ (45126055932749/100000000000000 : ℝ)^3503 := by
    have hnat : (2701253509 : ℕ)^4527*100000000000000^3503 ≤ 45126055932749^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701253509 5000000000 45126055932749 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1833205729/10000000000 : ℝ)^4527 ≤ (1116432488453/10000000000000 : ℝ)^3503 := by
    have hnat : (1833205729 : ℕ)^4527*10000000000000^3503 ≤ 1116432488453^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833205729 10000000000 1116432488453 10000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270816691/10000000000 : ℝ), (2701253509/5000000000 : ℝ), (-1833205729/10000000000 : ℝ)] ![(10927404791363/25000000000000 : ℝ), (45126055932749/100000000000000 : ℝ), (1116432488453/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270816691/10000000000 : ℝ)|^4527 ≤ (10927404791363/25000000000000 : ℝ)^3503
        have hw : |(5270816691/10000000000 : ℝ)|=(5270816691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701253509/5000000000 : ℝ)|^4527 ≤ (45126055932749/100000000000000 : ℝ)^3503
        have hw : |(2701253509/5000000000 : ℝ)|=(2701253509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1833205729/10000000000 : ℝ)|^4527 ≤ (1116432488453/10000000000000 : ℝ)^3503
        have hw : |(-1833205729/10000000000 : ℝ)|=(1833205729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_box_3 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (178852079/400000000 : ℝ)*x 0 + (65216821/156250000 : ℝ)*x 1 + (417387841/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (178852079/400000000 : ℝ)^4527 ≤ (17669268479317/50000000000000 : ℝ)^3503 := by
    have hnat : (178852079 : ℕ)^4527*50000000000000^3503 ≤ 17669268479317^3503*400000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178852079 400000000 17669268479317 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65216821/156250000 : ℝ)^4527 ≤ (32330722173889/100000000000000 : ℝ)^3503 := by
    have hnat : (65216821 : ℕ)^4527*100000000000000^3503 ≤ 32330722173889^3503*156250000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65216821 156250000 32330722173889 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417387841/1000000000 : ℝ)^4527 ≤ (3233074085307/10000000000000 : ℝ)^3503 := by
    have hnat : (417387841 : ℕ)^4527*10000000000000^3503 ≤ 3233074085307^3503*1000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417387841 1000000000 3233074085307 10000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(178852079/400000000 : ℝ), (65216821/156250000 : ℝ), (417387841/1000000000 : ℝ)] ![(17669268479317/50000000000000 : ℝ), (32330722173889/100000000000000 : ℝ), (3233074085307/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(178852079/400000000 : ℝ)|^4527 ≤ (17669268479317/50000000000000 : ℝ)^3503
        have hw : |(178852079/400000000 : ℝ)|=(178852079/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(65216821/156250000 : ℝ)|^4527 ≤ (32330722173889/100000000000000 : ℝ)^3503
        have hw : |(65216821/156250000 : ℝ)|=(65216821/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(417387841/1000000000 : ℝ)|^4527 ≤ (3233074085307/10000000000000 : ℝ)^3503
        have hw : |(417387841/1000000000 : ℝ)|=(417387841/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_box_4 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-104105973/500000000 : ℝ)*x 0 + (327732737/625000000 : ℝ)*x 1 + (2621860799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104105973/500000000 : ℝ)^4527 ≤ (13161052495583/100000000000000 : ℝ)^3503 := by
    have hnat : (104105973 : ℕ)^4527*100000000000000^3503 ≤ 13161052495583^3503*500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104105973 500000000 13161052495583 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327732737/625000000 : ℝ)^4527 ≤ (43419485486597/100000000000000 : ℝ)^3503 := by
    have hnat : (327732737 : ℕ)^4527*100000000000000^3503 ≤ 43419485486597^3503*625000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327732737 625000000 43419485486597 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621860799/5000000000 : ℝ)^4527 ≤ (21709731004549/50000000000000 : ℝ)^3503 := by
    have hnat : (2621860799 : ℕ)^4527*50000000000000^3503 ≤ 21709731004549^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621860799 5000000000 21709731004549 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104105973/500000000 : ℝ), (327732737/625000000 : ℝ), (2621860799/5000000000 : ℝ)] ![(13161052495583/100000000000000 : ℝ), (43419485486597/100000000000000 : ℝ), (21709731004549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104105973/500000000 : ℝ)|^4527 ≤ (13161052495583/100000000000000 : ℝ)^3503
        have hw : |(-104105973/500000000 : ℝ)|=(104105973/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327732737/625000000 : ℝ)|^4527 ≤ (43419485486597/100000000000000 : ℝ)^3503
        have hw : |(327732737/625000000 : ℝ)|=(327732737/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621860799/5000000000 : ℝ)|^4527 ≤ (21709731004549/50000000000000 : ℝ)^3503
        have hw : |(2621860799/5000000000 : ℝ)|=(2621860799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_box_5 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215253541/400000000 : ℝ)*x 0 + (-949373981/5000000000 : ℝ)*x 1 + (5243723353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215253541/400000000 : ℝ)^4527 ≤ (44897683690659/100000000000000 : ℝ)^3503 := by
    have hnat : (215253541 : ℕ)^4527*100000000000000^3503 ≤ 44897683690659^3503*400000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215253541 400000000 44897683690659 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (949373981/5000000000 : ℝ)^4527 ≤ (2336567100513/20000000000000 : ℝ)^3503 := by
    have hnat : (949373981 : ℕ)^4527*20000000000000^3503 ≤ 2336567100513^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949373981 5000000000 2336567100513 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243723353/10000000000 : ℝ)^4527 ≤ (43419480788957/100000000000000 : ℝ)^3503 := by
    have hnat : (5243723353 : ℕ)^4527*100000000000000^3503 ≤ 43419480788957^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243723353 10000000000 43419480788957 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215253541/400000000 : ℝ), (-949373981/5000000000 : ℝ), (5243723353/10000000000 : ℝ)] ![(44897683690659/100000000000000 : ℝ), (2336567100513/20000000000000 : ℝ), (43419480788957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215253541/400000000 : ℝ)|^4527 ≤ (44897683690659/100000000000000 : ℝ)^3503
        have hw : |(215253541/400000000 : ℝ)|=(215253541/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-949373981/5000000000 : ℝ)|^4527 ≤ (2336567100513/20000000000000 : ℝ)^3503
        have hw : |(-949373981/5000000000 : ℝ)|=(949373981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243723353/10000000000 : ℝ)|^4527 ≤ (43419480788957/100000000000000 : ℝ)^3503
        have hw : |(5243723353/10000000000 : ℝ)|=(5243723353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_box_6 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16816689/31250000 : ℝ)*x 0 + (2621860657/5000000000 : ℝ)*x 1 + (-237343507/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16816689/31250000 : ℝ)^4527 ≤ (1403053274053/3125000000000 : ℝ)^3503 := by
    have hnat : (16816689 : ℕ)^4527*3125000000000^3503 ≤ 1403053274053^3503*31250000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16816689 31250000 1403053274053 3125000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621860657/5000000000 : ℝ)^4527 ≤ (43419458970079/100000000000000 : ℝ)^3503 := by
    have hnat : (2621860657 : ℕ)^4527*100000000000000^3503 ≤ 43419458970079^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621860657 5000000000 43419458970079 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237343507/1250000000 : ℝ)^4527 ≤ (1168283625001/10000000000000 : ℝ)^3503 := by
    have hnat : (237343507 : ℕ)^4527*10000000000000^3503 ≤ 1168283625001^3503*1250000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237343507 1250000000 1168283625001 10000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16816689/31250000 : ℝ), (2621860657/5000000000 : ℝ), (-237343507/1250000000 : ℝ)] ![(1403053274053/3125000000000 : ℝ), (43419458970079/100000000000000 : ℝ), (1168283625001/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16816689/31250000 : ℝ)|^4527 ≤ (1403053274053/3125000000000 : ℝ)^3503
        have hw : |(16816689/31250000 : ℝ)|=(16816689/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621860657/5000000000 : ℝ)|^4527 ≤ (43419458970079/100000000000000 : ℝ)^3503
        have hw : |(2621860657/5000000000 : ℝ)|=(2621860657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-237343507/1250000000 : ℝ)|^4527 ≤ (1168283625001/10000000000000 : ℝ)^3503
        have hw : |(-237343507/1250000000 : ℝ)|=(237343507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_box_7 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (63484679/156250000 : ℝ)*x 0 + (547235593/1250000000 : ℝ)*x 1 + (4377884937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63484679/156250000 : ℝ)^4527 ≤ (7806336754721/25000000000000 : ℝ)^3503 := by
    have hnat : (63484679 : ℕ)^4527*25000000000000^3503 ≤ 7806336754721^3503*156250000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63484679 156250000 7806336754721 25000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (547235593/1250000000 : ℝ)^4527 ≤ (6877465100233/20000000000000 : ℝ)^3503 := by
    have hnat : (547235593 : ℕ)^4527*20000000000000^3503 ≤ 6877465100233^3503*1250000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547235593 1250000000 6877465100233 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4377884937/10000000000 : ℝ)^4527 ≤ (537301991567/1562500000000 : ℝ)^3503 := by
    have hnat : (4377884937 : ℕ)^4527*1562500000000^3503 ≤ 537301991567^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377884937 10000000000 537301991567 1562500000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(63484679/156250000 : ℝ), (547235593/1250000000 : ℝ), (4377884937/10000000000 : ℝ)] ![(7806336754721/25000000000000 : ℝ), (6877465100233/20000000000000 : ℝ), (537301991567/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(63484679/156250000 : ℝ)|^4527 ≤ (7806336754721/25000000000000 : ℝ)^3503
        have hw : |(63484679/156250000 : ℝ)|=(63484679/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(547235593/1250000000 : ℝ)|^4527 ≤ (6877465100233/20000000000000 : ℝ)^3503
        have hw : |(547235593/1250000000 : ℝ)|=(547235593/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4377884937/10000000000 : ℝ)|^4527 ≤ (537301991567/1562500000000 : ℝ)^3503
        have hw : |(4377884937/10000000000 : ℝ)|=(4377884937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_box_8 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-49772343/250000000 : ℝ)*x 0 + (2566224209/5000000000 : ℝ)*x 1 + (2711475493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (49772343/250000000 : ℝ)^4527 ≤ (1242067511401/10000000000000 : ℝ)^3503 := by
    have hnat : (49772343 : ℕ)^4527*10000000000000^3503 ≤ 1242067511401^3503*250000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49772343 250000000 1242067511401 10000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2566224209/5000000000 : ℝ)^4527 ≤ (21116232317681/50000000000000 : ℝ)^3503 := by
    have hnat : (2566224209 : ℕ)^4527*50000000000000^3503 ≤ 21116232317681^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566224209 5000000000 21116232317681 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711475493/5000000000 : ℝ)^4527 ≤ (22673430112901/50000000000000 : ℝ)^3503 := by
    have hnat : (2711475493 : ℕ)^4527*50000000000000^3503 ≤ 22673430112901^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711475493 5000000000 22673430112901 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-49772343/250000000 : ℝ), (2566224209/5000000000 : ℝ), (2711475493/5000000000 : ℝ)] ![(1242067511401/10000000000000 : ℝ), (21116232317681/50000000000000 : ℝ), (22673430112901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-49772343/250000000 : ℝ)|^4527 ≤ (1242067511401/10000000000000 : ℝ)^3503
        have hw : |(-49772343/250000000 : ℝ)|=(49772343/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2566224209/5000000000 : ℝ)|^4527 ≤ (21116232317681/50000000000000 : ℝ)^3503
        have hw : |(2566224209/5000000000 : ℝ)|=(2566224209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711475493/5000000000 : ℝ)|^4527 ≤ (22673430112901/50000000000000 : ℝ)^3503
        have hw : |(2711475493/5000000000 : ℝ)|=(2711475493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_box_9 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314145009/2500000000 : ℝ)*x 0 + (-1824522663/10000000000 : ℝ)*x 1 + (338934433/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314145009/2500000000 : ℝ)^4527 ≤ (21778553263899/50000000000000 : ℝ)^3503 := by
    have hnat : (1314145009 : ℕ)^4527*50000000000000^3503 ≤ 21778553263899^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314145009 2500000000 21778553263899 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1824522663/10000000000 : ℝ)^4527 ≤ (11096033861557/100000000000000 : ℝ)^3503 := by
    have hnat : (1824522663 : ℕ)^4527*100000000000000^3503 ≤ 11096033861557^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824522663 10000000000 11096033861557 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338934433/625000000 : ℝ)^4527 ≤ (45346859599029/100000000000000 : ℝ)^3503 := by
    have hnat : (338934433 : ℕ)^4527*100000000000000^3503 ≤ 45346859599029^3503*625000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338934433 625000000 45346859599029 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314145009/2500000000 : ℝ), (-1824522663/10000000000 : ℝ), (338934433/625000000 : ℝ)] ![(21778553263899/50000000000000 : ℝ), (11096033861557/100000000000000 : ℝ), (45346859599029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314145009/2500000000 : ℝ)|^4527 ≤ (21778553263899/50000000000000 : ℝ)^3503
        have hw : |(1314145009/2500000000 : ℝ)|=(1314145009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1824522663/10000000000 : ℝ)|^4527 ≤ (11096033861557/100000000000000 : ℝ)^3503
        have hw : |(-1824522663/10000000000 : ℝ)|=(1824522663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338934433/625000000 : ℝ)|^4527 ≤ (45346859599029/100000000000000 : ℝ)^3503
        have hw : |(338934433/625000000 : ℝ)|=(338934433/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_box_10 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210263219/400000000 : ℝ)*x 0 + (2711475083/5000000000 : ℝ)*x 1 + (-228065389/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210263219/400000000 : ℝ)^4527 ≤ (21778555614401/50000000000000 : ℝ)^3503 := by
    have hnat : (210263219 : ℕ)^4527*50000000000000^3503 ≤ 21778555614401^3503*400000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210263219 400000000 21778555614401 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711475083/5000000000 : ℝ)^4527 ≤ (5668356420567/12500000000000 : ℝ)^3503 := by
    have hnat : (2711475083 : ℕ)^4527*12500000000000^3503 ≤ 5668356420567^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711475083 5000000000 5668356420567 12500000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228065389/1250000000 : ℝ)^4527 ≤ (11096037390423/100000000000000 : ℝ)^3503 := by
    have hnat : (228065389 : ℕ)^4527*100000000000000^3503 ≤ 11096037390423^3503*1250000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228065389 1250000000 11096037390423 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210263219/400000000 : ℝ), (2711475083/5000000000 : ℝ), (-228065389/1250000000 : ℝ)] ![(21778555614401/50000000000000 : ℝ), (5668356420567/12500000000000 : ℝ), (11096037390423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210263219/400000000 : ℝ)|^4527 ≤ (21778555614401/50000000000000 : ℝ)^3503
        have hw : |(210263219/400000000 : ℝ)|=(210263219/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711475083/5000000000 : ℝ)|^4527 ≤ (5668356420567/12500000000000 : ℝ)^3503
        have hw : |(2711475083/5000000000 : ℝ)|=(2711475083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-228065389/1250000000 : ℝ)|^4527 ≤ (11096037390423/100000000000000 : ℝ)^3503
        have hw : |(-228065389/1250000000 : ℝ)|=(228065389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_box_11 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4522717399/10000000000 : ℝ)*x 0 + (2073789341/5000000000 : ℝ)*x 1 + (1036894841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4522717399/10000000000 : ℝ)^4527 ≤ (17932280552453/50000000000000 : ℝ)^3503 := by
    have hnat : (4522717399 : ℕ)^4527*50000000000000^3503 ≤ 17932280552453^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522717399 10000000000 17932280552453 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2073789341/5000000000 : ℝ)^4527 ≤ (6413543207117/20000000000000 : ℝ)^3503 := by
    have hnat : (2073789341 : ℕ)^4527*20000000000000^3503 ≤ 6413543207117^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073789341 5000000000 6413543207117 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036894841/2500000000 : ℝ)^4527 ≤ (32067722849993/100000000000000 : ℝ)^3503 := by
    have hnat : (1036894841 : ℕ)^4527*100000000000000^3503 ≤ 32067722849993^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036894841 2500000000 32067722849993 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4522717399/10000000000 : ℝ), (2073789341/5000000000 : ℝ), (1036894841/2500000000 : ℝ)] ![(17932280552453/50000000000000 : ℝ), (6413543207117/20000000000000 : ℝ), (32067722849993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4522717399/10000000000 : ℝ)|^4527 ≤ (17932280552453/50000000000000 : ℝ)^3503
        have hw : |(4522717399/10000000000 : ℝ)|=(4522717399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2073789341/5000000000 : ℝ)|^4527 ≤ (6413543207117/20000000000000 : ℝ)^3503
        have hw : |(2073789341/5000000000 : ℝ)|=(2073789341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036894841/2500000000 : ℝ)|^4527 ≤ (32067722849993/100000000000000 : ℝ)^3503
        have hw : |(1036894841/2500000000 : ℝ)|=(1036894841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_box_12 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-435416921/2500000000 : ℝ)*x 0 + (2755107059/5000000000 : ℝ)*x 1 + (5228693243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435416921/2500000000 : ℝ)^4527 ≤ (10449213664899/100000000000000 : ℝ)^3503 := by
    have hnat : (435416921 : ℕ)^4527*100000000000000^3503 ≤ 10449213664899^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435416921 2500000000 10449213664899 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2755107059/5000000000 : ℝ)^4527 ≤ (46292071922179/100000000000000 : ℝ)^3503 := by
    have hnat : (2755107059 : ℕ)^4527*100000000000000^3503 ≤ 46292071922179^3503*5000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755107059 5000000000 46292071922179 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228693243/10000000000 : ℝ)^4527 ≤ (5407339299583/12500000000000 : ℝ)^3503 := by
    have hnat : (5228693243 : ℕ)^4527*12500000000000^3503 ≤ 5407339299583^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228693243 10000000000 5407339299583 12500000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-435416921/2500000000 : ℝ), (2755107059/5000000000 : ℝ), (5228693243/10000000000 : ℝ)] ![(10449213664899/100000000000000 : ℝ), (46292071922179/100000000000000 : ℝ), (5407339299583/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-435416921/2500000000 : ℝ)|^4527 ≤ (10449213664899/100000000000000 : ℝ)^3503
        have hw : |(-435416921/2500000000 : ℝ)|=(435416921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2755107059/5000000000 : ℝ)|^4527 ≤ (46292071922179/100000000000000 : ℝ)^3503
        have hw : |(2755107059/5000000000 : ℝ)|=(2755107059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228693243/10000000000 : ℝ)|^4527 ≤ (5407339299583/12500000000000 : ℝ)^3503
        have hw : |(5228693243/10000000000 : ℝ)|=(5228693243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_box_13 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5391800727/10000000000 : ℝ)*x 0 + (-1904771989/10000000000 : ℝ)*x 1 + (1307173479/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5391800727/10000000000 : ℝ)^4527 ≤ (45010520400927/100000000000000 : ℝ)^3503 := by
    have hnat : (5391800727 : ℕ)^4527*100000000000000^3503 ≤ 45010520400927^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391800727 10000000000 45010520400927 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1904771989/10000000000 : ℝ)^4527 ≤ (733172374697/6250000000000 : ℝ)^3503 := by
    have hnat : (1904771989 : ℕ)^4527*6250000000000^3503 ≤ 733172374697^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904771989 10000000000 733172374697 6250000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307173479/2500000000 : ℝ)^4527 ≤ (21629360796123/50000000000000 : ℝ)^3503 := by
    have hnat : (1307173479 : ℕ)^4527*50000000000000^3503 ≤ 21629360796123^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307173479 2500000000 21629360796123 50000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5391800727/10000000000 : ℝ), (-1904771989/10000000000 : ℝ), (1307173479/2500000000 : ℝ)] ![(45010520400927/100000000000000 : ℝ), (733172374697/6250000000000 : ℝ), (21629360796123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5391800727/10000000000 : ℝ)|^4527 ≤ (45010520400927/100000000000000 : ℝ)^3503
        have hw : |(5391800727/10000000000 : ℝ)|=(5391800727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1904771989/10000000000 : ℝ)|^4527 ≤ (733172374697/6250000000000 : ℝ)^3503
        have hw : |(-1904771989/10000000000 : ℝ)|=(1904771989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307173479/2500000000 : ℝ)|^4527 ≤ (21629360796123/50000000000000 : ℝ)^3503
        have hw : |(1307173479/2500000000 : ℝ)|=(1307173479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_box_14 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1347950107/2500000000 : ℝ)*x 0 + (5228693531/10000000000 : ℝ)*x 1 + (-1904772911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347950107/2500000000 : ℝ)^4527 ≤ (45010517175243/100000000000000 : ℝ)^3503 := by
    have hnat : (1347950107 : ℕ)^4527*100000000000000^3503 ≤ 45010517175243^3503*2500000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347950107 2500000000 45010517175243 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228693531/10000000000 : ℝ)^4527 ≤ (43258717475903/100000000000000 : ℝ)^3503 := by
    have hnat : (5228693531 : ℕ)^4527*100000000000000^3503 ≤ 43258717475903^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228693531 10000000000 43258717475903 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1904772911/10000000000 : ℝ)^4527 ≤ (2346153066653/20000000000000 : ℝ)^3503 := by
    have hnat : (1904772911 : ℕ)^4527*20000000000000^3503 ≤ 2346153066653^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904772911 10000000000 2346153066653 20000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1347950107/2500000000 : ℝ), (5228693531/10000000000 : ℝ), (-1904772911/10000000000 : ℝ)] ![(45010517175243/100000000000000 : ℝ), (43258717475903/100000000000000 : ℝ), (2346153066653/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1347950107/2500000000 : ℝ)|^4527 ≤ (45010517175243/100000000000000 : ℝ)^3503
        have hw : |(1347950107/2500000000 : ℝ)|=(1347950107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228693531/10000000000 : ℝ)|^4527 ≤ (43258717475903/100000000000000 : ℝ)^3503
        have hw : |(5228693531/10000000000 : ℝ)|=(5228693531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1904772911/10000000000 : ℝ)|^4527 ≤ (2346153066653/20000000000000 : ℝ)^3503
        have hw : |(-1904772911/10000000000 : ℝ)|=(1904772911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1515_box_15 (p : ℝ) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4023513863/10000000000 : ℝ)*x 0 + (439717243/1000000000 : ℝ)*x 1 + (274823147/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4023513863/10000000000 : ℝ)^4527 ≤ (30833543570201/100000000000000 : ℝ)^3503 := by
    have hnat : (4023513863 : ℕ)^4527*100000000000000^3503 ≤ 30833543570201^3503*10000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023513863 10000000000 30833543570201 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (439717243/1000000000 : ℝ)^4527 ≤ (34583238765063/100000000000000 : ℝ)^3503 := by
    have hnat : (439717243 : ℕ)^4527*100000000000000^3503 ≤ 34583238765063^3503*1000000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439717243 1000000000 34583238765063 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274823147/625000000 : ℝ)^4527 ≤ (34583217644377/100000000000000 : ℝ)^3503 := by
    have hnat : (274823147 : ℕ)^4527*100000000000000^3503 ≤ 34583217644377^3503*625000000^4527 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274823147 625000000 34583217644377 100000000000000 4527 3503 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4527/1024 : ℝ)) 4527 3503 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4023513863/10000000000 : ℝ), (439717243/1000000000 : ℝ), (274823147/625000000 : ℝ)] ![(30833543570201/100000000000000 : ℝ), (34583238765063/100000000000000 : ℝ), (34583217644377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4023513863/10000000000 : ℝ)|^4527 ≤ (30833543570201/100000000000000 : ℝ)^3503
        have hw : |(4023513863/10000000000 : ℝ)|=(4023513863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(439717243/1000000000 : ℝ)|^4527 ≤ (34583238765063/100000000000000 : ℝ)^3503
        have hw : |(439717243/1000000000 : ℝ)|=(439717243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(274823147/625000000 : ℝ)|^4527 ≤ (34583217644377/100000000000000 : ℝ)^3503
        have hw : |(274823147/625000000 : ℝ)|=(274823147/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1515_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (683/6250 : ℝ)*pair X i i ≤ pair X i h) :
    -(63743/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29321/50000 : ℝ) ∧ (2511/3125 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (86021/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (683/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (683/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (683/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (683/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (683/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (683/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (683/6250 : ℝ) ^ (4525/1024 : ℝ) ≤ (2820550481782901/50000000000000000000 : ℝ) := by
    have hpowers : (683/6250 : ℝ)^4525 ≤ (2820550481782901/50000000000000000000 : ℝ)^1024 := by
      have hnat : (683 : ℕ)^4525*50000000000000000000^1024 ≤ 2820550481782901^1024*6250^4525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        683 6250 2820550481782901 50000000000000000000 4525 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (683/6250 : ℝ)) (X := (2820550481782901/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7741/50000 : ℝ) ^ (4525/1024 : ℝ) ≤ (26296024654815199/100000000000000000000 : ℝ) := by
    have hpowers : (7741/50000 : ℝ)^4525 ≤ (26296024654815199/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7741 : ℕ)^4525*100000000000000000000^1024 ≤ 26296024654815199^1024*50000^4525 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7741 50000 26296024654815199 100000000000000000000 4525 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7741/50000 : ℝ)) (X := (26296024654815199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002820550481782901/25000000000000000000 : ℝ) ≤ (10000255303217107/10000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (25002820550481782901/25000000000000000000 : ℝ)^1024 ≤ (10000255303217107/10000000000000000 : ℝ)^4525 := by
      have hnat : (25002820550481782901 : ℕ)^1024*10000000000000000^4525 ≤ 10000255303217107^4525*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002820550481782901 25000000000000000000 10000255303217107 10000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000255303217107/10000000000000000 : ℝ)) (X := (25002820550481782901/25000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100031937125618381001/100000000000000000000 : ℝ) ≤ (10000722642583331/10000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (100031937125618381001/100000000000000000000 : ℝ)^1024 ≤ (10000722642583331/10000000000000000 : ℝ)^4525 := by
      have hnat : (100031937125618381001 : ℕ)^1024*10000000000000000^4525 ≤ 10000722642583331^4525*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100031937125618381001 100000000000000000000 10000722642583331 10000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000722642583331/10000000000000000 : ℝ)) (X := (100031937125618381001/100000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026296024654815199/50000000000000000000 : ℝ) ≤ (2000237996389911/2000000000000000 : ℝ) ^ (4525/1024 : ℝ) := by
    have hpowers : (50026296024654815199/50000000000000000000 : ℝ)^1024 ≤ (2000237996389911/2000000000000000 : ℝ)^4525 := by
      have hnat : (50026296024654815199 : ℕ)^1024*2000000000000000^4525 ≤ 2000237996389911^4525*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026296024654815199 50000000000000000000 2000237996389911 2000000000000000 1024 4525 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000237996389911/2000000000000000 : ℝ)) (X := (50026296024654815199/50000000000000000000 : ℝ)) (by norm_num) 4525 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2820550481782901/50000000000000000000 : ℝ) ≤ ((22765474240831256767/22770000000000000000 : ℝ)+2*(29208710389/28462500000000 : ℝ)*(683/6250 : ℝ))^(4525/1024 : ℝ) := by
    rw [show (22765474240831256767/22770000000000000000 : ℝ)+2*(29208710389/28462500000000 : ℝ)*(683/6250 : ℝ)=(10000255303217107/10000000000000000 : ℝ) by norm_num, show 1+2*(2820550481782901/50000000000000000000 : ℝ)=(25002820550481782901/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26296024654815199/100000000000000000000 : ℝ)+(2820550481782901/50000000000000000000 : ℝ) ≤ ((22765474240831256767/22770000000000000000 : ℝ)+(29208710389/28462500000000 : ℝ)*((7741/50000 : ℝ)+(683/6250 : ℝ)))^(4525/1024 : ℝ) := by
    rw [show (22765474240831256767/22770000000000000000 : ℝ)+(29208710389/28462500000000 : ℝ)*((7741/50000 : ℝ)+(683/6250 : ℝ))=(10000722642583331/10000000000000000 : ℝ) by norm_num, show 1+(26296024654815199/100000000000000000000 : ℝ)+(2820550481782901/50000000000000000000 : ℝ)=(100031937125618381001/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26296024654815199/100000000000000000000 : ℝ) ≤ ((22765474240831256767/22770000000000000000 : ℝ)+2*(29208710389/28462500000000 : ℝ)*(7741/50000 : ℝ))^(4525/1024 : ℝ) := by
    rw [show (22765474240831256767/22770000000000000000 : ℝ)+2*(29208710389/28462500000000 : ℝ)*(7741/50000 : ℝ)=(2000237996389911/2000000000000000 : ℝ) by norm_num, show 1+2*(26296024654815199/100000000000000000000 : ℝ)=(50026296024654815199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22765474240831256767/22770000000000000000 : ℝ)*(X 1 0+X 2 0)+(29208710389/28462500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (683/6250 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (22765474240831256767/22770000000000000000 : ℝ)) (alpha := (29208710389/28462500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22765474240831256767/22770000000000000000 : ℝ)*(X 0 1+X 2 1)+(29208710389/28462500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (683/6250 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (22765474240831256767/22770000000000000000 : ℝ)) (alpha := (29208710389/28462500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22765474240831256767/22770000000000000000 : ℝ)*(X 0 2+X 1 2)+(29208710389/28462500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4525/1024 : ℝ)) (lo := (683/6250 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (22765474240831256767/22770000000000000000 : ℝ)) (alpha := (29208710389/28462500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1650506627/10000000000 : ℝ)*X 0 0+(5402508117/10000000000 : ℝ)*X 0 1+(5402506047/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1317703897/2500000000 : ℝ)*X 1 0+(-91660371/500000000 : ℝ)*X 1 1+(8441417/15625000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270816691/10000000000 : ℝ)*X 2 0+(2701253509/5000000000 : ℝ)*X 2 1+(-1833205729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((178852079/400000000 : ℝ)*X 0 0+(65216821/156250000 : ℝ)*X 0 1+(417387841/1000000000 : ℝ)*X 0 2+(178852079/400000000 : ℝ)*X 1 0+(65216821/156250000 : ℝ)*X 1 1+(417387841/1000000000 : ℝ)*X 1 2+(178852079/400000000 : ℝ)*X 2 0+(65216821/156250000 : ℝ)*X 2 1+(417387841/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-104105973/500000000 : ℝ)*X 0 0+(327732737/625000000 : ℝ)*X 0 1+(2621860799/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((215253541/400000000 : ℝ)*X 1 0+(-949373981/5000000000 : ℝ)*X 1 1+(5243723353/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((16816689/31250000 : ℝ)*X 2 0+(2621860657/5000000000 : ℝ)*X 2 1+(-237343507/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((63484679/156250000 : ℝ)*X 0 0+(547235593/1250000000 : ℝ)*X 0 1+(4377884937/10000000000 : ℝ)*X 0 2+(63484679/156250000 : ℝ)*X 1 0+(547235593/1250000000 : ℝ)*X 1 1+(4377884937/10000000000 : ℝ)*X 1 2+(63484679/156250000 : ℝ)*X 2 0+(547235593/1250000000 : ℝ)*X 2 1+(4377884937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-49772343/250000000 : ℝ)*X 0 0+(2566224209/5000000000 : ℝ)*X 0 1+(2711475493/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1314145009/2500000000 : ℝ)*X 1 0+(-1824522663/10000000000 : ℝ)*X 1 1+(338934433/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((210263219/400000000 : ℝ)*X 2 0+(2711475083/5000000000 : ℝ)*X 2 1+(-228065389/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4522717399/10000000000 : ℝ)*X 0 0+(2073789341/5000000000 : ℝ)*X 0 1+(1036894841/2500000000 : ℝ)*X 0 2+(4522717399/10000000000 : ℝ)*X 1 0+(2073789341/5000000000 : ℝ)*X 1 1+(1036894841/2500000000 : ℝ)*X 1 2+(4522717399/10000000000 : ℝ)*X 2 0+(2073789341/5000000000 : ℝ)*X 2 1+(1036894841/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-435416921/2500000000 : ℝ)*X 0 0+(2755107059/5000000000 : ℝ)*X 0 1+(5228693243/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5391800727/10000000000 : ℝ)*X 1 0+(-1904771989/10000000000 : ℝ)*X 1 1+(1307173479/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1347950107/2500000000 : ℝ)*X 2 0+(5228693531/10000000000 : ℝ)*X 2 1+(-1904772911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4023513863/10000000000 : ℝ)*X 0 0+(439717243/1000000000 : ℝ)*X 0 1+(274823147/625000000 : ℝ)*X 0 2+(4023513863/10000000000 : ℝ)*X 1 0+(439717243/1000000000 : ℝ)*X 1 1+(274823147/625000000 : ℝ)*X 1 2+(4023513863/10000000000 : ℝ)*X 2 0+(439717243/1000000000 : ℝ)*X 2 1+(274823147/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1515_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63743/100000 : ℝ) ≤ (-120948012026128659745524031560311/189750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44519/200000000000 : ℝ)*(upper1) + (91051033/50000000000000 : ℝ)*(upper4) + (272448619/100000000000000 : ℝ)*(upper5) + (1113946042888967/50000000000000 : ℝ)*(major0) + (1113946042888967/50000000000000 : ℝ)*(major1) + (1113946042888967/50000000000000 : ℝ)*(major2) + (1510974997/50000000000000 : ℝ)*(sp1) + (41652344109/100000000000000 : ℝ)*(sp2) + (3516920071/50000000000000 : ℝ)*(sp3) + (77884059633851/2500000000000 : ℝ)*(sp4) + (1557696894147909/50000000000000 : ℝ)*(sp5) + (1557677578950851/50000000000000 : ℝ)*(sp6) + (1361627233403351/100000000000000 : ℝ)*(sp7) + (34424891771/100000000000000 : ℝ)*(sp8) + (1361634267243493/100000000000000 : ℝ)*(f.failure) + (778849202561453/25000000000000 : ℝ)*(f.sum) + (31712233487501/5692500000000000000000000000 : ℝ)*base66 + (177039436094054233/34500000000000000000000000000000 : ℝ)*base67 + (161279841869445767/34500000000000000000000000000000 : ℝ)*base70 + (196825957596945767/34500000000000000000000000000000 : ℝ)*base72 + (6913464829037/2846250000000000000000000000 : ℝ)*base73 + (216738741875445767/34500000000000000000000000000000 : ℝ)*base76 + (51743982413445767/34500000000000000000000000000000 : ℝ)*base78 + (55038968690054233/34500000000000000000000000000000 : ℝ)*base79 + (44994460330991/5692500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (69053647/10000000000000000000000 : ℝ)*base89 + (69053647/10000000000000000000000 : ℝ)*base91 + (69053647/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29321/50000 : ℝ) ≤ (111277470850661389586607863/189750000000000000000000000 : ℝ) := by norm_num
    linear_combination (47360227/50000000000000 : ℝ)*(upper0) + (251252089/50000000000000 : ℝ)*(lower1) + (344215547/50000000000000 : ℝ)*(upper4) + (460866578022017/20000000000000 : ℝ)*(major0) + (460866578022017/20000000000000 : ℝ)*(major1) + (460866578022017/20000000000000 : ℝ)*(major2) + (636149470589069/20000000000000 : ℝ)*(sp0) + (3180631158724179/100000000000000 : ℝ)*(sp1) + (318075128798119/10000000000000 : ℝ)*(sp2) + (70417070524619/5000000000000 : ℝ)*(sp3) + (13352276813/100000000000000 : ℝ)*(sp6) + (11644998869/100000000000000 : ℝ)*(sp7) + (8643656329/50000000000000 : ℝ)*(sp8) + (1042824483/781250000000 : ℝ)*(sp9) + (1408353055491249/100000000000000 : ℝ)*(f.failure) + (3180764640258003/100000000000000 : ℝ)*(f.sum) + (1529882263949/2277000000000000000000000000 : ℝ)*base66 + (1207365253201183/13800000000000000000000000000000 : ℝ)*base67 + (225135342598817/13800000000000000000000000000000 : ℝ)*base70 + (78162727753798817/13800000000000000000000000000000 : ℝ)*base72 + (17595360314569/569250000000000000000000000 : ℝ)*base73 + (38695581649201183/13800000000000000000000000000000 : ℝ)*base75 + (66370525826998817/13800000000000000000000000000000 : ℝ)*base78 + (283558907809801183/13800000000000000000000000000000 : ℝ)*base79 + (7037666489749/2277000000000000000000000000 : ℝ)*base81 + (4814771/10000000000000000000000 : ℝ)*base89 + (4814771/10000000000000000000000 : ℝ)*base91 + (4814771/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (2511/3125 : ℝ) ≤ (101647818407911986363712277793689/126500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1231749/800000000000 : ℝ)*(upper0) + (2854341/50000000000000 : ℝ)*(upper2) + (54366297/50000000000000 : ℝ)*(lower5) + (2497876188302901/100000000000000 : ℝ)*(major0) + (2497876188302901/100000000000000 : ℝ)*(major1) + (2497876188302901/100000000000000 : ℝ)*(major2) + (55082787439/50000000000000 : ℝ)*(sp1) + (28172782107/100000000000000 : ℝ)*(sp3) + (2232740223/100000000000000 : ℝ)*(sp4) + (1721156415359639/50000000000000 : ℝ)*(sp8) + (430276932461281/12500000000000 : ℝ)*(sp9) + (3442325625265127/100000000000000 : ℝ)*(sp10) + (381653477419093/25000000000000 : ℝ)*(sp11) + (5280902813/50000000000000 : ℝ)*(sp12) + (1526642082458479/100000000000000 : ℝ)*(f.failure) + (3442325625265127/100000000000000 : ℝ)*(f.sum) + (10022621811751/3795000000000000000000000000 : ℝ)*base66 + (151086221188957767/23000000000000000000000000000000 : ℝ)*base68 + (70791180122957767/23000000000000000000000000000000 : ℝ)*base70 + (22291703876042233/23000000000000000000000000000000 : ℝ)*base71 + (194918137201/14824218750000000000000000 : ℝ)*base74 + (62586252185042233/23000000000000000000000000000000 : ℝ)*base75 + (91841383182957767/23000000000000000000000000000000 : ℝ)*base78 + (229928965250957767/23000000000000000000000000000000 : ℝ)*base80 + (54087687187/1897500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (43872941/10000000000000000000000 : ℝ)*base89 + (43872941/10000000000000000000000 : ℝ)*base91 + (43872941/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-86021/100000 : ℝ) ≤ (-81610128834970748532443210782031/94875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (334534411/100000000000000 : ℝ)*(lower0) + (229908531/100000000000000 : ℝ)*(upper3) + (127035381/50000000000000 : ℝ)*(lower4) + (1268515333878193/50000000000000 : ℝ)*(major0) + (1268515333878193/50000000000000 : ℝ)*(major1) + (1268515333878193/50000000000000 : ℝ)*(major2) + (28405071699/100000000000000 : ℝ)*(sp0) + (12896412691/4000000000000 : ℝ)*(sp5) + (463839122281/100000000000000 : ℝ)*(sp6) + (175324747729/100000000000000 : ℝ)*(sp7) + (3552133428571569/100000000000000 : ℝ)*(sp12) + (443979927915749/12500000000000 : ℝ)*(sp13) + (3551697994520987/100000000000000 : ℝ)*(sp14) + (62015881499767/4000000000000 : ℝ)*(sp15) + (96910772640119/6250000000000 : ℝ)*(f.failure) + (888040458410817/25000000000000 : ℝ)*(f.sum) + (6713191362733/2846250000000000000000000000 : ℝ)*base65 + (108875925822214607/34500000000000000000000000000000 : ℝ)*base67 + (14213044526785393/34500000000000000000000000000000 : ℝ)*base70 + (175214407555714607/34500000000000000000000000000000 : ℝ)*base71 + (2057590652537/2846250000000000000000000000 : ℝ)*base74 + (309272216341714607/34500000000000000000000000000000 : ℝ)*base75 + (39881196939214607/34500000000000000000000000000000 : ℝ)*base77 + (170598481815214607/34500000000000000000000000000000 : ℝ)*base79 + (1962750164267/2846250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (7281499/625000000000000000000 : ℝ)*base90 + (7281499/625000000000000000000 : ℝ)*base92 + (7281499/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1515_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (683/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63743/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29321/50000 : ℝ) else (2511/3125 : ℝ) ≤ X j i ∧ X j i ≤ (86021/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1515_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1515_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10927/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63743/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29321/50000 : ℝ) else (2511/3125 : ℝ) ≤ X j i ∧ X j i ≤ (86021/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1515_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1515_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1515_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4525/1024 : ℝ) ≤ p) (hpb : p ≤ (4527/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (163618979/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10927/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63743/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29321/50000 : ℝ) else (2511/3125 : ℝ) ≤ X j i ∧ X j i ≤ (86021/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1515_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

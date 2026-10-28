-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1189_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:53:02.405238+00:00
-- url     : https://prove2.me/submissions/21fc0379-aafc-4e26-991a-babf8f57f713

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
theorem support_rectangle_w1189_box_0 (p : ℝ) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2019248273/10000000000 : ℝ)*x 0 + (2687815483/5000000000 : ℝ)*x 1 + (5375629303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2019248273/10000000000 : ℝ)^4191 ≤ (12037426960819/100000000000000 : ℝ)^3167 := by
    have hnat : (2019248273 : ℕ)^4191*100000000000000^3167 ≤ 12037426960819^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019248273 10000000000 12037426960819 100000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687815483/5000000000 : ℝ)^4191 ≤ (43981295514127/100000000000000 : ℝ)^3167 := by
    have hnat : (2687815483 : ℕ)^4191*100000000000000^3167 ≤ 43981295514127^3167*5000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687815483 5000000000 43981295514127 100000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375629303/10000000000 : ℝ)^4191 ≤ (1759251100353/4000000000000 : ℝ)^3167 := by
    have hnat : (5375629303 : ℕ)^4191*4000000000000^3167 ≤ 1759251100353^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375629303 10000000000 1759251100353 4000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4191/1024 : ℝ)) 4191 3167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2019248273/10000000000 : ℝ), (2687815483/5000000000 : ℝ), (5375629303/10000000000 : ℝ)] ![(12037426960819/100000000000000 : ℝ), (43981295514127/100000000000000 : ℝ), (1759251100353/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2019248273/10000000000 : ℝ)|^4191 ≤ (12037426960819/100000000000000 : ℝ)^3167
        have hw : |(-2019248273/10000000000 : ℝ)|=(2019248273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687815483/5000000000 : ℝ)|^4191 ≤ (43981295514127/100000000000000 : ℝ)^3167
        have hw : |(2687815483/5000000000 : ℝ)|=(2687815483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375629303/10000000000 : ℝ)|^4191 ≤ (1759251100353/4000000000000 : ℝ)^3167
        have hw : |(5375629303/10000000000 : ℝ)|=(5375629303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1189_box_1 (p : ℝ) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296394619/10000000000 : ℝ)*x 0 + (-2126818889/10000000000 : ℝ)*x 1 + (1343907557/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296394619/10000000000 : ℝ)^4191 ≤ (8625090936991/20000000000000 : ℝ)^3167 := by
    have hnat : (5296394619 : ℕ)^4191*20000000000000^3167 ≤ 8625090936991^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296394619 10000000000 8625090936991 20000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126818889/10000000000 : ℝ)^4191 ≤ (6446628888967/50000000000000 : ℝ)^3167 := by
    have hnat : (2126818889 : ℕ)^4191*50000000000000^3167 ≤ 6446628888967^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126818889 10000000000 6446628888967 50000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343907557/2500000000 : ℝ)^4191 ≤ (219906437619/500000000000 : ℝ)^3167 := by
    have hnat : (1343907557 : ℕ)^4191*500000000000^3167 ≤ 219906437619^3167*2500000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343907557 2500000000 219906437619 500000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4191/1024 : ℝ)) 4191 3167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296394619/10000000000 : ℝ), (-2126818889/10000000000 : ℝ), (1343907557/2500000000 : ℝ)] ![(8625090936991/20000000000000 : ℝ), (6446628888967/50000000000000 : ℝ), (219906437619/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296394619/10000000000 : ℝ)|^4191 ≤ (8625090936991/20000000000000 : ℝ)^3167
        have hw : |(5296394619/10000000000 : ℝ)|=(5296394619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2126818889/10000000000 : ℝ)|^4191 ≤ (6446628888967/50000000000000 : ℝ)^3167
        have hw : |(-2126818889/10000000000 : ℝ)|=(2126818889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1343907557/2500000000 : ℝ)|^4191 ≤ (219906437619/500000000000 : ℝ)^3167
        have hw : |(1343907557/2500000000 : ℝ)|=(1343907557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1189_box_2 (p : ℝ) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2648197551/5000000000 : ℝ)*x 0 + (2687814821/5000000000 : ℝ)*x 1 + (-212681903/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648197551/5000000000 : ℝ)^4191 ≤ (10781364972337/25000000000000 : ℝ)^3167 := by
    have hnat : (2648197551 : ℕ)^4191*25000000000000^3167 ≤ 10781364972337^3167*5000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648197551 5000000000 10781364972337 25000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687814821/5000000000 : ℝ)^4191 ≤ (21990640589589/50000000000000 : ℝ)^3167 := by
    have hnat : (2687814821 : ℕ)^4191*50000000000000^3167 ≤ 21990640589589^3167*5000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687814821 5000000000 21990640589589 50000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212681903/1000000000 : ℝ)^4191 ≤ (6446629454543/50000000000000 : ℝ)^3167 := by
    have hnat : (212681903 : ℕ)^4191*50000000000000^3167 ≤ 6446629454543^3167*1000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212681903 1000000000 6446629454543 50000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4191/1024 : ℝ)) 4191 3167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648197551/5000000000 : ℝ), (2687814821/5000000000 : ℝ), (-212681903/1000000000 : ℝ)] ![(10781364972337/25000000000000 : ℝ), (21990640589589/50000000000000 : ℝ), (6446629454543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648197551/5000000000 : ℝ)|^4191 ≤ (10781364972337/25000000000000 : ℝ)^3167
        have hw : |(2648197551/5000000000 : ℝ)|=(2648197551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687814821/5000000000 : ℝ)|^4191 ≤ (21990640589589/50000000000000 : ℝ)^3167
        have hw : |(2687814821/5000000000 : ℝ)|=(2687814821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212681903/1000000000 : ℝ)|^4191 ≤ (6446629454543/50000000000000 : ℝ)^3167
        have hw : |(-212681903/1000000000 : ℝ)|=(212681903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1189_box_3 (p : ℝ) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4465149657/10000000000 : ℝ)*x 0 + (2153322191/5000000000 : ℝ)*x 1 + (4306645927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4465149657/10000000000 : ℝ)^4191 ≤ (1075142391063/3125000000000 : ℝ)^3167 := by
    have hnat : (4465149657 : ℕ)^4191*3125000000000^3167 ≤ 1075142391063^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4465149657 10000000000 1075142391063 3125000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2153322191/5000000000 : ℝ)^4191 ≤ (32797713945881/100000000000000 : ℝ)^3167 := by
    have hnat : (2153322191 : ℕ)^4191*100000000000000^3167 ≤ 32797713945881^3167*5000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153322191 5000000000 32797713945881 100000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4306645927/10000000000 : ℝ)^4191 ≤ (6559545903277/20000000000000 : ℝ)^3167 := by
    have hnat : (4306645927 : ℕ)^4191*20000000000000^3167 ≤ 6559545903277^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306645927 10000000000 6559545903277 20000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4191/1024 : ℝ)) 4191 3167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4465149657/10000000000 : ℝ), (2153322191/5000000000 : ℝ), (4306645927/10000000000 : ℝ)] ![(1075142391063/3125000000000 : ℝ), (32797713945881/100000000000000 : ℝ), (6559545903277/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4465149657/10000000000 : ℝ)|^4191 ≤ (1075142391063/3125000000000 : ℝ)^3167
        have hw : |(4465149657/10000000000 : ℝ)|=(4465149657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2153322191/5000000000 : ℝ)|^4191 ≤ (32797713945881/100000000000000 : ℝ)^3167
        have hw : |(2153322191/5000000000 : ℝ)|=(2153322191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4306645927/10000000000 : ℝ)|^4191 ≤ (6559545903277/20000000000000 : ℝ)^3167
        have hw : |(4306645927/10000000000 : ℝ)|=(4306645927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1189_box_4 (p : ℝ) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-567840477/2500000000 : ℝ)*x 0 + (132042781/250000000 : ℝ)*x 1 + (5281710887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (567840477/2500000000 : ℝ)^4191 ≤ (7032691728977/50000000000000 : ℝ)^3167 := by
    have hnat : (567840477 : ℕ)^4191*50000000000000^3167 ≤ 7032691728977^3167*2500000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567840477 2500000000 7032691728977 50000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132042781/250000000 : ℝ)^4191 ≤ (8593462033303/20000000000000 : ℝ)^3167 := by
    have hnat : (132042781 : ℕ)^4191*20000000000000^3167 ≤ 8593462033303^3167*250000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132042781 250000000 8593462033303 20000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281710887/10000000000 : ℝ)^4191 ≤ (42967306366303/100000000000000 : ℝ)^3167 := by
    have hnat : (5281710887 : ℕ)^4191*100000000000000^3167 ≤ 42967306366303^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281710887 10000000000 42967306366303 100000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4191/1024 : ℝ)) 4191 3167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-567840477/2500000000 : ℝ), (132042781/250000000 : ℝ), (5281710887/10000000000 : ℝ)] ![(7032691728977/50000000000000 : ℝ), (8593462033303/20000000000000 : ℝ), (42967306366303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-567840477/2500000000 : ℝ)|^4191 ≤ (7032691728977/50000000000000 : ℝ)^3167
        have hw : |(-567840477/2500000000 : ℝ)|=(567840477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132042781/250000000 : ℝ)|^4191 ≤ (8593462033303/20000000000000 : ℝ)^3167
        have hw : |(132042781/250000000 : ℝ)|=(132042781/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281710887/10000000000 : ℝ)|^4191 ≤ (42967306366303/100000000000000 : ℝ)^3167
        have hw : |(5281710887/10000000000 : ℝ)|=(5281710887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1189_box_5 (p : ℝ) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (670334871/1250000000 : ℝ)*x 0 + (-2163900333/10000000000 : ℝ)*x 1 + (165053469/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670334871/1250000000 : ℝ)^4191 ≤ (21920559437077/50000000000000 : ℝ)^3167 := by
    have hnat : (670334871 : ℕ)^4191*50000000000000^3167 ≤ 21920559437077^3167*1250000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670334871 1250000000 21920559437077 50000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2163900333/10000000000 : ℝ)^4191 ≤ (1319157343503/10000000000000 : ℝ)^3167 := by
    have hnat : (2163900333 : ℕ)^4191*10000000000000^3167 ≤ 1319157343503^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163900333 10000000000 1319157343503 10000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (165053469/312500000 : ℝ)^4191 ≤ (21483653834463/50000000000000 : ℝ)^3167 := by
    have hnat : (165053469 : ℕ)^4191*50000000000000^3167 ≤ 21483653834463^3167*312500000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165053469 312500000 21483653834463 50000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4191/1024 : ℝ)) 4191 3167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670334871/1250000000 : ℝ), (-2163900333/10000000000 : ℝ), (165053469/312500000 : ℝ)] ![(21920559437077/50000000000000 : ℝ), (1319157343503/10000000000000 : ℝ), (21483653834463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670334871/1250000000 : ℝ)|^4191 ≤ (21920559437077/50000000000000 : ℝ)^3167
        have hw : |(670334871/1250000000 : ℝ)|=(670334871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2163900333/10000000000 : ℝ)|^4191 ≤ (1319157343503/10000000000000 : ℝ)^3167
        have hw : |(-2163900333/10000000000 : ℝ)|=(2163900333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(165053469/312500000 : ℝ)|^4191 ≤ (21483653834463/50000000000000 : ℝ)^3167
        have hw : |(165053469/312500000 : ℝ)|=(165053469/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1189_box_6 (p : ℝ) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5362679007/10000000000 : ℝ)*x 0 + (132042777/250000000 : ℝ)*x 1 + (-432780037/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362679007/10000000000 : ℝ)^4191 ≤ (21920559648039/50000000000000 : ℝ)^3167 := by
    have hnat : (5362679007 : ℕ)^4191*50000000000000^3167 ≤ 21920559648039^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362679007 10000000000 21920559648039 50000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132042777/250000000 : ℝ)^4191 ≤ (1074182711101/2500000000000 : ℝ)^3167 := by
    have hnat : (132042777 : ℕ)^4191*2500000000000^3167 ≤ 1074182711101^3167*250000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132042777 250000000 1074182711101 2500000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (432780037/2000000000 : ℝ)^4191 ≤ (3297893060267/25000000000000 : ℝ)^3167 := by
    have hnat : (432780037 : ℕ)^4191*25000000000000^3167 ≤ 3297893060267^3167*2000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432780037 2000000000 3297893060267 25000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4191/1024 : ℝ)) 4191 3167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362679007/10000000000 : ℝ), (132042777/250000000 : ℝ), (-432780037/2000000000 : ℝ)] ![(21920559648039/50000000000000 : ℝ), (1074182711101/2500000000000 : ℝ), (3297893060267/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362679007/10000000000 : ℝ)|^4191 ≤ (21920559648039/50000000000000 : ℝ)^3167
        have hw : |(5362679007/10000000000 : ℝ)|=(5362679007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(132042777/250000000 : ℝ)|^4191 ≤ (1074182711101/2500000000000 : ℝ)^3167
        have hw : |(132042777/250000000 : ℝ)|=(132042777/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-432780037/2000000000 : ℝ)|^4191 ≤ (3297893060267/25000000000000 : ℝ)^3167
        have hw : |(-432780037/2000000000 : ℝ)|=(432780037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1189_box_7 (p : ℝ) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4250660637/10000000000 : ℝ)*x 0 + (882773839/2000000000 : ℝ)*x 1 + (882773833/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4250660637/10000000000 : ℝ)^4191 ≤ (32234699228877/100000000000000 : ℝ)^3167 := by
    have hnat : (4250660637 : ℕ)^4191*100000000000000^3167 ≤ 32234699228877^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250660637 10000000000 32234699228877 100000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (882773839/2000000000 : ℝ)^4191 ≤ (2117665658487/6250000000000 : ℝ)^3167 := by
    have hnat : (882773839 : ℕ)^4191*6250000000000^3167 ≤ 2117665658487^3167*2000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882773839 2000000000 2117665658487 6250000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (882773833/2000000000 : ℝ)^4191 ≤ (16941325115519/50000000000000 : ℝ)^3167 := by
    have hnat : (882773833 : ℕ)^4191*50000000000000^3167 ≤ 16941325115519^3167*2000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882773833 2000000000 16941325115519 50000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4191/1024 : ℝ)) 4191 3167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4250660637/10000000000 : ℝ), (882773839/2000000000 : ℝ), (882773833/2000000000 : ℝ)] ![(32234699228877/100000000000000 : ℝ), (2117665658487/6250000000000 : ℝ), (16941325115519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4250660637/10000000000 : ℝ)|^4191 ≤ (32234699228877/100000000000000 : ℝ)^3167
        have hw : |(4250660637/10000000000 : ℝ)|=(4250660637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(882773839/2000000000 : ℝ)|^4191 ≤ (2117665658487/6250000000000 : ℝ)^3167
        have hw : |(882773839/2000000000 : ℝ)|=(882773839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(882773833/2000000000 : ℝ)|^4191 ≤ (16941325115519/50000000000000 : ℝ)^3167
        have hw : |(882773833/2000000000 : ℝ)|=(882773833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1189_box_8 (p : ℝ) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2218588641/10000000000 : ℝ)*x 0 + (5217747901/10000000000 : ℝ)*x 1 + (5385241601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2218588641/10000000000 : ℝ)^4191 ≤ (1363455361451/10000000000000 : ℝ)^3167 := by
    have hnat : (2218588641 : ℕ)^4191*10000000000000^3167 ≤ 1363455361451^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218588641 10000000000 1363455361451 10000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217747901/10000000000 : ℝ)^4191 ≤ (165156509537/390625000000 : ℝ)^3167 := by
    have hnat : (5217747901 : ℕ)^4191*390625000000^3167 ≤ 165156509537^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217747901 10000000000 165156509537 390625000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385241601/10000000000 : ℝ)^4191 ≤ (22042689964819/50000000000000 : ℝ)^3167 := by
    have hnat : (5385241601 : ℕ)^4191*50000000000000^3167 ≤ 22042689964819^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385241601 10000000000 22042689964819 50000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4191/1024 : ℝ)) 4191 3167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2218588641/10000000000 : ℝ), (5217747901/10000000000 : ℝ), (5385241601/10000000000 : ℝ)] ![(1363455361451/10000000000000 : ℝ), (165156509537/390625000000 : ℝ), (22042689964819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2218588641/10000000000 : ℝ)|^4191 ≤ (1363455361451/10000000000000 : ℝ)^3167
        have hw : |(-2218588641/10000000000 : ℝ)|=(2218588641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217747901/10000000000 : ℝ)|^4191 ≤ (165156509537/390625000000 : ℝ)^3167
        have hw : |(5217747901/10000000000 : ℝ)|=(5217747901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385241601/10000000000 : ℝ)|^4191 ≤ (22042689964819/50000000000000 : ℝ)^3167
        have hw : |(5385241601/10000000000 : ℝ)|=(5385241601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1189_box_9 (p : ℝ) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330600523/625000000 : ℝ)*x 0 + (-1061477691/5000000000 : ℝ)*x 1 + (5385241653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330600523/625000000 : ℝ)^4191 ≤ (21526173513537/50000000000000 : ℝ)^3167 := by
    have hnat : (330600523 : ℕ)^4191*50000000000000^3167 ≤ 21526173513537^3167*625000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330600523 625000000 21526173513537 50000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061477691/5000000000 : ℝ)^4191 ≤ (12862272468073/100000000000000 : ℝ)^3167 := by
    have hnat : (1061477691 : ℕ)^4191*100000000000000^3167 ≤ 12862272468073^3167*5000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061477691 5000000000 12862272468073 100000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385241653/10000000000 : ℝ)^4191 ≤ (44085380492967/100000000000000 : ℝ)^3167 := by
    have hnat : (5385241653 : ℕ)^4191*100000000000000^3167 ≤ 44085380492967^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385241653 10000000000 44085380492967 100000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4191/1024 : ℝ)) 4191 3167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330600523/625000000 : ℝ), (-1061477691/5000000000 : ℝ), (5385241653/10000000000 : ℝ)] ![(21526173513537/50000000000000 : ℝ), (12862272468073/100000000000000 : ℝ), (44085380492967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330600523/625000000 : ℝ)|^4191 ≤ (21526173513537/50000000000000 : ℝ)^3167
        have hw : |(330600523/625000000 : ℝ)|=(330600523/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1061477691/5000000000 : ℝ)|^4191 ≤ (12862272468073/100000000000000 : ℝ)^3167
        have hw : |(-1061477691/5000000000 : ℝ)|=(1061477691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385241653/10000000000 : ℝ)|^4191 ≤ (44085380492967/100000000000000 : ℝ)^3167
        have hw : |(5385241653/10000000000 : ℝ)|=(5385241653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1189_box_10 (p : ℝ) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289608363/10000000000 : ℝ)*x 0 + (5385241579/10000000000 : ℝ)*x 1 + (-66342359/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289608363/10000000000 : ℝ)^4191 ≤ (43052346973221/100000000000000 : ℝ)^3167 := by
    have hnat : (5289608363 : ℕ)^4191*100000000000000^3167 ≤ 43052346973221^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289608363 10000000000 43052346973221 100000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385241579/10000000000 : ℝ)^4191 ≤ (22042689845653/50000000000000 : ℝ)^3167 := by
    have hnat : (5385241579 : ℕ)^4191*50000000000000^3167 ≤ 22042689845653^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385241579 10000000000 22042689845653 50000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66342359/312500000 : ℝ)^4191 ≤ (12862273317943/100000000000000 : ℝ)^3167 := by
    have hnat : (66342359 : ℕ)^4191*100000000000000^3167 ≤ 12862273317943^3167*312500000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66342359 312500000 12862273317943 100000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4191/1024 : ℝ)) 4191 3167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289608363/10000000000 : ℝ), (5385241579/10000000000 : ℝ), (-66342359/312500000 : ℝ)] ![(43052346973221/100000000000000 : ℝ), (22042689845653/50000000000000 : ℝ), (12862273317943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289608363/10000000000 : ℝ)|^4191 ≤ (43052346973221/100000000000000 : ℝ)^3167
        have hw : |(5289608363/10000000000 : ℝ)|=(5289608363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385241579/10000000000 : ℝ)|^4191 ≤ (22042689845653/50000000000000 : ℝ)^3167
        have hw : |(5385241579/10000000000 : ℝ)|=(5385241579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-66342359/312500000 : ℝ)|^4191 ≤ (12862273317943/100000000000000 : ℝ)^3167
        have hw : |(-66342359/312500000 : ℝ)|=(66342359/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1189_box_11 (p : ℝ) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1121706937/2500000000 : ℝ)*x 0 + (4295665663/10000000000 : ℝ)*x 1 + (4295665477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1121706937/2500000000 : ℝ)^4191 ≤ (1082055302047/3125000000000 : ℝ)^3167 := by
    have hnat : (1121706937 : ℕ)^4191*3125000000000^3167 ≤ 1082055302047^3167*2500000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121706937 2500000000 1082055302047 3125000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4295665663/10000000000 : ℝ)^4191 ≤ (6537423218227/20000000000000 : ℝ)^3167 := by
    have hnat : (4295665663 : ℕ)^4191*20000000000000^3167 ≤ 6537423218227^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4295665663 10000000000 6537423218227 20000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4295665477/10000000000 : ℝ)^4191 ≤ (1307484568727/4000000000000 : ℝ)^3167 := by
    have hnat : (4295665477 : ℕ)^4191*4000000000000^3167 ≤ 1307484568727^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4295665477 10000000000 1307484568727 4000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4191/1024 : ℝ)) 4191 3167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1121706937/2500000000 : ℝ), (4295665663/10000000000 : ℝ), (4295665477/10000000000 : ℝ)] ![(1082055302047/3125000000000 : ℝ), (6537423218227/20000000000000 : ℝ), (1307484568727/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1121706937/2500000000 : ℝ)|^4191 ≤ (1082055302047/3125000000000 : ℝ)^3167
        have hw : |(1121706937/2500000000 : ℝ)|=(1121706937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4295665663/10000000000 : ℝ)|^4191 ≤ (6537423218227/20000000000000 : ℝ)^3167
        have hw : |(4295665663/10000000000 : ℝ)|=(4295665663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4295665477/10000000000 : ℝ)|^4191 ≤ (1307484568727/4000000000000 : ℝ)^3167
        have hw : |(4295665477/10000000000 : ℝ)|=(4295665477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1189_box_12 (p : ℝ) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-103615621/500000000 : ℝ)*x 0 + (543834861/1000000000 : ℝ)*x 1 + (5273652283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103615621/500000000 : ℝ)^4191 ≤ (12457809955579/100000000000000 : ℝ)^3167 := by
    have hnat : (103615621 : ℕ)^4191*100000000000000^3167 ≤ 12457809955579^3167*500000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103615621 500000000 12457809955579 100000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543834861/1000000000 : ℝ)^4191 ≤ (5582702117151/12500000000000 : ℝ)^3167 := by
    have hnat : (543834861 : ℕ)^4191*12500000000000^3167 ≤ 5582702117151^3167*1000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543834861 1000000000 5582702117151 12500000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273652283/10000000000 : ℝ)^4191 ≤ (21440286546107/50000000000000 : ℝ)^3167 := by
    have hnat : (5273652283 : ℕ)^4191*50000000000000^3167 ≤ 21440286546107^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273652283 10000000000 21440286546107 50000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4191/1024 : ℝ)) 4191 3167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-103615621/500000000 : ℝ), (543834861/1000000000 : ℝ), (5273652283/10000000000 : ℝ)] ![(12457809955579/100000000000000 : ℝ), (5582702117151/12500000000000 : ℝ), (21440286546107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-103615621/500000000 : ℝ)|^4191 ≤ (12457809955579/100000000000000 : ℝ)^3167
        have hw : |(-103615621/500000000 : ℝ)|=(103615621/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543834861/1000000000 : ℝ)|^4191 ≤ (5582702117151/12500000000000 : ℝ)^3167
        have hw : |(543834861/1000000000 : ℝ)|=(543834861/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273652283/10000000000 : ℝ)|^4191 ≤ (21440286546107/50000000000000 : ℝ)^3167
        have hw : |(5273652283/10000000000 : ℝ)|=(5273652283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1189_box_13 (p : ℝ) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (67104557/125000000 : ℝ)*x 0 + (-541756327/2500000000 : ℝ)*x 1 + (2636826053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67104557/125000000 : ℝ)^4191 ≤ (21951319664221/50000000000000 : ℝ)^3167 := by
    have hnat : (67104557 : ℕ)^4191*50000000000000^3167 ≤ 21951319664221^3167*125000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67104557 125000000 21951319664221 50000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541756327/2500000000 : ℝ)^4191 ≤ (1652098684057/12500000000000 : ℝ)^3167 := by
    have hnat : (541756327 : ℕ)^4191*12500000000000^3167 ≤ 1652098684057^3167*2500000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541756327 2500000000 1652098684057 12500000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636826053/5000000000 : ℝ)^4191 ≤ (8576114237533/20000000000000 : ℝ)^3167 := by
    have hnat : (2636826053 : ℕ)^4191*20000000000000^3167 ≤ 8576114237533^3167*5000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636826053 5000000000 8576114237533 20000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4191/1024 : ℝ)) 4191 3167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67104557/125000000 : ℝ), (-541756327/2500000000 : ℝ), (2636826053/5000000000 : ℝ)] ![(21951319664221/50000000000000 : ℝ), (1652098684057/12500000000000 : ℝ), (8576114237533/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67104557/125000000 : ℝ)|^4191 ≤ (21951319664221/50000000000000 : ℝ)^3167
        have hw : |(67104557/125000000 : ℝ)|=(67104557/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-541756327/2500000000 : ℝ)|^4191 ≤ (1652098684057/12500000000000 : ℝ)^3167
        have hw : |(-541756327/2500000000 : ℝ)|=(541756327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636826053/5000000000 : ℝ)|^4191 ≤ (8576114237533/20000000000000 : ℝ)^3167
        have hw : |(2636826053/5000000000 : ℝ)|=(2636826053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1189_box_14 (p : ℝ) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5368364597/10000000000 : ℝ)*x 0 + (2636826023/5000000000 : ℝ)*x 1 + (-1083512669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368364597/10000000000 : ℝ)^4191 ≤ (21951319864433/50000000000000 : ℝ)^3167 := by
    have hnat : (5368364597 : ℕ)^4191*50000000000000^3167 ≤ 21951319864433^3167*10000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368364597 10000000000 21951319864433 50000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636826023/5000000000 : ℝ)^4191 ≤ (5360071317757/12500000000000 : ℝ)^3167 := by
    have hnat : (2636826023 : ℕ)^4191*12500000000000^3167 ≤ 5360071317757^3167*5000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636826023 5000000000 5360071317757 12500000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083512669/5000000000 : ℝ)^4191 ≤ (3304197428647/25000000000000 : ℝ)^3167 := by
    have hnat : (1083512669 : ℕ)^4191*25000000000000^3167 ≤ 3304197428647^3167*5000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083512669 5000000000 3304197428647 25000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4191/1024 : ℝ)) 4191 3167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368364597/10000000000 : ℝ), (2636826023/5000000000 : ℝ), (-1083512669/5000000000 : ℝ)] ![(21951319864433/50000000000000 : ℝ), (5360071317757/12500000000000 : ℝ), (3304197428647/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368364597/10000000000 : ℝ)|^4191 ≤ (21951319864433/50000000000000 : ℝ)^3167
        have hw : |(5368364597/10000000000 : ℝ)|=(5368364597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636826023/5000000000 : ℝ)|^4191 ≤ (5360071317757/12500000000000 : ℝ)^3167
        have hw : |(2636826023/5000000000 : ℝ)|=(2636826023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1083512669/5000000000 : ℝ)|^4191 ≤ (3304197428647/25000000000000 : ℝ)^3167
        have hw : |(-1083512669/5000000000 : ℝ)|=(1083512669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1189_box_15 (p : ℝ) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2116012279/5000000000 : ℝ)*x 0 + (2211532407/5000000000 : ℝ)*x 1 + (1105766179/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116012279/5000000000 : ℝ)^4191 ≤ (32047810508833/100000000000000 : ℝ)^3167 := by
    have hnat : (2116012279 : ℕ)^4191*100000000000000^3167 ≤ 32047810508833^3167*5000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116012279 5000000000 32047810508833 100000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2211532407/5000000000 : ℝ)^4191 ≤ (33976095233867/100000000000000 : ℝ)^3167 := by
    have hnat : (2211532407 : ℕ)^4191*100000000000000^3167 ≤ 33976095233867^3167*5000000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211532407 5000000000 33976095233867 100000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1105766179/2500000000 : ℝ)^4191 ≤ (8494023559417/25000000000000 : ℝ)^3167 := by
    have hnat : (1105766179 : ℕ)^4191*25000000000000^3167 ≤ 8494023559417^3167*2500000000^4191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105766179 2500000000 8494023559417 25000000000000 4191 3167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4191/1024 : ℝ)) 4191 3167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2116012279/5000000000 : ℝ), (2211532407/5000000000 : ℝ), (1105766179/2500000000 : ℝ)] ![(32047810508833/100000000000000 : ℝ), (33976095233867/100000000000000 : ℝ), (8494023559417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2116012279/5000000000 : ℝ)|^4191 ≤ (32047810508833/100000000000000 : ℝ)^3167
        have hw : |(2116012279/5000000000 : ℝ)|=(2116012279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2211532407/5000000000 : ℝ)|^4191 ≤ (33976095233867/100000000000000 : ℝ)^3167
        have hw : |(2211532407/5000000000 : ℝ)|=(2211532407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1105766179/2500000000 : ℝ)|^4191 ≤ (8494023559417/25000000000000 : ℝ)^3167
        have hw : |(1105766179/2500000000 : ℝ)|=(1105766179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1189_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75195779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5707/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62237/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11867/20000 : ℝ) ∧ (79951/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83229/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (563/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5707/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (563/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5707/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (563/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5707/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (563/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5707/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (563/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5707/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (563/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5707/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5707/50000 : ℝ) ^ (8381/2048 : ℝ) ≤ (6946035260015751/50000000000000000000 : ℝ) := by
    have hpowers : (5707/50000 : ℝ)^8381 ≤ (6946035260015751/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5707 : ℕ)^8381*50000000000000000000^2048 ≤ 6946035260015751^2048*50000^8381 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5707 50000 6946035260015751 50000000000000000000 8381 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5707/50000 : ℝ)) (X := (6946035260015751/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8381 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (563/4000 : ℝ) ^ (8381/2048 : ℝ) ≤ (32749753986702043/100000000000000000000 : ℝ) := by
    have hpowers : (563/4000 : ℝ)^8381 ≤ (32749753986702043/100000000000000000000 : ℝ)^2048 := by
      have hnat : (563 : ℕ)^8381*100000000000000000000^2048 ≤ 32749753986702043^2048*4000^8381 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        563 4000 32749753986702043 100000000000000000000 8381 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (563/4000 : ℝ)) (X := (32749753986702043/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8381 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006946035260015751/25000000000000000000 : ℝ) ≤ (5000339434128471/5000000000000000 : ℝ) ^ (8381/2048 : ℝ) := by
    have hpowers : (25006946035260015751/25000000000000000000 : ℝ)^2048 ≤ (5000339434128471/5000000000000000 : ℝ)^8381 := by
      have hnat : (25006946035260015751 : ℕ)^2048*5000000000000000^8381 ≤ 5000339434128471^8381*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006946035260015751 25000000000000000000 5000339434128471 5000000000000000 2048 8381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000339434128471/5000000000000000 : ℝ)) (X := (25006946035260015751/25000000000000000000 : ℝ)) (by norm_num) 8381 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009328364901346709/20000000000000000000 : ℝ) ≤ (2000227909862931/2000000000000000 : ℝ) ^ (8381/2048 : ℝ) := by
    have hpowers : (20009328364901346709/20000000000000000000 : ℝ)^2048 ≤ (2000227909862931/2000000000000000 : ℝ)^8381 := by
      have hnat : (20009328364901346709 : ℕ)^2048*2000000000000000^8381 ≤ 2000227909862931^8381*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009328364901346709 20000000000000000000 2000227909862931 2000000000000000 2048 8381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000227909862931/2000000000000000 : ℝ)) (X := (20009328364901346709/20000000000000000000 : ℝ)) (by norm_num) 8381 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032749753986702043/50000000000000000000 : ℝ) ≤ (625100014398273/625000000000000 : ℝ) ^ (8381/2048 : ℝ) := by
    have hpowers : (50032749753986702043/50000000000000000000 : ℝ)^2048 ≤ (625100014398273/625000000000000 : ℝ)^8381 := by
      have hnat : (50032749753986702043 : ℕ)^2048*625000000000000^8381 ≤ 625100014398273^8381*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032749753986702043 50000000000000000000 625100014398273 625000000000000 2048 8381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625100014398273/625000000000000 : ℝ)) (X := (50032749753986702043/50000000000000000000 : ℝ)) (by norm_num) 8381 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6946035260015751/50000000000000000000 : ℝ) ≤ ((4433548340207708383/4435000000000000000 : ℝ)+2*(153560352571/88700000000000 : ℝ)*(5707/50000 : ℝ))^(8381/2048 : ℝ) := by
    rw [show (4433548340207708383/4435000000000000000 : ℝ)+2*(153560352571/88700000000000 : ℝ)*(5707/50000 : ℝ)=(5000339434128471/5000000000000000 : ℝ) by norm_num, show 1+2*(6946035260015751/50000000000000000000 : ℝ)=(25006946035260015751/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32749753986702043/100000000000000000000 : ℝ)+(6946035260015751/50000000000000000000 : ℝ) ≤ ((4433548340207708383/4435000000000000000 : ℝ)+(153560352571/88700000000000 : ℝ)*((563/4000 : ℝ)+(5707/50000 : ℝ)))^(8381/2048 : ℝ) := by
    rw [show (4433548340207708383/4435000000000000000 : ℝ)+(153560352571/88700000000000 : ℝ)*((563/4000 : ℝ)+(5707/50000 : ℝ))=(2000227909862931/2000000000000000 : ℝ) by norm_num, show 1+(32749753986702043/100000000000000000000 : ℝ)+(6946035260015751/50000000000000000000 : ℝ)=(20009328364901346709/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32749753986702043/100000000000000000000 : ℝ) ≤ ((4433548340207708383/4435000000000000000 : ℝ)+2*(153560352571/88700000000000 : ℝ)*(563/4000 : ℝ))^(8381/2048 : ℝ) := by
    rw [show (4433548340207708383/4435000000000000000 : ℝ)+2*(153560352571/88700000000000 : ℝ)*(563/4000 : ℝ)=(625100014398273/625000000000000 : ℝ) by norm_num, show 1+2*(32749753986702043/100000000000000000000 : ℝ)=(50032749753986702043/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4433548340207708383/4435000000000000000 : ℝ)*(X 1 0+X 2 0)+(153560352571/88700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8381/2048 : ℝ)) (lo := (5707/50000 : ℝ)) (hi := (563/4000 : ℝ)) (c := (4433548340207708383/4435000000000000000 : ℝ)) (alpha := (153560352571/88700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4433548340207708383/4435000000000000000 : ℝ)*(X 0 1+X 2 1)+(153560352571/88700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8381/2048 : ℝ)) (lo := (5707/50000 : ℝ)) (hi := (563/4000 : ℝ)) (c := (4433548340207708383/4435000000000000000 : ℝ)) (alpha := (153560352571/88700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4433548340207708383/4435000000000000000 : ℝ)*(X 0 2+X 1 2)+(153560352571/88700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8381/2048 : ℝ)) (lo := (5707/50000 : ℝ)) (hi := (563/4000 : ℝ)) (c := (4433548340207708383/4435000000000000000 : ℝ)) (alpha := (153560352571/88700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2019248273/10000000000 : ℝ)*X 0 0+(2687815483/5000000000 : ℝ)*X 0 1+(5375629303/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1189_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296394619/10000000000 : ℝ)*X 1 0+(-2126818889/10000000000 : ℝ)*X 1 1+(1343907557/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1189_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2648197551/5000000000 : ℝ)*X 2 0+(2687814821/5000000000 : ℝ)*X 2 1+(-212681903/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1189_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4465149657/10000000000 : ℝ)*X 0 0+(2153322191/5000000000 : ℝ)*X 0 1+(4306645927/10000000000 : ℝ)*X 0 2+(4465149657/10000000000 : ℝ)*X 1 0+(2153322191/5000000000 : ℝ)*X 1 1+(4306645927/10000000000 : ℝ)*X 1 2+(4465149657/10000000000 : ℝ)*X 2 0+(2153322191/5000000000 : ℝ)*X 2 1+(4306645927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1189_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-567840477/2500000000 : ℝ)*X 0 0+(132042781/250000000 : ℝ)*X 0 1+(5281710887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1189_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((670334871/1250000000 : ℝ)*X 1 0+(-2163900333/10000000000 : ℝ)*X 1 1+(165053469/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1189_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362679007/10000000000 : ℝ)*X 2 0+(132042777/250000000 : ℝ)*X 2 1+(-432780037/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1189_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4250660637/10000000000 : ℝ)*X 0 0+(882773839/2000000000 : ℝ)*X 0 1+(882773833/2000000000 : ℝ)*X 0 2+(4250660637/10000000000 : ℝ)*X 1 0+(882773839/2000000000 : ℝ)*X 1 1+(882773833/2000000000 : ℝ)*X 1 2+(4250660637/10000000000 : ℝ)*X 2 0+(882773839/2000000000 : ℝ)*X 2 1+(882773833/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1189_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2218588641/10000000000 : ℝ)*X 0 0+(5217747901/10000000000 : ℝ)*X 0 1+(5385241601/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1189_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((330600523/625000000 : ℝ)*X 1 0+(-1061477691/5000000000 : ℝ)*X 1 1+(5385241653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1189_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289608363/10000000000 : ℝ)*X 2 0+(5385241579/10000000000 : ℝ)*X 2 1+(-66342359/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1189_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1121706937/2500000000 : ℝ)*X 0 0+(4295665663/10000000000 : ℝ)*X 0 1+(4295665477/10000000000 : ℝ)*X 0 2+(1121706937/2500000000 : ℝ)*X 1 0+(4295665663/10000000000 : ℝ)*X 1 1+(4295665477/10000000000 : ℝ)*X 1 2+(1121706937/2500000000 : ℝ)*X 2 0+(4295665663/10000000000 : ℝ)*X 2 1+(4295665477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1189_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-103615621/500000000 : ℝ)*X 0 0+(543834861/1000000000 : ℝ)*X 0 1+(5273652283/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1189_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((67104557/125000000 : ℝ)*X 1 0+(-541756327/2500000000 : ℝ)*X 1 1+(2636826053/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1189_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368364597/10000000000 : ℝ)*X 2 0+(2636826023/5000000000 : ℝ)*X 2 1+(-1083512669/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1189_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2116012279/5000000000 : ℝ)*X 0 0+(2211532407/5000000000 : ℝ)*X 0 1+(1105766179/2500000000 : ℝ)*X 0 2+(2116012279/5000000000 : ℝ)*X 1 0+(2211532407/5000000000 : ℝ)*X 1 1+(1105766179/2500000000 : ℝ)*X 1 2+(2116012279/5000000000 : ℝ)*X 2 0+(2211532407/5000000000 : ℝ)*X 2 1+(1105766179/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1189_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62237/100000 : ℝ) ≤ (-69003006483515424624287911193151/110875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18600047/100000000000000 : ℝ)*(upper0) + (24207069/100000000000000 : ℝ)*(lower2) + (51330131/100000000000000 : ℝ)*(upper4) + (5341887/25000000000000 : ℝ)*(upper5) + (3959558232686699/100000000000000 : ℝ)*(major0) + (3959558232686699/100000000000000 : ℝ)*(major1) + (3959558232686699/100000000000000 : ℝ)*(major2) + (8273414259/100000000000000 : ℝ)*(sp1) + (1719404873/25000000000000 : ℝ)*(sp3) + (5307014965684223/100000000000000 : ℝ)*(sp4) + (5307020400115927/100000000000000 : ℝ)*(sp5) + (2653514336765093/50000000000000 : ℝ)*(sp6) + (658206474815493/25000000000000 : ℝ)*(sp7) + (13707845963/100000000000000 : ℝ)*(sp8) + (1316416388440733/50000000000000 : ℝ)*(f.failure) + (2653514336765093/50000000000000 : ℝ)*(f.sum) + (19056212500147/2217500000000000000000000000 : ℝ)*base65 + (108426672836847717/443500000000000000000000000000000 : ℝ)*base67 + (2910655539733347717/443500000000000000000000000000000 : ℝ)*base69 + (1205104869823847717/443500000000000000000000000000000 : ℝ)*base71 + (2983775009359/4435000000000000000000000000 : ℝ)*base73 + (1363770601809347717/443500000000000000000000000000000 : ℝ)*base75 + (2787153792266347717/443500000000000000000000000000000 : ℝ)*base77 + (124996556282652283/443500000000000000000000000000000 : ℝ)*base80 + (24747147083639/4435000000000000000000000000 : ℝ)*base81 + (38266007/2500000000000000000000 : ℝ)*base89 + (38266007/2500000000000000000000 : ℝ)*base91 + (38266007/2500000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (11867/20000 : ℝ) ≤ (131581145676321534766939335623661/221750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (511444739/100000000000000 : ℝ)*(upper0) + (89366937/100000000000000 : ℝ)*(upper3) + (4328049/4000000000000 : ℝ)*(upper4) + (4024491314048437/100000000000000 : ℝ)*(major0) + (4024491314048437/100000000000000 : ℝ)*(major1) + (4024491314048437/100000000000000 : ℝ)*(major2) + (1338292836225729/25000000000000 : ℝ)*(sp0) + (5353153809550557/100000000000000 : ℝ)*(sp1) + (5353176493226697/100000000000000 : ℝ)*(sp2) + (2676006327615599/100000000000000 : ℝ)*(sp3) + (20412096657/50000000000000 : ℝ)*(sp5) + (9070258587/50000000000000 : ℝ)*(sp6) + (24640803/1000000000000 : ℝ)*(sp7) + (4657768191/20000000000000 : ℝ)*(sp8) + (2676008791695899/100000000000000 : ℝ)*(f.failure) + (5353194633743871/100000000000000 : ℝ)*(f.sum) + (11351069771173/4435000000000000000000000000 : ℝ)*base66 + (3221181178647797371/443500000000000000000000000000000 : ℝ)*base67 + (748834704203297371/443500000000000000000000000000000 : ℝ)*base69 + (2329982231966297371/443500000000000000000000000000000 : ℝ)*base71 + (110786441142039/2217500000000000000000000000 : ℝ)*base74 + (3543363238485797371/443500000000000000000000000000000 : ℝ)*base75 + (3287085577566797371/443500000000000000000000000000000 : ℝ)*base77 + (3985039818837297371/443500000000000000000000000000000 : ℝ)*base79 + (2267528197943/1108750000000000000000000000 : ℝ)*base81 + (6410321/5000000000000000000000 : ℝ)*base89 + (6410321/5000000000000000000000 : ℝ)*base91 + (6410321/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79951/100000 : ℝ) ≤ (88648273065458306009692809386613/110875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28182343/50000000000000 : ℝ)*(upper1) + (42464357/100000000000000 : ℝ)*(upper2) + (1419437/10000000000000 : ℝ)*(upper3) + (6450113/25000000000000 : ℝ)*(lower5) + (2245960670571063/50000000000000 : ℝ)*(major0) + (2245960670571063/50000000000000 : ℝ)*(major1) + (2245960670571063/50000000000000 : ℝ)*(major2) + (76176278157/100000000000000 : ℝ)*(sp1) + (4499938943/25000000000000 : ℝ)*(sp2) + (27628800971/100000000000000 : ℝ)*(sp3) + (1194074817567739/20000000000000 : ℝ)*(sp8) + (5970297911560537/100000000000000 : ℝ)*(sp9) + (2985178044041461/50000000000000 : ℝ)*(sp10) + (2986789850104411/100000000000000 : ℝ)*(sp11) + (2986817478905383/100000000000000 : ℝ)*(f.failure) + (1194074817567739/20000000000000 : ℝ)*(f.sum) + (1317794144073/2217500000000000000000000000 : ℝ)*base65 + (1264147813313471129/221750000000000000000000000000000 : ℝ)*base67 + (2410715638652278871/221750000000000000000000000000000 : ℝ)*base70 + (957343258246471129/221750000000000000000000000000000 : ℝ)*base71 + (3994264422017/2217500000000000000000000000 : ℝ)*base74 + (7488175673125778871/221750000000000000000000000000000 : ℝ)*base76 + (906364123822221129/221750000000000000000000000000000 : ℝ)*base77 + (2546932032606221129/221750000000000000000000000000000 : ℝ)*base79 + (56885356754683/2217500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (41978357/5000000000000000000000 : ℝ)*base89 + (41978357/5000000000000000000000 : ℝ)*base91 + (41978357/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-83229/100000 : ℝ) ≤ (-1153469620787425047057020821539/1385937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (5800987/25000000000000 : ℝ)*(upper1) + (76038957/100000000000000 : ℝ)*(upper3) + (15970217/25000000000000 : ℝ)*(upper5) + (113178767281653/2500000000000 : ℝ)*(major0) + (113178767281653/2500000000000 : ℝ)*(major1) + (113178767281653/2500000000000 : ℝ)*(major2) + (10583644299/50000000000000 : ℝ)*(sp4) + (220084289561/100000000000000 : ℝ)*(sp5) + (507026769/195312500000 : ℝ)*(sp6) + (94099131389/50000000000000 : ℝ)*(sp7) + (303588993728727/5000000000000 : ℝ)*(sp12) + (6071580957573577/100000000000000 : ℝ)*(sp13) + (607154144415741/10000000000000 : ℝ)*(sp14) + (3010054365529347/100000000000000 : ℝ)*(sp15) + (24081940510337/800000000000 : ℝ)*(f.failure) + (3035900520931569/50000000000000 : ℝ)*(f.sum) + (255844838067/221750000000000000000000000 : ℝ)*base65 + (56479993244852901/11087500000000000000000000000000 : ℝ)*base68 + (134304829735602901/11087500000000000000000000000000 : ℝ)*base70 + (90448836757402901/11087500000000000000000000000000 : ℝ)*base72 + (2506125110889/887000000000000000000000000 : ℝ)*base74 + (692415756252452901/11087500000000000000000000000000 : ℝ)*base76 + (33820336333977901/11087500000000000000000000000000 : ℝ)*base78 + (12054104109397099/11087500000000000000000000000000 : ℝ)*base79 + (1230963666159/88700000000000000000000000 : ℝ)*base82 + (267523/40000000000000000000 : ℝ)*base89 + (267523/40000000000000000000 : ℝ)*base91 + (267523/40000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1189_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75195779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5707/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62237/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11867/20000 : ℝ) else (79951/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83229/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1189_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1189_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75195779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5707/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62237/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11867/20000 : ℝ) else (79951/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83229/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1189_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8381/2048 : ℝ) ≤ p) (hpb : p ≤ (4191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75195779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (563/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5707/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62237/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11867/20000 : ℝ) else (79951/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83229/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1189_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution

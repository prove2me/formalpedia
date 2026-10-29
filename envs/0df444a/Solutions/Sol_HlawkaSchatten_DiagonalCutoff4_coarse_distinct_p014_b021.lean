-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p014_b021
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:40:26.064966+00:00
-- url     : https://prove2.me/submissions/a6402cd8-7116-4381-8e70-e1cf19238a4c

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_FiniteCharts
import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c314041_s0_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1329246449/5000000000 : ℝ)*x 0 + (-4465182703/10000000000 : ℝ)*x 1 + (2676548763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1329246449/5000000000 : ℝ)^19 ≤ (18672607668709/100000000000000 : ℝ)^15 := by
    have hnat : (1329246449 : ℕ)^19*100000000000000^15 ≤ 18672607668709^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1329246449 5000000000 18672607668709 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4465182703/10000000000 : ℝ)^19 ≤ (36013309168393/100000000000000 : ℝ)^15 := by
    have hnat : (4465182703 : ℕ)^19*100000000000000^15 ≤ 36013309168393^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4465182703 10000000000 36013309168393 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2676548763/5000000000 : ℝ)^19 ≤ (4531408314757/10000000000000 : ℝ)^15 := by
    have hnat : (2676548763 : ℕ)^19*10000000000000^15 ≤ 4531408314757^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676548763 5000000000 4531408314757 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1329246449/5000000000 : ℝ), (-4465182703/10000000000 : ℝ), (2676548763/5000000000 : ℝ)] ![(18672607668709/100000000000000 : ℝ), (36013309168393/100000000000000 : ℝ), (4531408314757/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1329246449/5000000000 : ℝ)|^19 ≤ (18672607668709/100000000000000 : ℝ)^15
        have hw : |(-1329246449/5000000000 : ℝ)|=(1329246449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4465182703/10000000000 : ℝ)|^19 ≤ (36013309168393/100000000000000 : ℝ)^15
        have hw : |(-4465182703/10000000000 : ℝ)|=(4465182703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2676548763/5000000000 : ℝ)|^19 ≤ (4531408314757/10000000000000 : ℝ)^15
        have hw : |(2676548763/5000000000 : ℝ)|=(2676548763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s0_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (176825701/625000000 : ℝ)*x 0 + (2620344021/5000000000 : ℝ)*x 1 + (2216437389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (176825701/625000000 : ℝ)^19 ≤ (20204253244143/100000000000000 : ℝ)^15 := by
    have hnat : (176825701 : ℕ)^19*100000000000000^15 ≤ 20204253244143^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176825701 625000000 20204253244143 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620344021/5000000000 : ℝ)^19 ≤ (22056090168113/50000000000000 : ℝ)^15 := by
    have hnat : (2620344021 : ℕ)^19*50000000000000^15 ≤ 22056090168113^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620344021 5000000000 22056090168113 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2216437389/5000000000 : ℝ)^19 ≤ (35683566401613/100000000000000 : ℝ)^15 := by
    have hnat : (2216437389 : ℕ)^19*100000000000000^15 ≤ 35683566401613^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216437389 5000000000 35683566401613 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(176825701/625000000 : ℝ), (2620344021/5000000000 : ℝ), (2216437389/5000000000 : ℝ)] ![(20204253244143/100000000000000 : ℝ), (22056090168113/50000000000000 : ℝ), (35683566401613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(176825701/625000000 : ℝ)|^19 ≤ (20204253244143/100000000000000 : ℝ)^15
        have hw : |(176825701/625000000 : ℝ)|=(176825701/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620344021/5000000000 : ℝ)|^19 ≤ (22056090168113/50000000000000 : ℝ)^15
        have hw : |(2620344021/5000000000 : ℝ)|=(2620344021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2216437389/5000000000 : ℝ)|^19 ≤ (35683566401613/100000000000000 : ℝ)^15
        have hw : |(2216437389/5000000000 : ℝ)|=(2216437389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s0_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (876091133/2500000000 : ℝ)*x 0 + (-4122525491/10000000000 : ℝ)*x 1 + (617787739/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (876091133/2500000000 : ℝ)^19 ≤ (26495477441301/100000000000000 : ℝ)^15 := by
    have hnat : (876091133 : ℕ)^19*100000000000000^15 ≤ 26495477441301^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876091133 2500000000 26495477441301 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4122525491/10000000000 : ℝ)^19 ≤ (1017162322251/3125000000000 : ℝ)^15 := by
    have hnat : (4122525491 : ℕ)^19*3125000000000^15 ≤ 1017162322251^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4122525491 10000000000 1017162322251 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (617787739/1250000000 : ℝ)^19 ≤ (40955328233247/100000000000000 : ℝ)^15 := by
    have hnat : (617787739 : ℕ)^19*100000000000000^15 ≤ 40955328233247^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617787739 1250000000 40955328233247 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(876091133/2500000000 : ℝ), (-4122525491/10000000000 : ℝ), (617787739/1250000000 : ℝ)] ![(26495477441301/100000000000000 : ℝ), (1017162322251/3125000000000 : ℝ), (40955328233247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(876091133/2500000000 : ℝ)|^19 ≤ (26495477441301/100000000000000 : ℝ)^15
        have hw : |(876091133/2500000000 : ℝ)|=(876091133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4122525491/10000000000 : ℝ)|^19 ≤ (1017162322251/3125000000000 : ℝ)^15
        have hw : |(-4122525491/10000000000 : ℝ)|=(4122525491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(617787739/1250000000 : ℝ)|^19 ≤ (40955328233247/100000000000000 : ℝ)^15
        have hw : |(617787739/1250000000 : ℝ)|=(617787739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s0_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1333409871/5000000000 : ℝ)*x 0 + (-4637876539/10000000000 : ℝ)*x 1 + (5180052691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1333409871/5000000000 : ℝ)^19 ≤ (1171670031549/6250000000000 : ℝ)^15 := by
    have hnat : (1333409871 : ℕ)^19*6250000000000^15 ≤ 1171670031549^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1333409871 5000000000 1171670031549 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4637876539/10000000000 : ℝ)^19 ≤ (18893291999563/50000000000000 : ℝ)^15 := by
    have hnat : (4637876539 : ℕ)^19*50000000000000^15 ≤ 18893291999563^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4637876539 10000000000 18893291999563 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180052691/10000000000 : ℝ)^19 ≤ (10866673872637/25000000000000 : ℝ)^15 := by
    have hnat : (5180052691 : ℕ)^19*25000000000000^15 ≤ 10866673872637^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180052691 10000000000 10866673872637 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1333409871/5000000000 : ℝ), (-4637876539/10000000000 : ℝ), (5180052691/10000000000 : ℝ)] ![(1171670031549/6250000000000 : ℝ), (18893291999563/50000000000000 : ℝ), (10866673872637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1333409871/5000000000 : ℝ)|^19 ≤ (1171670031549/6250000000000 : ℝ)^15
        have hw : |(-1333409871/5000000000 : ℝ)|=(1333409871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4637876539/10000000000 : ℝ)|^19 ≤ (18893291999563/50000000000000 : ℝ)^15
        have hw : |(-4637876539/10000000000 : ℝ)|=(4637876539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180052691/10000000000 : ℝ)|^19 ≤ (10866673872637/25000000000000 : ℝ)^15
        have hw : |(5180052691/10000000000 : ℝ)|=(5180052691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s0_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (345697991/1250000000 : ℝ)*x 0 + (5251541331/10000000000 : ℝ)*x 1 + (4477738919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (345697991/1250000000 : ℝ)^19 ≤ (6134512029/31250000000 : ℝ)^15 := by
    have hnat : (345697991 : ℕ)^19*31250000000^15 ≤ 6134512029^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345697991 1250000000 6134512029 31250000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5251541331/10000000000 : ℝ)^19 ≤ (44227928409107/100000000000000 : ℝ)^15 := by
    have hnat : (5251541331 : ℕ)^19*100000000000000^15 ≤ 44227928409107^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251541331 10000000000 44227928409107 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4477738919/10000000000 : ℝ)^19 ≤ (36141633085029/100000000000000 : ℝ)^15 := by
    have hnat : (4477738919 : ℕ)^19*100000000000000^15 ≤ 36141633085029^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477738919 10000000000 36141633085029 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(345697991/1250000000 : ℝ), (5251541331/10000000000 : ℝ), (4477738919/10000000000 : ℝ)] ![(6134512029/31250000000 : ℝ), (44227928409107/100000000000000 : ℝ), (36141633085029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(345697991/1250000000 : ℝ)|^19 ≤ (6134512029/31250000000 : ℝ)^15
        have hw : |(345697991/1250000000 : ℝ)|=(345697991/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5251541331/10000000000 : ℝ)|^19 ≤ (44227928409107/100000000000000 : ℝ)^15
        have hw : |(5251541331/10000000000 : ℝ)|=(5251541331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4477738919/10000000000 : ℝ)|^19 ≤ (36141633085029/100000000000000 : ℝ)^15
        have hw : |(4477738919/10000000000 : ℝ)|=(4477738919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s0_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (447730921/625000000 : ℝ)*x 0 + (-539783567/2000000000 : ℝ)*x 1 + (-1143242029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (447730921/625000000 : ℝ)^19 ≤ (32770039216077/50000000000000 : ℝ)^15 := by
    have hnat : (447730921 : ℕ)^19*50000000000000^15 ≤ 32770039216077^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447730921 625000000 32770039216077 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539783567/2000000000 : ℝ)^19 ≤ (59478078321/312500000000 : ℝ)^15 := by
    have hnat : (539783567 : ℕ)^19*312500000000^15 ≤ 59478078321^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539783567 2000000000 59478078321 312500000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1143242029/5000000000 : ℝ)^19 ≤ (1928367061911/12500000000000 : ℝ)^15 := by
    have hnat : (1143242029 : ℕ)^19*12500000000000^15 ≤ 1928367061911^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143242029 5000000000 1928367061911 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(447730921/625000000 : ℝ), (-539783567/2000000000 : ℝ), (-1143242029/5000000000 : ℝ)] ![(32770039216077/50000000000000 : ℝ), (59478078321/312500000000 : ℝ), (1928367061911/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(447730921/625000000 : ℝ)|^19 ≤ (32770039216077/50000000000000 : ℝ)^15
        have hw : |(447730921/625000000 : ℝ)|=(447730921/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-539783567/2000000000 : ℝ)|^19 ≤ (59478078321/312500000000 : ℝ)^15
        have hw : |(-539783567/2000000000 : ℝ)|=(539783567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1143242029/5000000000 : ℝ)|^19 ≤ (1928367061911/12500000000000 : ℝ)^15
        have hw : |(-1143242029/5000000000 : ℝ)|=(1143242029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s0_10 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1999999983/2000000000 : ℝ)*x 0 + (2961/10000000000 : ℝ)*x 1 + (2961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1999999983/2000000000 : ℝ)^19 ≤ (49999999461667/50000000000000 : ℝ)^15 := by
    have hnat : (1999999983 : ℕ)^19*50000000000000^15 ≤ 49999999461667^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999999983 2000000000 49999999461667 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2961/10000000000 : ℝ)^19 ≤ (537637/100000000000000 : ℝ)^15 := by
    have hnat : (2961 : ℕ)^19*100000000000000^15 ≤ 537637^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2961 10000000000 537637 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2961/10000000000 : ℝ)^19 ≤ (537637/100000000000000 : ℝ)^15 := by
    have hnat : (2961 : ℕ)^19*100000000000000^15 ≤ 537637^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2961 10000000000 537637 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1999999983/2000000000 : ℝ), (2961/10000000000 : ℝ), (2961/10000000000 : ℝ)] ![(49999999461667/50000000000000 : ℝ), (537637/100000000000000 : ℝ), (537637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1999999983/2000000000 : ℝ)|^19 ≤ (49999999461667/50000000000000 : ℝ)^15
        have hw : |(1999999983/2000000000 : ℝ)|=(1999999983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2961/10000000000 : ℝ)|^19 ≤ (537637/100000000000000 : ℝ)^15
        have hw : |(2961/10000000000 : ℝ)|=(2961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2961/10000000000 : ℝ)|^19 ≤ (537637/100000000000000 : ℝ)^15
        have hw : |(2961/10000000000 : ℝ)|=(2961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s0_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3614666707/10000000000 : ℝ)*x 0 + (-147235547/400000000 : ℝ)*x 1 + (2626642109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3614666707/10000000000 : ℝ)^19 ≤ (27556229607423/100000000000000 : ℝ)^15 := by
    have hnat : (3614666707 : ℕ)^19*100000000000000^15 ≤ 27556229607423^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3614666707 10000000000 27556229607423 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147235547/400000000 : ℝ)^19 ≤ (28197248489081/100000000000000 : ℝ)^15 := by
    have hnat : (147235547 : ℕ)^19*100000000000000^15 ≤ 28197248489081^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147235547 400000000 28197248489081 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626642109/5000000000 : ℝ)^19 ≤ (22123260942787/50000000000000 : ℝ)^15 := by
    have hnat : (2626642109 : ℕ)^19*50000000000000^15 ≤ 22123260942787^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626642109 5000000000 22123260942787 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3614666707/10000000000 : ℝ), (-147235547/400000000 : ℝ), (2626642109/5000000000 : ℝ)] ![(27556229607423/100000000000000 : ℝ), (28197248489081/100000000000000 : ℝ), (22123260942787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3614666707/10000000000 : ℝ)|^19 ≤ (27556229607423/100000000000000 : ℝ)^15
        have hw : |(3614666707/10000000000 : ℝ)|=(3614666707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-147235547/400000000 : ℝ)|^19 ≤ (28197248489081/100000000000000 : ℝ)^15
        have hw : |(-147235547/400000000 : ℝ)|=(147235547/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626642109/5000000000 : ℝ)|^19 ≤ (22123260942787/50000000000000 : ℝ)^15
        have hw : |(2626642109/5000000000 : ℝ)|=(2626642109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s0_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2453778633/10000000000 : ℝ)*x 0 + (-2180558841/5000000000 : ℝ)*x 1 + (2809144971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2453778633/10000000000 : ℝ)^19 ≤ (16870378062417/100000000000000 : ℝ)^15 := by
    have hnat : (2453778633 : ℕ)^19*100000000000000^15 ≤ 16870378062417^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2453778633 10000000000 16870378062417 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2180558841/5000000000 : ℝ)^19 ≤ (17476745363147/50000000000000 : ℝ)^15 := by
    have hnat : (2180558841 : ℕ)^19*50000000000000^15 ≤ 17476745363147^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180558841 5000000000 17476745363147 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2809144971/5000000000 : ℝ)^19 ≤ (48176131187993/100000000000000 : ℝ)^15 := by
    have hnat : (2809144971 : ℕ)^19*100000000000000^15 ≤ 48176131187993^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2809144971 5000000000 48176131187993 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2453778633/10000000000 : ℝ), (-2180558841/5000000000 : ℝ), (2809144971/5000000000 : ℝ)] ![(16870378062417/100000000000000 : ℝ), (17476745363147/50000000000000 : ℝ), (48176131187993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2453778633/10000000000 : ℝ)|^19 ≤ (16870378062417/100000000000000 : ℝ)^15
        have hw : |(-2453778633/10000000000 : ℝ)|=(2453778633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2180558841/5000000000 : ℝ)|^19 ≤ (17476745363147/50000000000000 : ℝ)^15
        have hw : |(-2180558841/5000000000 : ℝ)|=(2180558841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2809144971/5000000000 : ℝ)|^19 ≤ (48176131187993/100000000000000 : ℝ)^15
        have hw : |(2809144971/5000000000 : ℝ)|=(2809144971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s0_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (338981959/1250000000 : ℝ)*x 0 + (2703406711/5000000000 : ℝ)*x 1 + (4361813919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338981959/1250000000 : ℝ)^19 ≤ (9574313909203/50000000000000 : ℝ)^15 := by
    have hnat : (338981959 : ℕ)^19*50000000000000^15 ≤ 9574313909203^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338981959 1250000000 9574313909203 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703406711/5000000000 : ℝ)^19 ≤ (22945406519951/50000000000000 : ℝ)^15 := by
    have hnat : (2703406711 : ℕ)^19*50000000000000^15 ≤ 22945406519951^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703406711 5000000000 22945406519951 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4361813919/10000000000 : ℝ)^19 ≤ (1092517472857/3125000000000 : ℝ)^15 := by
    have hnat : (4361813919 : ℕ)^19*3125000000000^15 ≤ 1092517472857^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361813919 10000000000 1092517472857 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338981959/1250000000 : ℝ), (2703406711/5000000000 : ℝ), (4361813919/10000000000 : ℝ)] ![(9574313909203/50000000000000 : ℝ), (22945406519951/50000000000000 : ℝ), (1092517472857/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338981959/1250000000 : ℝ)|^19 ≤ (9574313909203/50000000000000 : ℝ)^15
        have hw : |(338981959/1250000000 : ℝ)|=(338981959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703406711/5000000000 : ℝ)|^19 ≤ (22945406519951/50000000000000 : ℝ)^15
        have hw : |(2703406711/5000000000 : ℝ)|=(2703406711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4361813919/10000000000 : ℝ)|^19 ≤ (1092517472857/3125000000000 : ℝ)^15
        have hw : |(4361813919/10000000000 : ℝ)|=(4361813919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s0_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (746762591/1000000000 : ℝ)*x 0 + (-316421269/1250000000 : ℝ)*x 1 + (-510530173/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (746762591/1000000000 : ℝ)^19 ≤ (17270486712691/25000000000000 : ℝ)^15 := by
    have hnat : (746762591 : ℕ)^19*25000000000000^15 ≤ 17270486712691^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746762591 1000000000 17270486712691 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (316421269/1250000000 : ℝ)^19 ≤ (17548924124511/100000000000000 : ℝ)^15 := by
    have hnat : (316421269 : ℕ)^19*100000000000000^15 ≤ 17548924124511^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316421269 1250000000 17548924124511 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (510530173/2500000000 : ℝ)^19 ≤ (13369129007931/100000000000000 : ℝ)^15 := by
    have hnat : (510530173 : ℕ)^19*100000000000000^15 ≤ 13369129007931^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510530173 2500000000 13369129007931 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(746762591/1000000000 : ℝ), (-316421269/1250000000 : ℝ), (-510530173/2500000000 : ℝ)] ![(17270486712691/25000000000000 : ℝ), (17548924124511/100000000000000 : ℝ), (13369129007931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(746762591/1000000000 : ℝ)|^19 ≤ (17270486712691/25000000000000 : ℝ)^15
        have hw : |(746762591/1000000000 : ℝ)|=(746762591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-316421269/1250000000 : ℝ)|^19 ≤ (17548924124511/100000000000000 : ℝ)^15
        have hw : |(-316421269/1250000000 : ℝ)|=(316421269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-510530173/2500000000 : ℝ)|^19 ≤ (13369129007931/100000000000000 : ℝ)^15
        have hw : |(-510530173/2500000000 : ℝ)|=(510530173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s0_19 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1785605261/5000000000 : ℝ)*x 0 + (-1965034267/5000000000 : ℝ)*x 1 + (5062982961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1785605261/5000000000 : ℝ)^19 ≤ (27137275260711/100000000000000 : ℝ)^15 := by
    have hnat : (1785605261 : ℕ)^19*100000000000000^15 ≤ 27137275260711^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1785605261 5000000000 27137275260711 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1965034267/5000000000 : ℝ)^19 ≤ (30636571113339/100000000000000 : ℝ)^15 := by
    have hnat : (1965034267 : ℕ)^19*100000000000000^15 ≤ 30636571113339^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965034267 5000000000 30636571113339 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5062982961/10000000000 : ℝ)^19 ≤ (21113076810757/50000000000000 : ℝ)^15 := by
    have hnat : (5062982961 : ℕ)^19*50000000000000^15 ≤ 21113076810757^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5062982961 10000000000 21113076810757 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1785605261/5000000000 : ℝ), (-1965034267/5000000000 : ℝ), (5062982961/10000000000 : ℝ)] ![(27137275260711/100000000000000 : ℝ), (30636571113339/100000000000000 : ℝ), (21113076810757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1785605261/5000000000 : ℝ)|^19 ≤ (27137275260711/100000000000000 : ℝ)^15
        have hw : |(1785605261/5000000000 : ℝ)|=(1785605261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1965034267/5000000000 : ℝ)|^19 ≤ (30636571113339/100000000000000 : ℝ)^15
        have hw : |(-1965034267/5000000000 : ℝ)|=(1965034267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5062982961/10000000000 : ℝ)|^19 ≤ (21113076810757/50000000000000 : ℝ)^15
        have hw : |(5062982961/10000000000 : ℝ)|=(5062982961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s0_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1347103001/5000000000 : ℝ)*x 0 + (-185682747/400000000 : ℝ)*x 1 + (2576494539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347103001/5000000000 : ℝ)^19 ≤ (759636231207/4000000000000 : ℝ)^15 := by
    have hnat : (1347103001 : ℕ)^19*4000000000000^15 ≤ 759636231207^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347103001 5000000000 759636231207 4000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (185682747/400000000 : ℝ)^19 ≤ (9457463041107/25000000000000 : ℝ)^15 := by
    have hnat : (185682747 : ℕ)^19*25000000000000^15 ≤ 9457463041107^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185682747 400000000 9457463041107 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2576494539/5000000000 : ℝ)^19 ≤ (43179242033193/100000000000000 : ℝ)^15 := by
    have hnat : (2576494539 : ℕ)^19*100000000000000^15 ≤ 43179242033193^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576494539 5000000000 43179242033193 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1347103001/5000000000 : ℝ), (-185682747/400000000 : ℝ), (2576494539/5000000000 : ℝ)] ![(759636231207/4000000000000 : ℝ), (9457463041107/25000000000000 : ℝ), (43179242033193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1347103001/5000000000 : ℝ)|^19 ≤ (759636231207/4000000000000 : ℝ)^15
        have hw : |(-1347103001/5000000000 : ℝ)|=(1347103001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-185682747/400000000 : ℝ)|^19 ≤ (9457463041107/25000000000000 : ℝ)^15
        have hw : |(-185682747/400000000 : ℝ)|=(185682747/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2576494539/5000000000 : ℝ)|^19 ≤ (43179242033193/100000000000000 : ℝ)^15
        have hw : |(2576494539/5000000000 : ℝ)|=(2576494539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s0_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (528563003/2000000000 : ℝ)*x 0 + (5202342071/10000000000 : ℝ)*x 1 + (4635593439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528563003/2000000000 : ℝ)^19 ≤ (18533235161427/100000000000000 : ℝ)^15 := by
    have hnat : (528563003 : ℕ)^19*100000000000000^15 ≤ 18533235161427^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528563003 2000000000 18533235161427 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5202342071/10000000000 : ℝ)^19 ≤ (43703740932869/100000000000000 : ℝ)^15 := by
    have hnat : (5202342071 : ℕ)^19*100000000000000^15 ≤ 43703740932869^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202342071 10000000000 43703740932869 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4635593439/10000000000 : ℝ)^19 ≤ (18881511947243/50000000000000 : ℝ)^15 := by
    have hnat : (4635593439 : ℕ)^19*50000000000000^15 ≤ 18881511947243^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4635593439 10000000000 18881511947243 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528563003/2000000000 : ℝ), (5202342071/10000000000 : ℝ), (4635593439/10000000000 : ℝ)] ![(18533235161427/100000000000000 : ℝ), (43703740932869/100000000000000 : ℝ), (18881511947243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528563003/2000000000 : ℝ)|^19 ≤ (18533235161427/100000000000000 : ℝ)^15
        have hw : |(528563003/2000000000 : ℝ)|=(528563003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5202342071/10000000000 : ℝ)|^19 ≤ (43703740932869/100000000000000 : ℝ)^15
        have hw : |(5202342071/10000000000 : ℝ)|=(5202342071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4635593439/10000000000 : ℝ)|^19 ≤ (18881511947243/50000000000000 : ℝ)^15
        have hw : |(4635593439/10000000000 : ℝ)|=(4635593439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s0_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7443737919/10000000000 : ℝ)*x 0 + (-2438384489/10000000000 : ℝ)*x 1 + (-2172744311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7443737919/10000000000 : ℝ)^19 ≤ (34401076371407/50000000000000 : ℝ)^15 := by
    have hnat : (7443737919 : ℕ)^19*50000000000000^15 ≤ 34401076371407^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7443737919 10000000000 34401076371407 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2438384489/10000000000 : ℝ)^19 ≤ (8368213937001/50000000000000 : ℝ)^15 := by
    have hnat : (2438384489 : ℕ)^19*50000000000000^15 ≤ 8368213937001^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2438384489 10000000000 8368213937001 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2172744311/10000000000 : ℝ)^19 ≤ (451919355329/3125000000000 : ℝ)^15 := by
    have hnat : (2172744311 : ℕ)^19*3125000000000^15 ≤ 451919355329^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2172744311 10000000000 451919355329 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7443737919/10000000000 : ℝ), (-2438384489/10000000000 : ℝ), (-2172744311/10000000000 : ℝ)] ![(34401076371407/50000000000000 : ℝ), (8368213937001/50000000000000 : ℝ), (451919355329/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7443737919/10000000000 : ℝ)|^19 ≤ (34401076371407/50000000000000 : ℝ)^15
        have hw : |(7443737919/10000000000 : ℝ)|=(7443737919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2438384489/10000000000 : ℝ)|^19 ≤ (8368213937001/50000000000000 : ℝ)^15
        have hw : |(-2438384489/10000000000 : ℝ)|=(2438384489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2172744311/10000000000 : ℝ)|^19 ≤ (451919355329/3125000000000 : ℝ)^15
        have hw : |(-2172744311/10000000000 : ℝ)|=(2172744311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s0_25 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1605550229/5000000000 : ℝ)*x 0 + (-4426830739/10000000000 : ℝ)*x 1 + (4914061391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1605550229/5000000000 : ℝ)^19 ≤ (23718921104159/100000000000000 : ℝ)^15 := by
    have hnat : (1605550229 : ℕ)^19*100000000000000^15 ≤ 23718921104159^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1605550229 5000000000 23718921104159 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4426830739/10000000000 : ℝ)^19 ≤ (3562195041537/10000000000000 : ℝ)^15 := by
    have hnat : (4426830739 : ℕ)^19*10000000000000^15 ≤ 3562195041537^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4426830739 10000000000 3562195041537 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4914061391/10000000000 : ℝ)^19 ≤ (8131825692377/20000000000000 : ℝ)^15 := by
    have hnat : (4914061391 : ℕ)^19*20000000000000^15 ≤ 8131825692377^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4914061391 10000000000 8131825692377 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1605550229/5000000000 : ℝ), (-4426830739/10000000000 : ℝ), (4914061391/10000000000 : ℝ)] ![(23718921104159/100000000000000 : ℝ), (3562195041537/10000000000000 : ℝ), (8131825692377/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1605550229/5000000000 : ℝ)|^19 ≤ (23718921104159/100000000000000 : ℝ)^15
        have hw : |(1605550229/5000000000 : ℝ)|=(1605550229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4426830739/10000000000 : ℝ)|^19 ≤ (3562195041537/10000000000000 : ℝ)^15
        have hw : |(-4426830739/10000000000 : ℝ)|=(4426830739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4914061391/10000000000 : ℝ)|^19 ≤ (8131825692377/20000000000000 : ℝ)^15
        have hw : |(4914061391/10000000000 : ℝ)|=(4914061391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s1_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3268382043/10000000000 : ℝ)*x 0 + (-1026760739/2500000000 : ℝ)*x 1 + (516901717/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3268382043/10000000000 : ℝ)^19 ≤ (24256133075901/100000000000000 : ℝ)^15 := by
    have hnat : (3268382043 : ℕ)^19*100000000000000^15 ≤ 24256133075901^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3268382043 10000000000 24256133075901 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026760739/2500000000 : ℝ)^19 ≤ (16197216290297/50000000000000 : ℝ)^15 := by
    have hnat : (1026760739 : ℕ)^19*50000000000000^15 ≤ 16197216290297^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026760739 2500000000 16197216290297 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516901717/1000000000 : ℝ)^19 ≤ (1083735858259/2500000000000 : ℝ)^15 := by
    have hnat : (516901717 : ℕ)^19*2500000000000^15 ≤ 1083735858259^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516901717 1000000000 1083735858259 2500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3268382043/10000000000 : ℝ), (-1026760739/2500000000 : ℝ), (516901717/1000000000 : ℝ)] ![(24256133075901/100000000000000 : ℝ), (16197216290297/50000000000000 : ℝ), (1083735858259/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3268382043/10000000000 : ℝ)|^19 ≤ (24256133075901/100000000000000 : ℝ)^15
        have hw : |(-3268382043/10000000000 : ℝ)|=(3268382043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1026760739/2500000000 : ℝ)|^19 ≤ (16197216290297/50000000000000 : ℝ)^15
        have hw : |(-1026760739/2500000000 : ℝ)|=(1026760739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516901717/1000000000 : ℝ)|^19 ≤ (1083735858259/2500000000000 : ℝ)^15
        have hw : |(516901717/1000000000 : ℝ)|=(516901717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3797530201/10000000000 : ℝ)*x 0 + (4794843059/10000000000 : ℝ)*x 1 + (3992312439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3797530201/10000000000 : ℝ)^19 ≤ (14666896831359/50000000000000 : ℝ)^15 := by
    have hnat : (3797530201 : ℕ)^19*50000000000000^15 ≤ 14666896831359^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3797530201 10000000000 14666896831359 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4794843059/10000000000 : ℝ)^19 ≤ (157654931637/400000000000 : ℝ)^15 := by
    have hnat : (4794843059 : ℕ)^19*400000000000^15 ≤ 157654931637^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794843059 10000000000 157654931637 400000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3992312439/10000000000 : ℝ)^19 ≤ (31252473414363/100000000000000 : ℝ)^15 := by
    have hnat : (3992312439 : ℕ)^19*100000000000000^15 ≤ 31252473414363^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3992312439 10000000000 31252473414363 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3797530201/10000000000 : ℝ), (4794843059/10000000000 : ℝ), (3992312439/10000000000 : ℝ)] ![(14666896831359/50000000000000 : ℝ), (157654931637/400000000000 : ℝ), (31252473414363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3797530201/10000000000 : ℝ)|^19 ≤ (14666896831359/50000000000000 : ℝ)^15
        have hw : |(3797530201/10000000000 : ℝ)|=(3797530201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4794843059/10000000000 : ℝ)|^19 ≤ (157654931637/400000000000 : ℝ)^15
        have hw : |(4794843059/10000000000 : ℝ)|=(4794843059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3992312439/10000000000 : ℝ)|^19 ≤ (31252473414363/100000000000000 : ℝ)^15
        have hw : |(3992312439/10000000000 : ℝ)|=(3992312439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (338083459/625000000 : ℝ)*x 0 + (-776426501/2000000000 : ℝ)*x 1 + (-1616182813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338083459/625000000 : ℝ)^19 ≤ (45917927775031/100000000000000 : ℝ)^15 := by
    have hnat : (338083459 : ℕ)^19*100000000000000^15 ≤ 45917927775031^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338083459 625000000 45917927775031 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (776426501/2000000000 : ℝ)^19 ≤ (15082006382047/50000000000000 : ℝ)^15 := by
    have hnat : (776426501 : ℕ)^19*50000000000000^15 ≤ 15082006382047^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776426501 2000000000 15082006382047 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1616182813/5000000000 : ℝ)^19 ≤ (23918059445803/100000000000000 : ℝ)^15 := by
    have hnat : (1616182813 : ℕ)^19*100000000000000^15 ≤ 23918059445803^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616182813 5000000000 23918059445803 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338083459/625000000 : ℝ), (-776426501/2000000000 : ℝ), (-1616182813/5000000000 : ℝ)] ![(45917927775031/100000000000000 : ℝ), (15082006382047/50000000000000 : ℝ), (23918059445803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338083459/625000000 : ℝ)|^19 ≤ (45917927775031/100000000000000 : ℝ)^15
        have hw : |(338083459/625000000 : ℝ)|=(338083459/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-776426501/2000000000 : ℝ)|^19 ≤ (15082006382047/50000000000000 : ℝ)^15
        have hw : |(-776426501/2000000000 : ℝ)|=(776426501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1616182813/5000000000 : ℝ)|^19 ≤ (23918059445803/100000000000000 : ℝ)^15
        have hw : |(-1616182813/5000000000 : ℝ)|=(1616182813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314041_s1_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (875560577/2000000000 : ℝ)*x 0 + (-3634394077/10000000000 : ℝ)*x 1 + (914830723/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875560577/2000000000 : ℝ)^19 ≤ (3512296659321/10000000000000 : ℝ)^15 := by
    have hnat : (875560577 : ℕ)^19*10000000000000^15 ≤ 3512296659321^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875560577 2000000000 3512296659321 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3634394077/10000000000 : ℝ)^19 ≤ (13873431408391/50000000000000 : ℝ)^15 := by
    have hnat : (3634394077 : ℕ)^19*50000000000000^15 ≤ 13873431408391^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3634394077 10000000000 13873431408391 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (914830723/2000000000 : ℝ)^19 ≤ (2320635660853/6250000000000 : ℝ)^15 := by
    have hnat : (914830723 : ℕ)^19*6250000000000^15 ≤ 2320635660853^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914830723 2000000000 2320635660853 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875560577/2000000000 : ℝ), (-3634394077/10000000000 : ℝ), (914830723/2000000000 : ℝ)] ![(3512296659321/10000000000000 : ℝ), (13873431408391/50000000000000 : ℝ), (2320635660853/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875560577/2000000000 : ℝ)|^19 ≤ (3512296659321/10000000000000 : ℝ)^15
        have hw : |(875560577/2000000000 : ℝ)|=(875560577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3634394077/10000000000 : ℝ)|^19 ≤ (13873431408391/50000000000000 : ℝ)^15
        have hw : |(-3634394077/10000000000 : ℝ)|=(3634394077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(914830723/2000000000 : ℝ)|^19 ≤ (2320635660853/6250000000000 : ℝ)^15
        have hw : |(914830723/2000000000 : ℝ)|=(914830723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314041 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have s0_pow0 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1064401010795949/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1064401010795949/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1329246449/5000000000 : ℝ)*X 0 0+(-4465182703/10000000000 : ℝ)*X 0 1+(2676548763/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((176825701/625000000 : ℝ)*X 1 0+(2620344021/5000000000 : ℝ)*X 1 1+(2216437389/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((876091133/2500000000 : ℝ)*X 0 0+(-4122525491/10000000000 : ℝ)*X 0 1+(617787739/1250000000 : ℝ)*X 0 2+(876091133/2500000000 : ℝ)*X 1 0+(-4122525491/10000000000 : ℝ)*X 1 1+(617787739/1250000000 : ℝ)*X 1 2+(876091133/2500000000 : ℝ)*X 2 0+(-4122525491/10000000000 : ℝ)*X 2 1+(617787739/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1333409871/5000000000 : ℝ)*X 0 0+(-4637876539/10000000000 : ℝ)*X 0 1+(5180052691/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((345697991/1250000000 : ℝ)*X 1 0+(5251541331/10000000000 : ℝ)*X 1 1+(4477738919/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((447730921/625000000 : ℝ)*X 2 0+(-539783567/2000000000 : ℝ)*X 2 1+(-1143242029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_10 : ((1999999983/2000000000 : ℝ)*X 1 0+(2961/10000000000 : ℝ)*X 1 1+(2961/10000000000 : ℝ)*X 1 2+(1999999983/2000000000 : ℝ)*X 2 0+(2961/10000000000 : ℝ)*X 2 1+(2961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s0_10 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3614666707/10000000000 : ℝ)*X 0 0+(-147235547/400000000 : ℝ)*X 0 1+(2626642109/5000000000 : ℝ)*X 0 2+(3614666707/10000000000 : ℝ)*X 1 0+(-147235547/400000000 : ℝ)*X 1 1+(2626642109/5000000000 : ℝ)*X 1 2+(3614666707/10000000000 : ℝ)*X 2 0+(-147235547/400000000 : ℝ)*X 2 1+(2626642109/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-2453778633/10000000000 : ℝ)*X 0 0+(-2180558841/5000000000 : ℝ)*X 0 1+(2809144971/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((338981959/1250000000 : ℝ)*X 1 0+(2703406711/5000000000 : ℝ)*X 1 1+(4361813919/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((746762591/1000000000 : ℝ)*X 2 0+(-316421269/1250000000 : ℝ)*X 2 1+(-510530173/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((1785605261/5000000000 : ℝ)*X 0 0+(-1965034267/5000000000 : ℝ)*X 0 1+(5062982961/10000000000 : ℝ)*X 0 2+(1785605261/5000000000 : ℝ)*X 1 0+(-1965034267/5000000000 : ℝ)*X 1 1+(5062982961/10000000000 : ℝ)*X 1 2+(1785605261/5000000000 : ℝ)*X 2 0+(-1965034267/5000000000 : ℝ)*X 2 1+(5062982961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-1347103001/5000000000 : ℝ)*X 0 0+(-185682747/400000000 : ℝ)*X 0 1+(2576494539/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((528563003/2000000000 : ℝ)*X 1 0+(5202342071/10000000000 : ℝ)*X 1 1+(4635593439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((7443737919/10000000000 : ℝ)*X 2 0+(-2438384489/10000000000 : ℝ)*X 2 1+(-2172744311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_25 : ((1605550229/5000000000 : ℝ)*X 0 0+(-4426830739/10000000000 : ℝ)*X 0 1+(4914061391/10000000000 : ℝ)*X 0 2+(1605550229/5000000000 : ℝ)*X 1 0+(-4426830739/10000000000 : ℝ)*X 1 1+(4914061391/10000000000 : ℝ)*X 1 2+(1605550229/5000000000 : ℝ)*X 2 0+(-4426830739/10000000000 : ℝ)*X 2 1+(4914061391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s0_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((1817/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1817/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (84530144322050586740739/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2192093459119/1000000000000 : ℝ)*(base40) + (874801966791/1000000000000 : ℝ)*(base50) + (8322633/1000000000000 : ℝ)*(base59) + (774944562931/250000000000 : ℝ)*(base60) + (13219698250331/1000000000000 : ℝ)*(major_s0_0) + (13219698250331/1000000000000 : ℝ)*(major_s0_1) + (13219698250331/1000000000000 : ℝ)*(major_s0_2) + (9378300919311/500000000000 : ℝ)*(sp_s0_7) + (1875510358969/100000000000 : ℝ)*(sp_s0_8) + (9378300919311/500000000000 : ℝ)*(sp_s0_9) + (7682593774083/1000000000000 : ℝ)*(sp_s0_13) + (120207553/250000000000 : ℝ)*(sp_s0_15) + (39050521/200000000000 : ℝ)*(sp_s0_19) + (1017418719/1000000000000 : ℝ)*(sp_s0_21) + (7682789026687/1000000000000 : ℝ)*(f.failure) + (9378300919311/500000000000 : ℝ)*(f.sum) + (75788967/10000000000000000000000 : ℝ)*base62 + (6198293390290881/10000000000000000000000000000 : ℝ)*base65 + (7171180338290881/10000000000000000000000000000 : ℝ)*base66 + (90539145606853/400000000000000000000000000 : ℝ)*base68 + (4405838904731103/5000000000000000000000000000 : ℝ)*base71 + (858000884709119/10000000000000000000000000000 : ℝ)*base73 + (3730988113147/400000000000000000000000000 : ℝ)*base74 + (95837921806853/400000000000000000000000000 : ℝ)*base77 + (2642911748790881/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (94597/100000000000000000 : ℝ)*base86 + (94597/100000000000000000 : ℝ)*base88 + (94597/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-7341/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-7341/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9406803454442928200091/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (72937545577/31250000000 : ℝ)*(base40) + (83318843097/500000000000 : ℝ)*(base50) + (1361499798311/500000000000 : ℝ)*(base60) + (12892184513223/1000000000000 : ℝ)*(major_s0_0) + (2767236445201/250000000000 : ℝ)*(major_s0_1) + (2767236445201/250000000000 : ℝ)*(major_s0_2) + (1726333/40000000000 : ℝ)*(sp_s0_0) + (38242097/500000000000 : ℝ)*(sp_s0_1) + (1823238732419/1000000000000 : ℝ)*(sp_s0_10) + (58755243/1000000000000 : ℝ)*(sp_s0_13) + (7852497088397/500000000000 : ℝ)*(sp_s0_14) + (3926240212731/250000000000 : ℝ)*(sp_s0_15) + (15705037335119/1000000000000 : ℝ)*(sp_s0_16) + (3216397108499/500000000000 : ℝ)*(sp_s0_19) + (80410662153/12500000000 : ℝ)*(f.failure) + (15705037335119/1000000000000 : ℝ)*(f.sum) + (460214139/2000000000000000000000 : ℝ)*base63 + (1464675153709251/2500000000000000000000000000 : ℝ)*base65 + (2684624656209251/2500000000000000000000000000 : ℝ)*base66 + (16768564943663/100000000000000000000000000 : ℝ)*base68 + (6143488559863229/10000000000000000000000000000 : ℝ)*base71 + (3318462453666373/10000000000000000000000000000 : ℝ)*base72 + (49286219116337/100000000000000000000000000 : ℝ)*base74 + (266244161961049/400000000000000000000000000 : ℝ)*base77 + (6052272692503377/10000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (443/1250000000000000 : ℝ)*base86 + (443/1250000000000000 : ℝ)*base88 + (443/1250000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(5017/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(5017/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6494088351656420140707/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2163598538603/1000000000000 : ℝ)*(base40) + (235173708057/250000000000 : ℝ)*(base50) + (221061283639/100000000000 : ℝ)*(base60) + (15089310876681/1000000000000 : ℝ)*(major_s0_0) + (11602111557129/1000000000000 : ℝ)*(major_s0_1) + (11602111557129/1000000000000 : ℝ)*(major_s0_2) + (21943773/1000000000000 : ℝ)*(sp_s0_1) + (12992619/1000000000000 : ℝ)*(sp_s0_6) + (956376949/1000000000000 : ℝ)*(sp_s0_8) + (6810936171/1953125000 : ℝ)*(sp_s0_10) + (4115377503181/250000000000 : ℝ)*(sp_s0_20) + (8230265846001/500000000000 : ℝ)*(sp_s0_21) + (4115377503181/250000000000 : ℝ)*(sp_s0_22) + (6742695779519/1000000000000 : ℝ)*(sp_s0_25) + (3371354386069/500000000000 : ℝ)*(f.failure) + (4115377503181/250000000000 : ℝ)*(f.sum) + (1383930219/5000000000000000000000 : ℝ)*base63 + (2760614094729579/10000000000000000000000000000 : ℝ)*base65 + (7635674853729579/10000000000000000000000000000 : ℝ)*base66 + (64561656823127/400000000000000000000000000 : ℝ)*base68 + (2267476661298923/5000000000000000000000000000 : ℝ)*base70 + (1991091538634731/10000000000000000000000000000 : ℝ)*base72 + (126783111416873/400000000000000000000000000 : ℝ)*base74 + (23765380626903/400000000000000000000000000 : ℝ)*base77 + (123547589636431/1000000000000000000000000000 : ℝ)*base78 + (56761/50000000000000000 : ℝ)*base87 + (56761/50000000000000000 : ℝ)*base89 + (56761/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (1817/100000 : ℝ) ^ (37/8 : ℝ) ≤ (111282417527/12500000000000000000 : ℝ) := by
    have hpowers : (1817/100000 : ℝ)^37 ≤ (111282417527/12500000000000000000 : ℝ)^8 := by
      have hnat : (1817 : ℕ)^37*12500000000000000000^8 ≤ 111282417527^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1817 100000 111282417527 12500000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1817/100000 : ℝ)) (X := (111282417527/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (12500000111282417527/12500000000000000000 : ℝ) ≤ (10000000019248851/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (12500000111282417527/12500000000000000000 : ℝ)^8 ≤ (10000000019248851/10000000000000000 : ℝ)^37 := by
      have hnat : (12500000111282417527 : ℕ)^8*10000000000000000^37 ≤ 10000000019248851^37*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000111282417527 12500000000000000000 10000000019248851 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000019248851/10000000000000000 : ℝ)) (X := (12500000111282417527/12500000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (6250000111282417527/6250000000000000000 : ℝ) ≤ (10000000038497701/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (6250000111282417527/6250000000000000000 : ℝ)^8 ≤ (10000000038497701/10000000000000000 : ℝ)^37 := by
      have hnat : (6250000111282417527 : ℕ)^8*10000000000000000^37 ≤ 10000000038497701^37*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250000111282417527 6250000000000000000 10000000038497701 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000038497701/10000000000000000 : ℝ)) (X := (6250000111282417527/6250000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(19248851/181700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(384977/3634000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1817/100000 : ℝ)) (alpha := (19248851/181700000000000 : ℝ)) (beta := (384977/3634000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1817/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(19248851/181700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(384977/3634000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (7341/50000 : ℝ) ^ (37/8 : ℝ) ≤ (14008177666012237/100000000000000000000 : ℝ) := by
    have hpowers : (7341/50000 : ℝ)^37 ≤ (14008177666012237/100000000000000000000 : ℝ)^8 := by
      have hnat : (7341 : ℕ)^37*100000000000000000000^8 ≤ 14008177666012237^8*50000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7341 50000 14008177666012237 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7341/50000 : ℝ)) (X := (14008177666012237/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100014008177666012237/100000000000000000000 : ℝ) ≤ (5000151431445669/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (100014008177666012237/100000000000000000000 : ℝ)^8 ≤ (5000151431445669/5000000000000000 : ℝ)^37 := by
      have hnat : (100014008177666012237 : ℕ)^8*5000000000000000^37 ≤ 5000151431445669^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100014008177666012237 100000000000000000000 5000151431445669 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000151431445669/5000000000000000 : ℝ)) (X := (100014008177666012237/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50014008177666012237/50000000000000000000 : ℝ) ≤ (5000302846268341/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (50014008177666012237/50000000000000000000 : ℝ)^8 ≤ (5000302846268341/5000000000000000 : ℝ)^37 := by
      have hnat : (50014008177666012237 : ℕ)^8*5000000000000000^37 ≤ 5000302846268341^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014008177666012237 50000000000000000000 5000302846268341 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000302846268341/5000000000000000 : ℝ)) (X := (50014008177666012237/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(151431445669/734100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(9463426417/45881250000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (7341/50000 : ℝ)) (alpha := (151431445669/734100000000000 : ℝ)) (beta := (9463426417/45881250000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (7341/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(151431445669/734100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(9463426417/45881250000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (5017/50000 : ℝ) ^ (37/8 : ℝ) ≤ (2408894040489043/100000000000000000000 : ℝ) := by
    have hpowers : (5017/50000 : ℝ)^37 ≤ (2408894040489043/100000000000000000000 : ℝ)^8 := by
      have hnat : (5017 : ℕ)^37*100000000000000000000^8 ≤ 2408894040489043^8*50000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5017 50000 2408894040489043 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5017/50000 : ℝ)) (X := (2408894040489043/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100002408894040489043/100000000000000000000 : ℝ) ≤ (10000052083703789/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (100002408894040489043/100000000000000000000 : ℝ)^8 ≤ (10000052083703789/10000000000000000 : ℝ)^37 := by
      have hnat : (100002408894040489043 : ℕ)^8*10000000000000000^37 ≤ 10000052083703789^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100002408894040489043 100000000000000000000 10000052083703789 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000052083703789/10000000000000000 : ℝ)) (X := (100002408894040489043/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50002408894040489043/50000000000000000000 : ℝ) ≤ (10000104166424243/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (50002408894040489043/50000000000000000000 : ℝ)^8 ≤ (10000104166424243/10000000000000000 : ℝ)^37 := by
      have hnat : (50002408894040489043 : ℕ)^8*10000000000000000^37 ≤ 10000104166424243^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002408894040489043 50000000000000000000 10000104166424243 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000104166424243/10000000000000000 : ℝ)) (X := (50002408894040489043/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(52083703789/1003400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(26041360227/501700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (5017/50000 : ℝ)) (alpha := (52083703789/1003400000000000 : ℝ)) (beta := (26041360227/501700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (5017/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(52083703789/1003400000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(26041360227/501700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3268382043/10000000000 : ℝ)*X 0 0+(-1026760739/2500000000 : ℝ)*X 0 1+(516901717/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((3797530201/10000000000 : ℝ)*X 1 0+(4794843059/10000000000 : ℝ)*X 1 1+(3992312439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((338083459/625000000 : ℝ)*X 2 0+(-776426501/2000000000 : ℝ)*X 2 1+(-1616182813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((875560577/2000000000 : ℝ)*X 0 0+(-3634394077/10000000000 : ℝ)*X 0 1+(914830723/2000000000 : ℝ)*X 0 2+(875560577/2000000000 : ℝ)*X 1 0+(-3634394077/10000000000 : ℝ)*X 1 1+(914830723/2000000000 : ℝ)*X 1 2+(875560577/2000000000 : ℝ)*X 2 0+(-3634394077/10000000000 : ℝ)*X 2 1+(914830723/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314041_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-366207/50000 : ℝ) < ((-172069/100000 : ℝ)*P 0+(-172069/100000 : ℝ)*P 1+(-172069/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-366207/50000 : ℝ) < (-1611191333805762192654732617753821/223065803830000000000000000000000 : ℝ) := by norm_num
    linear_combination (1521/25000000000 : ℝ)*(base13) + (235481/1000000000000 : ℝ)*(base15) + (12227/250000000000 : ℝ)*(base19) + (120502966543/1000000000000 : ℝ)*(base39) + (84513965953/200000000000 : ℝ)*(base40) + (19112499333/1000000000000 : ℝ)*(base50) + (90509/1000000000000 : ℝ)*(base59) + (92127234581/250000000000 : ℝ)*(base60) + (172069/100000 : ℝ)*(major_s1_0) + (172069/100000 : ℝ)*(major_s1_1) + (172069/100000 : ℝ)*(major_s1_2) + (1203823614247/500000000000 : ℝ)*(sp_s1_0) + (481529400989/200000000000 : ℝ)*(sp_s1_1) + (1203823644667/500000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (1203823644667/500000000000 : ℝ)*(f.sum) + (67167870089944063/184148985000000000000000000000 : ℝ)*base62 + (762845815061/6271250000000000000000000 : ℝ)*base65 + (1341023368759/3670500000000000000000000 : ℝ)*base66 + (6658623114413/10034000000000000000000000 : ℝ)*base68 + (10929265167457961/18231778000000000000000000000 : ℝ)*base71 + (2346615144707/3634000000000000000000000 : ℝ)*base72 + (356316524923/2294062500000000000000000 : ℝ)*base74 + (966012243439/1817000000000000000000000 : ℝ)*base77 + (11323201373464213/33346492500000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c314042_s0_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2982197687/10000000000 : ℝ)*x 0 + (-596800237/1250000000 : ℝ)*x 1 + (-477440153/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2982197687/10000000000 : ℝ)^19 ≤ (21597963858877/100000000000000 : ℝ)^15 := by
    have hnat : (2982197687 : ℕ)^19*100000000000000^15 ≤ 21597963858877^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2982197687 10000000000 21597963858877 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (596800237/1250000000 : ℝ)^19 ≤ (39201019961691/100000000000000 : ℝ)^15 := by
    have hnat : (596800237 : ℕ)^19*100000000000000^15 ≤ 39201019961691^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596800237 1250000000 39201019961691 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (477440153/1000000000 : ℝ)^19 ≤ (19600508077613/50000000000000 : ℝ)^15 := by
    have hnat : (477440153 : ℕ)^19*50000000000000^15 ≤ 19600508077613^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477440153 1000000000 19600508077613 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2982197687/10000000000 : ℝ), (-596800237/1250000000 : ℝ), (-477440153/1000000000 : ℝ)] ![(21597963858877/100000000000000 : ℝ), (39201019961691/100000000000000 : ℝ), (19600508077613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2982197687/10000000000 : ℝ)|^19 ≤ (21597963858877/100000000000000 : ℝ)^15
        have hw : |(-2982197687/10000000000 : ℝ)|=(2982197687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-596800237/1250000000 : ℝ)|^19 ≤ (39201019961691/100000000000000 : ℝ)^15
        have hw : |(-596800237/1250000000 : ℝ)|=(596800237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-477440153/1000000000 : ℝ)|^19 ≤ (19600508077613/50000000000000 : ℝ)^15
        have hw : |(-477440153/1000000000 : ℝ)|=(477440153/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314042_s0_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2982197687/10000000000 : ℝ)*x 0 + (596800237/1250000000 : ℝ)*x 1 + (-477440153/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2982197687/10000000000 : ℝ)^19 ≤ (21597963858877/100000000000000 : ℝ)^15 := by
    have hnat : (2982197687 : ℕ)^19*100000000000000^15 ≤ 21597963858877^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2982197687 10000000000 21597963858877 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (596800237/1250000000 : ℝ)^19 ≤ (39201019961691/100000000000000 : ℝ)^15 := by
    have hnat : (596800237 : ℕ)^19*100000000000000^15 ≤ 39201019961691^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596800237 1250000000 39201019961691 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (477440153/1000000000 : ℝ)^19 ≤ (19600508077613/50000000000000 : ℝ)^15 := by
    have hnat : (477440153 : ℕ)^19*50000000000000^15 ≤ 19600508077613^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477440153 1000000000 19600508077613 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2982197687/10000000000 : ℝ), (596800237/1250000000 : ℝ), (-477440153/1000000000 : ℝ)] ![(21597963858877/100000000000000 : ℝ), (39201019961691/100000000000000 : ℝ), (19600508077613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2982197687/10000000000 : ℝ)|^19 ≤ (21597963858877/100000000000000 : ℝ)^15
        have hw : |(2982197687/10000000000 : ℝ)|=(2982197687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(596800237/1250000000 : ℝ)|^19 ≤ (39201019961691/100000000000000 : ℝ)^15
        have hw : |(596800237/1250000000 : ℝ)|=(596800237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-477440153/1000000000 : ℝ)|^19 ≤ (19600508077613/50000000000000 : ℝ)^15
        have hw : |(-477440153/1000000000 : ℝ)|=(477440153/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314042_s0_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5847304089/10000000000 : ℝ)*x 0 + (-3311430937/10000000000 : ℝ)*x 1 + (3311430683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5847304089/10000000000 : ℝ)^19 ≤ (12669239220047/25000000000000 : ℝ)^15 := by
    have hnat : (5847304089 : ℕ)^19*25000000000000^15 ≤ 12669239220047^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5847304089 10000000000 12669239220047 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3311430937/10000000000 : ℝ)^19 ≤ (24661522749581/100000000000000 : ℝ)^15 := by
    have hnat : (3311430937 : ℕ)^19*100000000000000^15 ≤ 24661522749581^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3311430937 10000000000 24661522749581 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3311430683/10000000000 : ℝ)^19 ≤ (24661520353507/100000000000000 : ℝ)^15 := by
    have hnat : (3311430683 : ℕ)^19*100000000000000^15 ≤ 24661520353507^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3311430683 10000000000 24661520353507 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5847304089/10000000000 : ℝ), (-3311430937/10000000000 : ℝ), (3311430683/10000000000 : ℝ)] ![(12669239220047/25000000000000 : ℝ), (24661522749581/100000000000000 : ℝ), (24661520353507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5847304089/10000000000 : ℝ)|^19 ≤ (12669239220047/25000000000000 : ℝ)^15
        have hw : |(5847304089/10000000000 : ℝ)|=(5847304089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3311430937/10000000000 : ℝ)|^19 ≤ (24661522749581/100000000000000 : ℝ)^15
        have hw : |(-3311430937/10000000000 : ℝ)|=(3311430937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3311430683/10000000000 : ℝ)|^19 ≤ (24661520353507/100000000000000 : ℝ)^15
        have hw : |(3311430683/10000000000 : ℝ)|=(3311430683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314042_s0_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5847304089/10000000000 : ℝ)*x 0 + (-3311430937/10000000000 : ℝ)*x 1 + (-3311430683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5847304089/10000000000 : ℝ)^19 ≤ (12669239220047/25000000000000 : ℝ)^15 := by
    have hnat : (5847304089 : ℕ)^19*25000000000000^15 ≤ 12669239220047^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5847304089 10000000000 12669239220047 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3311430937/10000000000 : ℝ)^19 ≤ (24661522749581/100000000000000 : ℝ)^15 := by
    have hnat : (3311430937 : ℕ)^19*100000000000000^15 ≤ 24661522749581^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3311430937 10000000000 24661522749581 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3311430683/10000000000 : ℝ)^19 ≤ (24661520353507/100000000000000 : ℝ)^15 := by
    have hnat : (3311430683 : ℕ)^19*100000000000000^15 ≤ 24661520353507^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3311430683 10000000000 24661520353507 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5847304089/10000000000 : ℝ), (-3311430937/10000000000 : ℝ), (-3311430683/10000000000 : ℝ)] ![(12669239220047/25000000000000 : ℝ), (24661522749581/100000000000000 : ℝ), (24661520353507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5847304089/10000000000 : ℝ)|^19 ≤ (12669239220047/25000000000000 : ℝ)^15
        have hw : |(5847304089/10000000000 : ℝ)|=(5847304089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3311430937/10000000000 : ℝ)|^19 ≤ (24661522749581/100000000000000 : ℝ)^15
        have hw : |(-3311430937/10000000000 : ℝ)|=(3311430937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3311430683/10000000000 : ℝ)|^19 ≤ (24661520353507/100000000000000 : ℝ)^15
        have hw : |(-3311430683/10000000000 : ℝ)|=(3311430683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314042 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have s0_pow0 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (37/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^37 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^37*1^8 ≤ 1^8*1^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (464673127956063/400000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (464673127956063/400000000000000 : ℝ)^37 := by
      have hnat : (2 : ℕ)^8*400000000000000^37 ≤ 464673127956063^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 464673127956063 400000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (464673127956063/400000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3170307302424381/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (3170307302424381/2500000000000000 : ℝ)^37 := by
      have hnat : (3 : ℕ)^8*2500000000000000^37 ≤ 3170307302424381^37*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3170307302424381 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3170307302424381/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2982197687/10000000000 : ℝ)*X 0 0+(-596800237/1250000000 : ℝ)*X 0 1+(-477440153/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314042_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2982197687/10000000000 : ℝ)*X 1 0+(596800237/1250000000 : ℝ)*X 1 1+(-477440153/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314042_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5847304089/10000000000 : ℝ)*X 2 0+(-3311430937/10000000000 : ℝ)*X 2 1+(3311430683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314042_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((5847304089/10000000000 : ℝ)*X 0 0+(-3311430937/10000000000 : ℝ)*X 0 1+(-3311430683/10000000000 : ℝ)*X 0 2+(5847304089/10000000000 : ℝ)*X 1 0+(-3311430937/10000000000 : ℝ)*X 1 1+(-3311430683/10000000000 : ℝ)*X 1 2+(5847304089/10000000000 : ℝ)*X 2 0+(-3311430937/10000000000 : ℝ)*X 2 1+(-3311430683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314042_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-366207/50000 : ℝ) < ((-172069/100000 : ℝ)*P 0+(-172069/100000 : ℝ)*P 1+(-172069/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-366207/50000 : ℝ) < (-4534671938409619936007939841/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (181092767971/500000000000 : ℝ)*(base39) + (310474107969/1000000000000 : ℝ)*(base40) + (51711418323/1000000000000 : ℝ)*(base49) + (25327/250000000000 : ℝ)*(base53) + (881/62500000000 : ℝ)*(base54) + (23527883313/125000000000 : ℝ)*(base59) + (136511616123/1000000000000 : ℝ)*(base60) + (172069/100000 : ℝ)*(major_s0_0) + (107543126033/62500000000 : ℝ)*(major_s0_1) + (430172471149/250000000000 : ℝ)*(major_s0_2) + (604622891529/250000000000 : ℝ)*(sp_s0_0) + (604622887397/250000000000 : ℝ)*(sp_s0_1) + (2418491653327/1000000000000 : ℝ)*(sp_s0_2) + (62499999119/62500000000 : ℝ)*(sp_s0_6) + (483698330179/200000000000 : ℝ)*(f.sum) + (51191497185929/100000000000000000000000000 : ℝ)*base63 + (1664125724575401/2500000000000000000000000000 : ℝ)*base65 + (456315072340317/625000000000000000000000000 : ℝ)*base67 + (37094148753613/100000000000000000000000000 : ℝ)*base69 + (1860653716075401/2500000000000000000000000000 : ℝ)*base71 + (1786323441/5000000000000000000000 : ℝ)*base73 + (7871106590579/25000000000000000000000000 : ℝ)*base75 + (3327376197/10000000000000000000000 : ℝ)*base77 + (64321009152817/625000000000000000000000000 : ℝ)*base79 + (16529/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1033/62500000000 : ℝ)*base85 + (1033/62500000000 : ℝ)*base88 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p014_b021 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (c : Fin 88) (hlo : 41 ≤ c.val) (hhi : c.val < 43)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=41 ∨ c=42 := by omega
  rcases hc with rfl|rfl
  · exact collision_c314041 p hpa (by linarith only [hpb]) X hX
  · exact collision_c314042 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (c : Fin 88) (hlo : 41 ≤ c.val) (hhi : c.val < 43)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p014_b021 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

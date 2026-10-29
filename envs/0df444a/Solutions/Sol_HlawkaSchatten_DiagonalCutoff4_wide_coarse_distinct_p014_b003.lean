-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p014_b003
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:50:05.465916+00:00
-- url     : https://prove2.me/submissions/771b80b4-7fc1-480a-ac2b-af0bebfb2f3a

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
theorem collision_support_c314007_s0_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-473821227/2000000000 : ℝ)*x 0 + (-3205760027/5000000000 : ℝ)*x 1 + (443510499/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (473821227/2000000000 : ℝ)^19 ≤ (20170518783/125000000000 : ℝ)^15 := by
    have hnat : (473821227 : ℕ)^19*125000000000^15 ≤ 20170518783^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473821227 2000000000 20170518783 125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3205760027/5000000000 : ℝ)^19 ≤ (7118589549167/12500000000000 : ℝ)^15 := by
    have hnat : (3205760027 : ℕ)^19*12500000000000^15 ≤ 7118589549167^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3205760027 5000000000 7118589549167 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (443510499/1250000000 : ℝ)^19 ≤ (26914868565343/100000000000000 : ℝ)^15 := by
    have hnat : (443510499 : ℕ)^19*100000000000000^15 ≤ 26914868565343^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443510499 1250000000 26914868565343 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-473821227/2000000000 : ℝ), (-3205760027/5000000000 : ℝ), (443510499/1250000000 : ℝ)] ![(20170518783/125000000000 : ℝ), (7118589549167/12500000000000 : ℝ), (26914868565343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-473821227/2000000000 : ℝ)|^19 ≤ (20170518783/125000000000 : ℝ)^15
        have hw : |(-473821227/2000000000 : ℝ)|=(473821227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3205760027/5000000000 : ℝ)|^19 ≤ (7118589549167/12500000000000 : ℝ)^15
        have hw : |(-3205760027/5000000000 : ℝ)|=(3205760027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(443510499/1250000000 : ℝ)|^19 ≤ (26914868565343/100000000000000 : ℝ)^15
        have hw : |(443510499/1250000000 : ℝ)|=(443510499/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314007_s0_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (57181517/100000000 : ℝ)*x 0 + (387671649/1250000000 : ℝ)*x 1 + (3664638399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (57181517/100000000 : ℝ)^19 ≤ (9852667978271/20000000000000 : ℝ)^15 := by
    have hnat : (57181517 : ℕ)^19*20000000000000^15 ≤ 9852667978271^15*100000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57181517 100000000 9852667978271 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (387671649/1250000000 : ℝ)^19 ≤ (22696998877797/100000000000000 : ℝ)^15 := by
    have hnat : (387671649 : ℕ)^19*100000000000000^15 ≤ 22696998877797^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387671649 1250000000 22696998877797 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3664638399/10000000000 : ℝ)^19 ≤ (7009915304131/25000000000000 : ℝ)^15 := by
    have hnat : (3664638399 : ℕ)^19*25000000000000^15 ≤ 7009915304131^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3664638399 10000000000 7009915304131 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(57181517/100000000 : ℝ), (387671649/1250000000 : ℝ), (3664638399/10000000000 : ℝ)] ![(9852667978271/20000000000000 : ℝ), (22696998877797/100000000000000 : ℝ), (7009915304131/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(57181517/100000000 : ℝ)|^19 ≤ (9852667978271/20000000000000 : ℝ)^15
        have hw : |(57181517/100000000 : ℝ)|=(57181517/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(387671649/1250000000 : ℝ)|^19 ≤ (22696998877797/100000000000000 : ℝ)^15
        have hw : |(387671649/1250000000 : ℝ)|=(387671649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3664638399/10000000000 : ℝ)|^19 ≤ (7009915304131/25000000000000 : ℝ)^15
        have hw : |(3664638399/10000000000 : ℝ)|=(3664638399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314007_s0_4 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (-1 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^19 ≤ (0 : ℝ)^15 := by
    have hnat : (0 : ℕ)^19*1^15 ≤ 0^15*1^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1 : ℝ)^19 ≤ (1 : ℝ)^15 := by
    have hnat : (1 : ℕ)^19*1^15 ≤ 1^15*1^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^19 ≤ (0 : ℝ)^15 := by
    have hnat : (0 : ℕ)^19*1^15 ≤ 0^15*1^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (-1 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^19 ≤ (0 : ℝ)^15
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1 : ℝ)|^19 ≤ (1 : ℝ)^15
        have hw : |(-1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^19 ≤ (0 : ℝ)^15
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314007_s0_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1782988247/10000000000 : ℝ)*x 0 + (-1489573597/2000000000 : ℝ)*x 1 + (279459711/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1782988247/10000000000 : ℝ)^19 ≤ (2814457860373/25000000000000 : ℝ)^15 := by
    have hnat : (1782988247 : ℕ)^19*25000000000000^15 ≤ 2814457860373^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1782988247 10000000000 2814457860373 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1489573597/2000000000 : ℝ)^19 ≤ (68850510083501/100000000000000 : ℝ)^15 := by
    have hnat : (1489573597 : ℕ)^19*100000000000000^15 ≤ 68850510083501^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1489573597 2000000000 68850510083501 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279459711/1000000000 : ℝ)^19 ≤ (310807163419/1562500000000 : ℝ)^15 := by
    have hnat : (279459711 : ℕ)^19*1562500000000^15 ≤ 310807163419^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279459711 1000000000 310807163419 1562500000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1782988247/10000000000 : ℝ), (-1489573597/2000000000 : ℝ), (279459711/1000000000 : ℝ)] ![(2814457860373/25000000000000 : ℝ), (68850510083501/100000000000000 : ℝ), (310807163419/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1782988247/10000000000 : ℝ)|^19 ≤ (2814457860373/25000000000000 : ℝ)^15
        have hw : |(-1782988247/10000000000 : ℝ)|=(1782988247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1489573597/2000000000 : ℝ)|^19 ≤ (68850510083501/100000000000000 : ℝ)^15
        have hw : |(-1489573597/2000000000 : ℝ)|=(1489573597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(279459711/1000000000 : ℝ)|^19 ≤ (310807163419/1562500000000 : ℝ)^15
        have hw : |(279459711/1000000000 : ℝ)|=(279459711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314007_s0_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1143514139/2500000000 : ℝ)*x 0 + (442943247/1250000000 : ℝ)*x 1 + (4463836369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1143514139/2500000000 : ℝ)^19 ≤ (37129172613671/100000000000000 : ℝ)^15 := by
    have hnat : (1143514139 : ℕ)^19*100000000000000^15 ≤ 37129172613671^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143514139 2500000000 37129172613671 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442943247/1250000000 : ℝ)^19 ≤ (26871271962983/100000000000000 : ℝ)^15 := by
    have hnat : (442943247 : ℕ)^19*100000000000000^15 ≤ 26871271962983^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442943247 1250000000 26871271962983 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4463836369/10000000000 : ℝ)^19 ≤ (35999555406873/100000000000000 : ℝ)^15 := by
    have hnat : (4463836369 : ℕ)^19*100000000000000^15 ≤ 35999555406873^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4463836369 10000000000 35999555406873 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1143514139/2500000000 : ℝ), (442943247/1250000000 : ℝ), (4463836369/10000000000 : ℝ)] ![(37129172613671/100000000000000 : ℝ), (26871271962983/100000000000000 : ℝ), (35999555406873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1143514139/2500000000 : ℝ)|^19 ≤ (37129172613671/100000000000000 : ℝ)^15
        have hw : |(1143514139/2500000000 : ℝ)|=(1143514139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(442943247/1250000000 : ℝ)|^19 ≤ (26871271962983/100000000000000 : ℝ)^15
        have hw : |(442943247/1250000000 : ℝ)|=(442943247/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4463836369/10000000000 : ℝ)|^19 ≤ (35999555406873/100000000000000 : ℝ)^15
        have hw : |(4463836369/10000000000 : ℝ)|=(4463836369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314007_s0_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1868688663/5000000000 : ℝ)*x 0 + (-2857539333/10000000000 : ℝ)*x 1 + (-5857842243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1868688663/5000000000 : ℝ)^19 ≤ (7186622082597/25000000000000 : ℝ)^15 := by
    have hnat : (1868688663 : ℕ)^19*25000000000000^15 ≤ 7186622082597^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868688663 5000000000 7186622082597 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2857539333/10000000000 : ℝ)^19 ≤ (4092168147033/20000000000000 : ℝ)^15 := by
    have hnat : (2857539333 : ℕ)^19*20000000000000^15 ≤ 4092168147033^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2857539333 10000000000 4092168147033 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5857842243/10000000000 : ℝ)^19 ≤ (25396335456777/50000000000000 : ℝ)^15 := by
    have hnat : (5857842243 : ℕ)^19*50000000000000^15 ≤ 25396335456777^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5857842243 10000000000 25396335456777 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1868688663/5000000000 : ℝ), (-2857539333/10000000000 : ℝ), (-5857842243/10000000000 : ℝ)] ![(7186622082597/25000000000000 : ℝ), (4092168147033/20000000000000 : ℝ), (25396335456777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1868688663/5000000000 : ℝ)|^19 ≤ (7186622082597/25000000000000 : ℝ)^15
        have hw : |(1868688663/5000000000 : ℝ)|=(1868688663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2857539333/10000000000 : ℝ)|^19 ≤ (4092168147033/20000000000000 : ℝ)^15
        have hw : |(-2857539333/10000000000 : ℝ)|=(2857539333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5857842243/10000000000 : ℝ)|^19 ≤ (25396335456777/50000000000000 : ℝ)^15
        have hw : |(-5857842243/10000000000 : ℝ)|=(5857842243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314007_s0_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-730631833/2500000000 : ℝ)*x 0 + (-6315897949/10000000000 : ℝ)*x 1 + (3141856261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (730631833/2500000000 : ℝ)^19 ≤ (21052040806843/100000000000000 : ℝ)^15 := by
    have hnat : (730631833 : ℕ)^19*100000000000000^15 ≤ 21052040806843^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730631833 2500000000 21052040806843 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6315897949/10000000000 : ℝ)^19 ≤ (27937516883067/50000000000000 : ℝ)^15 := by
    have hnat : (6315897949 : ℕ)^19*50000000000000^15 ≤ 27937516883067^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6315897949 10000000000 27937516883067 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3141856261/10000000000 : ℝ)^19 ≤ (11536462709551/50000000000000 : ℝ)^15 := by
    have hnat : (3141856261 : ℕ)^19*50000000000000^15 ≤ 11536462709551^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3141856261 10000000000 11536462709551 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-730631833/2500000000 : ℝ), (-6315897949/10000000000 : ℝ), (3141856261/10000000000 : ℝ)] ![(21052040806843/100000000000000 : ℝ), (27937516883067/50000000000000 : ℝ), (11536462709551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-730631833/2500000000 : ℝ)|^19 ≤ (21052040806843/100000000000000 : ℝ)^15
        have hw : |(-730631833/2500000000 : ℝ)|=(730631833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6315897949/10000000000 : ℝ)|^19 ≤ (27937516883067/50000000000000 : ℝ)^15
        have hw : |(-6315897949/10000000000 : ℝ)|=(6315897949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3141856261/10000000000 : ℝ)|^19 ≤ (11536462709551/50000000000000 : ℝ)^15
        have hw : |(3141856261/10000000000 : ℝ)|=(3141856261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314007_s0_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2858528871/5000000000 : ℝ)*x 0 + (3048259953/10000000000 : ℝ)*x 1 + (1858228831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2858528871/5000000000 : ℝ)^19 ≤ (12312850551753/25000000000000 : ℝ)^15 := by
    have hnat : (2858528871 : ℕ)^19*25000000000000^15 ≤ 12312850551753^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2858528871 5000000000 12312850551753 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3048259953/10000000000 : ℝ)^19 ≤ (22205771538371/100000000000000 : ℝ)^15 := by
    have hnat : (3048259953 : ℕ)^19*100000000000000^15 ≤ 22205771538371^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3048259953 10000000000 22205771538371 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1858228831/5000000000 : ℝ)^19 ≤ (28542826234151/100000000000000 : ℝ)^15 := by
    have hnat : (1858228831 : ℕ)^19*100000000000000^15 ≤ 28542826234151^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858228831 5000000000 28542826234151 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2858528871/5000000000 : ℝ), (3048259953/10000000000 : ℝ), (1858228831/5000000000 : ℝ)] ![(12312850551753/25000000000000 : ℝ), (22205771538371/100000000000000 : ℝ), (28542826234151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2858528871/5000000000 : ℝ)|^19 ≤ (12312850551753/25000000000000 : ℝ)^15
        have hw : |(2858528871/5000000000 : ℝ)|=(2858528871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3048259953/10000000000 : ℝ)|^19 ≤ (22205771538371/100000000000000 : ℝ)^15
        have hw : |(3048259953/10000000000 : ℝ)|=(3048259953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1858228831/5000000000 : ℝ)|^19 ≤ (28542826234151/100000000000000 : ℝ)^15
        have hw : |(1858228831/5000000000 : ℝ)|=(1858228831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314007_s0_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (636070589/2000000000 : ℝ)*x 0 + (-3356510633/10000000000 : ℝ)*x 1 + (-5920411071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (636070589/2000000000 : ℝ)^19 ≤ (23431606803351/100000000000000 : ℝ)^15 := by
    have hnat : (636070589 : ℕ)^19*100000000000000^15 ≤ 23431606803351^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636070589 2000000000 23431606803351 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3356510633/10000000000 : ℝ)^19 ≤ (25087545198217/100000000000000 : ℝ)^15 := by
    have hnat : (3356510633 : ℕ)^19*100000000000000^15 ≤ 25087545198217^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3356510633 10000000000 25087545198217 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5920411071/10000000000 : ℝ)^19 ≤ (25740423994393/50000000000000 : ℝ)^15 := by
    have hnat : (5920411071 : ℕ)^19*50000000000000^15 ≤ 25740423994393^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5920411071 10000000000 25740423994393 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(636070589/2000000000 : ℝ), (-3356510633/10000000000 : ℝ), (-5920411071/10000000000 : ℝ)] ![(23431606803351/100000000000000 : ℝ), (25087545198217/100000000000000 : ℝ), (25740423994393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(636070589/2000000000 : ℝ)|^19 ≤ (23431606803351/100000000000000 : ℝ)^15
        have hw : |(636070589/2000000000 : ℝ)|=(636070589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3356510633/10000000000 : ℝ)|^19 ≤ (25087545198217/100000000000000 : ℝ)^15
        have hw : |(-3356510633/10000000000 : ℝ)|=(3356510633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5920411071/10000000000 : ℝ)|^19 ≤ (25740423994393/50000000000000 : ℝ)^15
        have hw : |(-5920411071/10000000000 : ℝ)|=(5920411071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314007_s0_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-834999003/5000000000 : ℝ)*x 0 + (-366893539/500000000 : ℝ)*x 1 + (3033865719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (834999003/5000000000 : ℝ)^19 ≤ (518095966191/5000000000000 : ℝ)^15 := by
    have hnat : (834999003 : ℕ)^19*5000000000000^15 ≤ 518095966191^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834999003 5000000000 518095966191 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366893539/500000000 : ℝ)^19 ≤ (67565045791119/100000000000000 : ℝ)^15 := by
    have hnat : (366893539 : ℕ)^19*100000000000000^15 ≤ 67565045791119^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366893539 500000000 67565045791119 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3033865719/10000000000 : ℝ)^19 ≤ (22073034865931/100000000000000 : ℝ)^15 := by
    have hnat : (3033865719 : ℕ)^19*100000000000000^15 ≤ 22073034865931^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3033865719 10000000000 22073034865931 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-834999003/5000000000 : ℝ), (-366893539/500000000 : ℝ), (3033865719/10000000000 : ℝ)] ![(518095966191/5000000000000 : ℝ), (67565045791119/100000000000000 : ℝ), (22073034865931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-834999003/5000000000 : ℝ)|^19 ≤ (518095966191/5000000000000 : ℝ)^15
        have hw : |(-834999003/5000000000 : ℝ)|=(834999003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-366893539/500000000 : ℝ)|^19 ≤ (67565045791119/100000000000000 : ℝ)^15
        have hw : |(-366893539/500000000 : ℝ)|=(366893539/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3033865719/10000000000 : ℝ)|^19 ≤ (22073034865931/100000000000000 : ℝ)^15
        have hw : |(3033865719/10000000000 : ℝ)|=(3033865719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314007_s0_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6747798299/10000000000 : ℝ)*x 0 + (2671070727/10000000000 : ℝ)*x 1 + (571426731/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6747798299/10000000000 : ℝ)^19 ≤ (75947823093/125000000000 : ℝ)^15 := by
    have hnat : (6747798299 : ℕ)^19*125000000000^15 ≤ 75947823093^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6747798299 10000000000 75947823093 125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2671070727/10000000000 : ℝ)^19 ≤ (9392290043423/50000000000000 : ℝ)^15 := by
    have hnat : (2671070727 : ℕ)^19*50000000000000^15 ≤ 9392290043423^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2671070727 10000000000 9392290043423 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571426731/2000000000 : ℝ)^19 ≤ (20457161421317/100000000000000 : ℝ)^15 := by
    have hnat : (571426731 : ℕ)^19*100000000000000^15 ≤ 20457161421317^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571426731 2000000000 20457161421317 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6747798299/10000000000 : ℝ), (2671070727/10000000000 : ℝ), (571426731/2000000000 : ℝ)] ![(75947823093/125000000000 : ℝ), (9392290043423/50000000000000 : ℝ), (20457161421317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6747798299/10000000000 : ℝ)|^19 ≤ (75947823093/125000000000 : ℝ)^15
        have hw : |(6747798299/10000000000 : ℝ)|=(6747798299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2671070727/10000000000 : ℝ)|^19 ≤ (9392290043423/50000000000000 : ℝ)^15
        have hw : |(2671070727/10000000000 : ℝ)|=(2671070727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(571426731/2000000000 : ℝ)|^19 ≤ (20457161421317/100000000000000 : ℝ)^15
        have hw : |(571426731/2000000000 : ℝ)|=(571426731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314007_s0_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1441700689/5000000000 : ℝ)*x 0 + (-4387173297/10000000000 : ℝ)*x 1 + (-5238241341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1441700689/5000000000 : ℝ)^19 ≤ (5173921129679/25000000000000 : ℝ)^15 := by
    have hnat : (1441700689 : ℕ)^19*25000000000000^15 ≤ 5173921129679^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1441700689 5000000000 5173921129679 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4387173297/10000000000 : ℝ)^19 ≤ (8804554964907/25000000000000 : ℝ)^15 := by
    have hnat : (4387173297 : ℕ)^19*25000000000000^15 ≤ 8804554964907^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4387173297 10000000000 8804554964907 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238241341/10000000000 : ℝ)^19 ≤ (22043047800921/50000000000000 : ℝ)^15 := by
    have hnat : (5238241341 : ℕ)^19*50000000000000^15 ≤ 22043047800921^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238241341 10000000000 22043047800921 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1441700689/5000000000 : ℝ), (-4387173297/10000000000 : ℝ), (-5238241341/10000000000 : ℝ)] ![(5173921129679/25000000000000 : ℝ), (8804554964907/25000000000000 : ℝ), (22043047800921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1441700689/5000000000 : ℝ)|^19 ≤ (5173921129679/25000000000000 : ℝ)^15
        have hw : |(1441700689/5000000000 : ℝ)|=(1441700689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4387173297/10000000000 : ℝ)|^19 ≤ (8804554964907/25000000000000 : ℝ)^15
        have hw : |(-4387173297/10000000000 : ℝ)|=(4387173297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5238241341/10000000000 : ℝ)|^19 ≤ (22043047800921/50000000000000 : ℝ)^15
        have hw : |(-5238241341/10000000000 : ℝ)|=(5238241341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314007_s1_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3403877737/10000000000 : ℝ)*x 0 + (-4584014003/10000000000 : ℝ)*x 1 + (4584013993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3403877737/10000000000 : ℝ)^19 ≤ (25536831233529/100000000000000 : ℝ)^15 := by
    have hnat : (3403877737 : ℕ)^19*100000000000000^15 ≤ 25536831233529^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3403877737 10000000000 25536831233529 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4584014003/10000000000 : ℝ)^19 ≤ (37231584427773/100000000000000 : ℝ)^15 := by
    have hnat : (4584014003 : ℕ)^19*100000000000000^15 ≤ 37231584427773^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4584014003 10000000000 37231584427773 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4584013993/10000000000 : ℝ)^19 ≤ (18615792162447/50000000000000 : ℝ)^15 := by
    have hnat : (4584013993 : ℕ)^19*50000000000000^15 ≤ 18615792162447^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4584013993 10000000000 18615792162447 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3403877737/10000000000 : ℝ), (-4584014003/10000000000 : ℝ), (4584013993/10000000000 : ℝ)] ![(25536831233529/100000000000000 : ℝ), (37231584427773/100000000000000 : ℝ), (18615792162447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3403877737/10000000000 : ℝ)|^19 ≤ (25536831233529/100000000000000 : ℝ)^15
        have hw : |(-3403877737/10000000000 : ℝ)|=(3403877737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4584014003/10000000000 : ℝ)|^19 ≤ (37231584427773/100000000000000 : ℝ)^15
        have hw : |(-4584014003/10000000000 : ℝ)|=(4584014003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4584013993/10000000000 : ℝ)|^19 ≤ (18615792162447/50000000000000 : ℝ)^15
        have hw : |(4584013993/10000000000 : ℝ)|=(4584013993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314007_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2646592247/5000000000 : ℝ)*x 0 + (3625789801/10000000000 : ℝ)*x 1 + (1812894897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646592247/5000000000 : ℝ)^19 ≤ (44672635351187/100000000000000 : ℝ)^15 := by
    have hnat : (2646592247 : ℕ)^19*100000000000000^15 ≤ 44672635351187^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646592247 5000000000 44672635351187 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3625789801/10000000000 : ℝ)^19 ≤ (276636823497/1000000000000 : ℝ)^15 := by
    have hnat : (3625789801 : ℕ)^19*1000000000000^15 ≤ 276636823497^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3625789801 10000000000 276636823497 1000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1812894897/5000000000 : ℝ)^19 ≤ (553273645641/2000000000000 : ℝ)^15 := by
    have hnat : (1812894897 : ℕ)^19*2000000000000^15 ≤ 553273645641^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1812894897 5000000000 553273645641 2000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646592247/5000000000 : ℝ), (3625789801/10000000000 : ℝ), (1812894897/5000000000 : ℝ)] ![(44672635351187/100000000000000 : ℝ), (276636823497/1000000000000 : ℝ), (553273645641/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646592247/5000000000 : ℝ)|^19 ≤ (44672635351187/100000000000000 : ℝ)^15
        have hw : |(2646592247/5000000000 : ℝ)|=(2646592247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3625789801/10000000000 : ℝ)|^19 ≤ (276636823497/1000000000000 : ℝ)^15
        have hw : |(3625789801/10000000000 : ℝ)|=(3625789801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1812894897/5000000000 : ℝ)|^19 ≤ (553273645641/2000000000000 : ℝ)^15
        have hw : |(1812894897/5000000000 : ℝ)|=(1812894897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314007_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3403877737/10000000000 : ℝ)*x 0 + (-4584014003/10000000000 : ℝ)*x 1 + (-4584013993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3403877737/10000000000 : ℝ)^19 ≤ (25536831233529/100000000000000 : ℝ)^15 := by
    have hnat : (3403877737 : ℕ)^19*100000000000000^15 ≤ 25536831233529^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3403877737 10000000000 25536831233529 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4584014003/10000000000 : ℝ)^19 ≤ (37231584427773/100000000000000 : ℝ)^15 := by
    have hnat : (4584014003 : ℕ)^19*100000000000000^15 ≤ 37231584427773^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4584014003 10000000000 37231584427773 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4584013993/10000000000 : ℝ)^19 ≤ (18615792162447/50000000000000 : ℝ)^15 := by
    have hnat : (4584013993 : ℕ)^19*50000000000000^15 ≤ 18615792162447^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4584013993 10000000000 18615792162447 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3403877737/10000000000 : ℝ), (-4584014003/10000000000 : ℝ), (-4584013993/10000000000 : ℝ)] ![(25536831233529/100000000000000 : ℝ), (37231584427773/100000000000000 : ℝ), (18615792162447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3403877737/10000000000 : ℝ)|^19 ≤ (25536831233529/100000000000000 : ℝ)^15
        have hw : |(3403877737/10000000000 : ℝ)|=(3403877737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4584014003/10000000000 : ℝ)|^19 ≤ (37231584427773/100000000000000 : ℝ)^15
        have hw : |(-4584014003/10000000000 : ℝ)|=(4584014003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4584013993/10000000000 : ℝ)|^19 ≤ (18615792162447/50000000000000 : ℝ)^15
        have hw : |(-4584013993/10000000000 : ℝ)|=(4584013993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314007_s1_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2646592247/5000000000 : ℝ)*x 0 + (-3625789801/10000000000 : ℝ)*x 1 + (1812894897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646592247/5000000000 : ℝ)^19 ≤ (44672635351187/100000000000000 : ℝ)^15 := by
    have hnat : (2646592247 : ℕ)^19*100000000000000^15 ≤ 44672635351187^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646592247 5000000000 44672635351187 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3625789801/10000000000 : ℝ)^19 ≤ (276636823497/1000000000000 : ℝ)^15 := by
    have hnat : (3625789801 : ℕ)^19*1000000000000^15 ≤ 276636823497^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3625789801 10000000000 276636823497 1000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1812894897/5000000000 : ℝ)^19 ≤ (553273645641/2000000000000 : ℝ)^15 := by
    have hnat : (1812894897 : ℕ)^19*2000000000000^15 ≤ 553273645641^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1812894897 5000000000 553273645641 2000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646592247/5000000000 : ℝ), (-3625789801/10000000000 : ℝ), (1812894897/5000000000 : ℝ)] ![(44672635351187/100000000000000 : ℝ), (276636823497/1000000000000 : ℝ), (553273645641/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646592247/5000000000 : ℝ)|^19 ≤ (44672635351187/100000000000000 : ℝ)^15
        have hw : |(2646592247/5000000000 : ℝ)|=(2646592247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3625789801/10000000000 : ℝ)|^19 ≤ (276636823497/1000000000000 : ℝ)^15
        have hw : |(-3625789801/10000000000 : ℝ)|=(3625789801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1812894897/5000000000 : ℝ)|^19 ≤ (553273645641/2000000000000 : ℝ)^15
        have hw : |(1812894897/5000000000 : ℝ)|=(1812894897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314007 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]]) : False := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (87867/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1064401010795949/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1064401010795949/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(64673127956063/400000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-473821227/2000000000 : ℝ)*X 0 0+(-3205760027/5000000000 : ℝ)*X 0 1+(443510499/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314007_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((57181517/100000000 : ℝ)*X 1 0+(387671649/1250000000 : ℝ)*X 1 1+(3664638399/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314007_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_4 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314007_s0_4 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1782988247/10000000000 : ℝ)*X 0 0+(-1489573597/2000000000 : ℝ)*X 0 1+(279459711/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314007_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1143514139/2500000000 : ℝ)*X 1 0+(442943247/1250000000 : ℝ)*X 1 1+(4463836369/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314007_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1868688663/5000000000 : ℝ)*X 2 0+(-2857539333/10000000000 : ℝ)*X 2 1+(-5857842243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314007_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-730631833/2500000000 : ℝ)*X 0 0+(-6315897949/10000000000 : ℝ)*X 0 1+(3141856261/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314007_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((2858528871/5000000000 : ℝ)*X 1 0+(3048259953/10000000000 : ℝ)*X 1 1+(1858228831/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314007_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((636070589/2000000000 : ℝ)*X 2 0+(-3356510633/10000000000 : ℝ)*X 2 1+(-5920411071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314007_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-834999003/5000000000 : ℝ)*X 0 0+(-366893539/500000000 : ℝ)*X 0 1+(3033865719/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314007_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((6747798299/10000000000 : ℝ)*X 1 0+(2671070727/10000000000 : ℝ)*X 1 1+(571426731/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314007_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((1441700689/5000000000 : ℝ)*X 2 0+(-4387173297/10000000000 : ℝ)*X 2 1+(-5238241341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314007_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((50151/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(50151/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (59643194585696064069999/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (136078087509/50000000000 : ℝ)*(base3) + (213130002589/200000000000 : ℝ)*(base7) + (205891273669/500000000000 : ℝ)*(base40) + (297361960321/250000000000 : ℝ)*(base49) + (2849310767143/1000000000000 : ℝ)*(major_s0_0) + (6619086894183/1000000000000 : ℝ)*(major_s0_1) + (2849310767143/1000000000000 : ℝ)*(major_s0_2) + (3769776127041/1000000000000 : ℝ)*(sp_s0_4) + (170918892561/50000000000 : ℝ)*(sp_s0_7) + (3070013746229/500000000000 : ℝ)*(sp_s0_8) + (1709209067273/500000000000 : ℝ)*(sp_s0_9) + (3613971/1000000000000 : ℝ)*(sp_s0_14) + (25610851/500000000000 : ℝ)*(sp_s0_15) + (91505029/1000000000000 : ℝ)*(sp_s0_20) + (331182347447/200000000000 : ℝ)*(f.failure) + (427308669531/125000000000 : ℝ)*(f.sum) + (263174732239/1250000000000000000000000 : ℝ)*base63 + (11843414546703707/10000000000000000000000000000 : ℝ)*base65 + (2625094219064667/10000000000000000000000000000 : ℝ)*base66 + (81651402838009/400000000000000000000000000 : ℝ)*base69 + (628782235836517/2500000000000000000000000000 : ℝ)*base70 + (4683269422703707/10000000000000000000000000000 : ℝ)*base73 + (193553790278471/400000000000000000000000000 : ℝ)*base75 + (150644335398009/400000000000000000000000000 : ℝ)*base77 + (10628623191753/31250000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (2157/20000000000000000 : ℝ)*base86 + (17843/20000000000000000 : ℝ)*base89 + (2157/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-6473/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(-6473/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (21792110105069723681211/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1639863694159/1000000000000 : ℝ)*(base3) + (192199138459/1000000000000 : ℝ)*(base7) + (9166879/1000000000000 : ℝ)*(base13) + (437504938819/500000000000 : ℝ)*(base40) + (28769553523/25000000000 : ℝ)*(base49) + (2490981924349/1000000000000 : ℝ)*(major_s0_0) + (2490981924349/1000000000000 : ℝ)*(major_s0_1) + (2490981924349/1000000000000 : ℝ)*(major_s0_2) + (5108851/200000000000 : ℝ)*(sp_s0_0) + (150847937/1000000000000 : ℝ)*(sp_s0_9) + (1710837632459/500000000000 : ℝ)*(sp_s0_13) + (5061573550149/1000000000000 : ℝ)*(sp_s0_14) + (1710779564057/500000000000 : ℝ)*(sp_s0_15) + (120061/1000000000000 : ℝ)*(sp_s0_21) + (1447664555701/1000000000000 : ℝ)*(f.failure) + (3421709976051/1000000000000 : ℝ)*(f.sum) + (2430243201/10000000000000000000000 : ℝ)*base63 + (4338607145662201/10000000000000000000000000000 : ℝ)*base65 + (5218781751662201/10000000000000000000000000000 : ℝ)*base66 + (95829669997987/400000000000000000000000000 : ℝ)*base69 + (392412900847031/2500000000000000000000000000 : ℝ)*base70 + (3397719600662201/10000000000000000000000000000 : ℝ)*base73 + (684250442013/400000000000000000000000000 : ℝ)*base75 + (91893450802013/400000000000000000000000000 : ℝ)*base76 + (972190557/2000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (15369/100000000000000000 : ℝ)*base87 + (15369/100000000000000000 : ℝ)*base89 + (15369/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1341/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1341/2000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (351960959127755051763/100000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3257084847559/1000000000000 : ℝ)*(base3) + (241905633017/200000000000 : ℝ)*(base7) + (1071318874117/1000000000000 : ℝ)*(base40) + (2892556525119/1000000000000 : ℝ)*(base49) + (429122240097/250000000000 : ℝ)*(base50) + (3523210307967/1000000000000 : ℝ)*(major_s0_0) + (3523210307967/1000000000000 : ℝ)*(major_s0_1) + (3523210307967/1000000000000 : ℝ)*(major_s0_2) + (16291719/1000000000000 : ℝ)*(sp_s0_0) + (473717/62500000000 : ℝ)*(sp_s0_1) + (88784719/1000000000000 : ℝ)*(sp_s0_7) + (4290240275269/1000000000000 : ℝ)*(sp_s0_20) + (1509484523959/200000000000 : ℝ)*(sp_s0_21) + (4290345351707/1000000000000 : ℝ)*(sp_s0_22) + (81902267299/40000000000 : ℝ)*(f.failure) + (4290345351707/1000000000000 : ℝ)*(f.sum) + (255488409/1250000000000000000000 : ℝ)*base63 + (1613261947025683/10000000000000000000000000000 : ℝ)*base65 + (5039795835025683/10000000000000000000000000000 : ℝ)*base66 + (231145769346079/400000000000000000000000000 : ℝ)*base68 + (1204000157906573/2500000000000000000000000000 : ℝ)*base70 + (1917477966974317/10000000000000000000000000000 : ℝ)*base72 + (15742435306079/400000000000000000000000000 : ℝ)*base75 + (49129805986079/400000000000000000000000000 : ℝ)*base76 + (1207680913/10000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (3631/4000000000000000 : ℝ)*base87 + (3631/4000000000000000 : ℝ)*base89 + (3631/4000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have s1_pow0 : (50151/100000 : ℝ) ^ (37/8 : ℝ) ≤ (4109539290024365803/100000000000000000000 : ℝ) := by
    have hpowers : (50151/100000 : ℝ)^37 ≤ (4109539290024365803/100000000000000000000 : ℝ)^8 := by
      have hnat : (50151 : ℕ)^37*100000000000000000000^8 ≤ 4109539290024365803^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50151 100000 4109539290024365803 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (50151/100000 : ℝ)) (X := (4109539290024365803/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (104109539290024365803/100000000000000000000 : ℝ) ≤ (10087457896457983/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (104109539290024365803/100000000000000000000 : ℝ)^8 ≤ (10087457896457983/10000000000000000 : ℝ)^37 := by
      have hnat : (104109539290024365803 : ℕ)^8*10000000000000000^37 ≤ 10087457896457983^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104109539290024365803 100000000000000000000 10087457896457983 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10087457896457983/10000000000000000 : ℝ)) (X := (104109539290024365803/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (54109539290024365803/50000000000000000000 : ℝ) ≤ (2543062614654897/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (54109539290024365803/50000000000000000000 : ℝ)^8 ≤ (2543062614654897/2500000000000000 : ℝ)^37 := by
      have hnat : (54109539290024365803 : ℕ)^8*2500000000000000^37 ≤ 2543062614654897^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54109539290024365803 50000000000000000000 2543062614654897 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2543062614654897/2500000000000000 : ℝ)) (X := (54109539290024365803/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(29152632152661/1671700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(16958512432321/1003020000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (50151/100000 : ℝ)) (alpha := (29152632152661/1671700000000000 : ℝ)) (beta := (16958512432321/1003020000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (50151/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(29152632152661/1671700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(16958512432321/1003020000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (6473/100000 : ℝ) ^ (37/8 : ℝ) ≤ (317222097548887/100000000000000000000 : ℝ) := by
    have hpowers : (6473/100000 : ℝ)^37 ≤ (317222097548887/100000000000000000000 : ℝ)^8 := by
      have hnat : (6473 : ℕ)^37*100000000000000000000^8 ≤ 317222097548887^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6473 100000 317222097548887 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6473/100000 : ℝ)) (X := (317222097548887/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100000317222097548887/100000000000000000000 : ℝ) ≤ (10000006858847637/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (100000317222097548887/100000000000000000000 : ℝ)^8 ≤ (10000006858847637/10000000000000000 : ℝ)^37 := by
      have hnat : (100000317222097548887 : ℕ)^8*10000000000000000^37 ≤ 10000006858847637^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100000317222097548887 100000000000000000000 10000006858847637 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000006858847637/10000000000000000 : ℝ)) (X := (100000317222097548887/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50000317222097548887/50000000000000000000 : ℝ) ≤ (500000685883911/500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (50000317222097548887/50000000000000000000 : ℝ)^8 ≤ (500000685883911/500000000000000 : ℝ)^37 := by
      have hnat : (50000317222097548887 : ℕ)^8*500000000000000^37 ≤ 500000685883911^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000317222097548887 50000000000000000000 500000685883911 500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000685883911/500000000000000 : ℝ)) (X := (50000317222097548887/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(6858847637/647300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(6858830583/647300000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (6473/100000 : ℝ)) (alpha := (6858847637/647300000000000 : ℝ)) (beta := (6858830583/647300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (6473/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(6858847637/647300000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(6858830583/647300000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (1341/2000 : ℝ) ^ (37/8 : ℝ) ≤ (3148649823057320869/20000000000000000000 : ℝ) := by
    have hpowers : (1341/2000 : ℝ)^37 ≤ (3148649823057320869/20000000000000000000 : ℝ)^8 := by
      have hnat : (1341 : ℕ)^37*20000000000000000000^8 ≤ 3148649823057320869^8*2000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1341 2000 3148649823057320869 20000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1341/2000 : ℝ)) (X := (3148649823057320869/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (23148649823057320869/20000000000000000000 : ℝ) ≤ (10321166721640639/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (23148649823057320869/20000000000000000000 : ℝ)^8 ≤ (10321166721640639/10000000000000000 : ℝ)^37 := by
      have hnat : (23148649823057320869 : ℕ)^8*10000000000000000^37 ≤ 10321166721640639^37*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23148649823057320869 20000000000000000000 10321166721640639 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10321166721640639/10000000000000000 : ℝ)) (X := (23148649823057320869/20000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (13148649823057320869/10000000000000000000 : ℝ) ≤ (10609722731651771/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (13148649823057320869/10000000000000000000 : ℝ)^8 ≤ (10609722731651771/10000000000000000 : ℝ)^37 := by
      have hnat : (13148649823057320869 : ℕ)^8*10000000000000000^37 ≤ 10609722731651771^37*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13148649823057320869 10000000000000000000 10609722731651771 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10609722731651771/10000000000000000 : ℝ)) (X := (13148649823057320869/10000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(107055573880213/2235000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(72139002502783/1676250000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1341/2000 : ℝ)) (alpha := (107055573880213/2235000000000000 : ℝ)) (beta := (72139002502783/1676250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1341/2000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(107055573880213/2235000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(72139002502783/1676250000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3403877737/10000000000 : ℝ)*X 0 0+(-4584014003/10000000000 : ℝ)*X 0 1+(4584013993/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314007_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2646592247/5000000000 : ℝ)*X 1 0+(3625789801/10000000000 : ℝ)*X 1 1+(1812894897/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314007_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3403877737/10000000000 : ℝ)*X 2 0+(-4584014003/10000000000 : ℝ)*X 2 1+(-4584013993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314007_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((2646592247/5000000000 : ℝ)*X 0 0+(-3625789801/10000000000 : ℝ)*X 0 1+(1812894897/5000000000 : ℝ)*X 0 2+(2646592247/5000000000 : ℝ)*X 1 0+(-3625789801/10000000000 : ℝ)*X 1 1+(1812894897/5000000000 : ℝ)*X 1 2+(2646592247/5000000000 : ℝ)*X 2 0+(-3625789801/10000000000 : ℝ)*X 2 1+(1812894897/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314007_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-366207/50000 : ℝ) < ((-172069/100000 : ℝ)*P 0+(-172069/100000 : ℝ)*P 1+(-172069/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-366207/50000 : ℝ) < (-26111141365351662195508036717049/3616788750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1563/1000000000000 : ℝ)*(base1) + (798981020501/1000000000000 : ℝ)*(base3) + (24063/200000000000 : ℝ)*(base10) + (514666005887/1000000000000 : ℝ)*(base40) + (669894305233/500000000000 : ℝ)*(base49) + (397566925063/500000000000 : ℝ)*(base50) + (15939/250000000000 : ℝ)*(base53) + (3764971333/8000000000 : ℝ)*(base59) + (172069/100000 : ℝ)*(major_s1_0) + (172069/100000 : ℝ)*(major_s1_1) + (430172484061/250000000000 : ℝ)*(major_s1_2) + (1203237696471/500000000000 : ℝ)*(sp_s1_0) + (641091306439/200000000000 : ℝ)*(sp_s1_1) + (48129511509/20000000000 : ℝ)*(sp_s1_2) + (12563686121/62500000000 : ℝ)*(sp_s1_6) + (48129511509/20000000000 : ℝ)*(f.sum) + (1479538045910994061/3616788750000000000000000000000 : ℝ)*base62 + (316192090551349/838125000000000000000000000 : ℝ)*base64 + (8482248457493/6473000000000000000000000 : ℝ)*base67 + (196783609757/558750000000000000000000000 : ℝ)*base68 + (7767108753398482091/28021871250000000000000000000000 : ℝ)*base70 + (65810919777557/250755000000000000000000000 : ℝ)*base72 + (7624631766541/32365000000000000000000000 : ℝ)*base74 + (13299855953331/83585000000000000000000000 : ℝ)*base77 + (1011481704746920859/1623137115000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c314008_s0_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2100260617/5000000000 : ℝ)*x 0 + (-4267931847/10000000000 : ℝ)*x 1 + (-826693223/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100260617/5000000000 : ℝ)^19 ≤ (33331180870971/100000000000000 : ℝ)^15 := by
    have hnat : (2100260617 : ℕ)^19*100000000000000^15 ≤ 33331180870971^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100260617 5000000000 33331180870971 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4267931847/10000000000 : ℝ)^19 ≤ (34010169985943/100000000000000 : ℝ)^15 := by
    have hnat : (4267931847 : ℕ)^19*100000000000000^15 ≤ 34010169985943^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4267931847 10000000000 34010169985943 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (826693223/2000000000 : ℝ)^19 ≤ (32658649128143/100000000000000 : ℝ)^15 := by
    have hnat : (826693223 : ℕ)^19*100000000000000^15 ≤ 32658649128143^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826693223 2000000000 32658649128143 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2100260617/5000000000 : ℝ), (-4267931847/10000000000 : ℝ), (-826693223/2000000000 : ℝ)] ![(33331180870971/100000000000000 : ℝ), (34010169985943/100000000000000 : ℝ), (32658649128143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2100260617/5000000000 : ℝ)|^19 ≤ (33331180870971/100000000000000 : ℝ)^15
        have hw : |(-2100260617/5000000000 : ℝ)|=(2100260617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4267931847/10000000000 : ℝ)|^19 ≤ (34010169985943/100000000000000 : ℝ)^15
        have hw : |(-4267931847/10000000000 : ℝ)|=(4267931847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-826693223/2000000000 : ℝ)|^19 ≤ (32658649128143/100000000000000 : ℝ)^15
        have hw : |(-826693223/2000000000 : ℝ)|=(826693223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314008_s0_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4123769563/10000000000 : ℝ)*x 0 + (4190930769/10000000000 : ℝ)*x 1 + (-85741569/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4123769563/10000000000 : ℝ)^19 ≤ (16280818328293/50000000000000 : ℝ)^15 := by
    have hnat : (4123769563 : ℕ)^19*50000000000000^15 ≤ 16280818328293^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4123769563 10000000000 16280818328293 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4190930769/10000000000 : ℝ)^19 ≤ (1329392653529/4000000000000 : ℝ)^15 := by
    have hnat : (4190930769 : ℕ)^19*4000000000000^15 ≤ 1329392653529^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4190930769 10000000000 1329392653529 4000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85741569/200000000 : ℝ)^19 ≤ (2137721686507/6250000000000 : ℝ)^15 := by
    have hnat : (85741569 : ℕ)^19*6250000000000^15 ≤ 2137721686507^15*200000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85741569 200000000 2137721686507 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4123769563/10000000000 : ℝ), (4190930769/10000000000 : ℝ), (-85741569/200000000 : ℝ)] ![(16280818328293/50000000000000 : ℝ), (1329392653529/4000000000000 : ℝ), (2137721686507/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4123769563/10000000000 : ℝ)|^19 ≤ (16280818328293/50000000000000 : ℝ)^15
        have hw : |(4123769563/10000000000 : ℝ)|=(4123769563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4190930769/10000000000 : ℝ)|^19 ≤ (1329392653529/4000000000000 : ℝ)^15
        have hw : |(4190930769/10000000000 : ℝ)|=(4190930769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85741569/200000000 : ℝ)|^19 ≤ (2137721686507/6250000000000 : ℝ)^15
        have hw : |(-85741569/200000000 : ℝ)|=(85741569/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314008_s0_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4277585381/10000000000 : ℝ)*x 0 + (-4114896727/10000000000 : ℝ)*x 1 + (2104650023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4277585381/10000000000 : ℝ)^19 ≤ (17053819983679/50000000000000 : ℝ)^15 := by
    have hnat : (4277585381 : ℕ)^19*50000000000000^15 ≤ 17053819983679^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4277585381 10000000000 17053819983679 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4114896727/10000000000 : ℝ)^19 ≤ (32472918612723/100000000000000 : ℝ)^15 := by
    have hnat : (4114896727 : ℕ)^19*100000000000000^15 ≤ 32472918612723^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114896727 10000000000 32472918612723 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2104650023/5000000000 : ℝ)^19 ≤ (33419441404283/100000000000000 : ℝ)^15 := by
    have hnat : (2104650023 : ℕ)^19*100000000000000^15 ≤ 33419441404283^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104650023 5000000000 33419441404283 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4277585381/10000000000 : ℝ), (-4114896727/10000000000 : ℝ), (2104650023/5000000000 : ℝ)] ![(17053819983679/50000000000000 : ℝ), (32472918612723/100000000000000 : ℝ), (33419441404283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4277585381/10000000000 : ℝ)|^19 ≤ (17053819983679/50000000000000 : ℝ)^15
        have hw : |(4277585381/10000000000 : ℝ)|=(4277585381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4114896727/10000000000 : ℝ)|^19 ≤ (32472918612723/100000000000000 : ℝ)^15
        have hw : |(-4114896727/10000000000 : ℝ)|=(4114896727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2104650023/5000000000 : ℝ)|^19 ≤ (33419441404283/100000000000000 : ℝ)^15
        have hw : |(2104650023/5000000000 : ℝ)|=(2104650023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314008 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, false]]) : False := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base10 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).1]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, false]] hX 0 (by
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
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1064401010795949/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
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
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1064401010795949/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (64673127956063/400000000000000 : ℝ)) (beta := (1064401010795949/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(64673127956063/400000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1064401010795949/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2100260617/5000000000 : ℝ)*X 0 0+(-4267931847/10000000000 : ℝ)*X 0 1+(-826693223/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314008_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((4123769563/10000000000 : ℝ)*X 1 0+(4190930769/10000000000 : ℝ)*X 1 1+(-85741569/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314008_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((4277585381/10000000000 : ℝ)*X 2 0+(-4114896727/10000000000 : ℝ)*X 2 1+(2104650023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314008_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-366207/50000 : ℝ) < ((-172069/100000 : ℝ)*P 0+(-172069/100000 : ℝ)*P 1+(-172069/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-366207/50000 : ℝ) < (-8990708546726730460467/1250000000000000000000 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(base1) + (13443/1000000000000 : ℝ)*(base10) + (4673/250000000000 : ℝ)*(base18) + (141/200000000000 : ℝ)*(base21) + (482815646589/500000000000 : ℝ)*(base39) + (227964165503/500000000000 : ℝ)*(base40) + (275054314759/500000000000 : ℝ)*(base49) + (20846168153/50000000000 : ℝ)*(base50) + (18152042249/40000000000 : ℝ)*(base60) + (172069/100000 : ℝ)*(major_s0_0) + (172069/100000 : ℝ)*(major_s0_1) + (172069/100000 : ℝ)*(major_s0_2) + (3397522265681/1000000000000 : ℝ)*(sp_s0_0) + (149845141277/62500000000 : ℝ)*(sp_s0_1) + (2397522278419/1000000000000 : ℝ)*(sp_s0_2) + (599380569781/250000000000 : ℝ)*(f.sum) + (2536101573/5000000000000000000000 : ℝ)*base62 + (5053557997/10000000000000000000000 : ℝ)*base65 + (24620927/80000000000000000000 : ℝ)*base66 + (1195958983/5000000000000000000000 : ℝ)*base68 + (1142392433/2500000000000000000000 : ℝ)*base71 + (20362479/1000000000000000000000 : ℝ)*base72 + (4877279389/10000000000000000000000 : ℝ)*base74 + (3876921363/10000000000000000000000 : ℝ)*base77 + (1079268827/5000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p014_b003 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (c : Fin 88) (hlo : 7 ≤ c.val) (hhi : c.val < 9)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=7 ∨ c=8 := by omega
  rcases hc with rfl|rfl
  · exact collision_c314007 p hpa (by linarith only [hpb]) X hX
  · exact collision_c314008 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (c : Fin 88) (hlo : 7 ≤ c.val) (hhi : c.val < 9)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p014_b003 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

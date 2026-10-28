-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p002_b028
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:13:48.38134+00:00
-- url     : https://prove2.me/submissions/d883a117-2fc3-4b83-af8a-c1379a6bdb9d

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
theorem collision_support_c302069_s0_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2022446223/10000000000 : ℝ)*x 0 + (-7553603811/10000000000 : ℝ)*x 1 + (2844697837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2022446223/10000000000 : ℝ)^131 ≤ (603231471563/5000000000000 : ℝ)^99 := by
    have hnat : (2022446223 : ℕ)^131*5000000000000^99 ≤ 603231471563^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022446223 10000000000 603231471563 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7553603811/10000000000 : ℝ)^131 ≤ (34493693991953/50000000000000 : ℝ)^99 := by
    have hnat : (7553603811 : ℕ)^131*50000000000000^99 ≤ 34493693991953^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7553603811 10000000000 34493693991953 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2844697837/10000000000 : ℝ)^131 ≤ (4736995641879/25000000000000 : ℝ)^99 := by
    have hnat : (2844697837 : ℕ)^131*25000000000000^99 ≤ 4736995641879^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2844697837 10000000000 4736995641879 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2022446223/10000000000 : ℝ), (-7553603811/10000000000 : ℝ), (2844697837/10000000000 : ℝ)] ![(603231471563/5000000000000 : ℝ), (34493693991953/50000000000000 : ℝ), (4736995641879/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2022446223/10000000000 : ℝ)|^131 ≤ (603231471563/5000000000000 : ℝ)^99
        have hw : |(-2022446223/10000000000 : ℝ)|=(2022446223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7553603811/10000000000 : ℝ)|^131 ≤ (34493693991953/50000000000000 : ℝ)^99
        have hw : |(-7553603811/10000000000 : ℝ)|=(7553603811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2844697837/10000000000 : ℝ)|^131 ≤ (4736995641879/25000000000000 : ℝ)^99
        have hw : |(2844697837/10000000000 : ℝ)|=(2844697837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302069_s0_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1423856201/10000000000 : ℝ)*x 0 + (-264286143/312500000 : ℝ)*x 1 + (256593811/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1423856201/10000000000 : ℝ)^131 ≤ (7582964481923/100000000000000 : ℝ)^99 := by
    have hnat : (1423856201 : ℕ)^131*100000000000000^99 ≤ 7582964481923^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1423856201 10000000000 7582964481923 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264286143/312500000 : ℝ)^131 ≤ (16022524019009/20000000000000 : ℝ)^99 := by
    have hnat : (264286143 : ℕ)^131*20000000000000^99 ≤ 16022524019009^99*312500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264286143 312500000 16022524019009 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256593811/1250000000 : ℝ)^131 ≤ (6152207702243/50000000000000 : ℝ)^99 := by
    have hnat : (256593811 : ℕ)^131*50000000000000^99 ≤ 6152207702243^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256593811 1250000000 6152207702243 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1423856201/10000000000 : ℝ), (-264286143/312500000 : ℝ), (256593811/1250000000 : ℝ)] ![(7582964481923/100000000000000 : ℝ), (16022524019009/20000000000000 : ℝ), (6152207702243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1423856201/10000000000 : ℝ)|^131 ≤ (7582964481923/100000000000000 : ℝ)^99
        have hw : |(-1423856201/10000000000 : ℝ)|=(1423856201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-264286143/312500000 : ℝ)|^131 ≤ (16022524019009/20000000000000 : ℝ)^99
        have hw : |(-264286143/312500000 : ℝ)|=(264286143/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(256593811/1250000000 : ℝ)|^131 ≤ (6152207702243/50000000000000 : ℝ)^99
        have hw : |(256593811/1250000000 : ℝ)|=(256593811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302069_s0_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (175551019/312500000 : ℝ)*x 0 + (338606333/1250000000 : ℝ)*x 1 + (4583271027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (175551019/312500000 : ℝ)^131 ≤ (46623070837287/100000000000000 : ℝ)^99 := by
    have hnat : (175551019 : ℕ)^131*100000000000000^99 ≤ 46623070837287^99*312500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175551019 312500000 46623070837287 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338606333/1250000000 : ℝ)^131 ≤ (2219999490731/12500000000000 : ℝ)^99 := by
    have hnat : (338606333 : ℕ)^131*12500000000000^99 ≤ 2219999490731^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338606333 1250000000 2219999490731 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4583271027/10000000000 : ℝ)^131 ≤ (17808466611547/50000000000000 : ℝ)^99 := by
    have hnat : (4583271027 : ℕ)^131*50000000000000^99 ≤ 17808466611547^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4583271027 10000000000 17808466611547 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(175551019/312500000 : ℝ), (338606333/1250000000 : ℝ), (4583271027/10000000000 : ℝ)] ![(46623070837287/100000000000000 : ℝ), (2219999490731/12500000000000 : ℝ), (17808466611547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(175551019/312500000 : ℝ)|^131 ≤ (46623070837287/100000000000000 : ℝ)^99
        have hw : |(175551019/312500000 : ℝ)|=(175551019/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338606333/1250000000 : ℝ)|^131 ≤ (2219999490731/12500000000000 : ℝ)^99
        have hw : |(338606333/1250000000 : ℝ)|=(338606333/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4583271027/10000000000 : ℝ)|^131 ≤ (17808466611547/50000000000000 : ℝ)^99
        have hw : |(4583271027/10000000000 : ℝ)|=(4583271027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302069_s0_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1056925563/2500000000 : ℝ)*x 0 + (-7843999/31250000 : ℝ)*x 1 + (-1523752513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056925563/2500000000 : ℝ)^131 ≤ (4000914409083/12500000000000 : ℝ)^99 := by
    have hnat : (1056925563 : ℕ)^131*12500000000000^99 ≤ 4000914409083^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056925563 2500000000 4000914409083 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7843999/31250000 : ℝ)^131 ≤ (642254414143/4000000000000 : ℝ)^99 := by
    have hnat : (7843999 : ℕ)^131*4000000000000^99 ≤ 642254414143^99*31250000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7843999 31250000 642254414143 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1523752513/2500000000 : ℝ)^131 ≤ (10387264870963/20000000000000 : ℝ)^99 := by
    have hnat : (1523752513 : ℕ)^131*20000000000000^99 ≤ 10387264870963^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1523752513 2500000000 10387264870963 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056925563/2500000000 : ℝ), (-7843999/31250000 : ℝ), (-1523752513/2500000000 : ℝ)] ![(4000914409083/12500000000000 : ℝ), (642254414143/4000000000000 : ℝ), (10387264870963/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056925563/2500000000 : ℝ)|^131 ≤ (4000914409083/12500000000000 : ℝ)^99
        have hw : |(1056925563/2500000000 : ℝ)|=(1056925563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7843999/31250000 : ℝ)|^131 ≤ (642254414143/4000000000000 : ℝ)^99
        have hw : |(-7843999/31250000 : ℝ)|=(7843999/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1523752513/2500000000 : ℝ)|^131 ≤ (10387264870963/20000000000000 : ℝ)^99
        have hw : |(-1523752513/2500000000 : ℝ)|=(1523752513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302069_s0_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2447857513/10000000000 : ℝ)*x 0 + (-187391533/250000000 : ℝ)*x 1 + (315586719/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2447857513/10000000000 : ℝ)^131 ≤ (7765904775751/50000000000000 : ℝ)^99 := by
    have hnat : (2447857513 : ℕ)^131*50000000000000^99 ≤ 7765904775751^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2447857513 10000000000 7765904775751 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (187391533/250000000 : ℝ)^131 ≤ (34144007313/50000000000 : ℝ)^99 := by
    have hnat : (187391533 : ℕ)^131*50000000000^99 ≤ 34144007313^99*250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187391533 250000000 34144007313 50000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315586719/1250000000 : ℝ)^131 ≤ (16180175811/100000000000 : ℝ)^99 := by
    have hnat : (315586719 : ℕ)^131*100000000000^99 ≤ 16180175811^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315586719 1250000000 16180175811 100000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2447857513/10000000000 : ℝ), (-187391533/250000000 : ℝ), (315586719/1250000000 : ℝ)] ![(7765904775751/50000000000000 : ℝ), (34144007313/50000000000 : ℝ), (16180175811/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2447857513/10000000000 : ℝ)|^131 ≤ (7765904775751/50000000000000 : ℝ)^99
        have hw : |(-2447857513/10000000000 : ℝ)|=(2447857513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-187391533/250000000 : ℝ)|^131 ≤ (34144007313/50000000000 : ℝ)^99
        have hw : |(-187391533/250000000 : ℝ)|=(187391533/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(315586719/1250000000 : ℝ)|^131 ≤ (16180175811/100000000000 : ℝ)^99
        have hw : |(315586719/1250000000 : ℝ)|=(315586719/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302069_s0_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (741275849/1250000000 : ℝ)*x 0 + (123246431/500000000 : ℝ)*x 1 + (556071219/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (741275849/1250000000 : ℝ)^131 ≤ (50086268161111/100000000000000 : ℝ)^99 := by
    have hnat : (741275849 : ℕ)^131*100000000000000^99 ≤ 50086268161111^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741275849 1250000000 50086268161111 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (123246431/500000000 : ℝ)^131 ≤ (15675299723467/100000000000000 : ℝ)^99 := by
    have hnat : (123246431 : ℕ)^131*100000000000000^99 ≤ 15675299723467^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123246431 500000000 15675299723467 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (556071219/1250000000 : ℝ)^131 ≤ (8559608026371/25000000000000 : ℝ)^99 := by
    have hnat : (556071219 : ℕ)^131*25000000000000^99 ≤ 8559608026371^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556071219 1250000000 8559608026371 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(741275849/1250000000 : ℝ), (123246431/500000000 : ℝ), (556071219/1250000000 : ℝ)] ![(50086268161111/100000000000000 : ℝ), (15675299723467/100000000000000 : ℝ), (8559608026371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(741275849/1250000000 : ℝ)|^131 ≤ (50086268161111/100000000000000 : ℝ)^99
        have hw : |(741275849/1250000000 : ℝ)|=(741275849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(123246431/500000000 : ℝ)|^131 ≤ (15675299723467/100000000000000 : ℝ)^99
        have hw : |(123246431/500000000 : ℝ)|=(123246431/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(556071219/1250000000 : ℝ)|^131 ≤ (8559608026371/25000000000000 : ℝ)^99
        have hw : |(556071219/1250000000 : ℝ)|=(556071219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302069_s0_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1836932133/5000000000 : ℝ)*x 0 + (-3114013901/10000000000 : ℝ)*x 1 + (-6106208947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1836932133/5000000000 : ℝ)^131 ≤ (26580113947809/100000000000000 : ℝ)^99 := by
    have hnat : (1836932133 : ℕ)^131*100000000000000^99 ≤ 26580113947809^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1836932133 5000000000 26580113947809 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3114013901/10000000000 : ℝ)^131 ≤ (21357251908471/100000000000000 : ℝ)^99 := by
    have hnat : (3114013901 : ℕ)^131*100000000000000^99 ≤ 21357251908471^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3114013901 10000000000 21357251908471 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6106208947/10000000000 : ℝ)^131 ≤ (13015658531609/25000000000000 : ℝ)^99 := by
    have hnat : (6106208947 : ℕ)^131*25000000000000^99 ≤ 13015658531609^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6106208947 10000000000 13015658531609 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1836932133/5000000000 : ℝ), (-3114013901/10000000000 : ℝ), (-6106208947/10000000000 : ℝ)] ![(26580113947809/100000000000000 : ℝ), (21357251908471/100000000000000 : ℝ), (13015658531609/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1836932133/5000000000 : ℝ)|^131 ≤ (26580113947809/100000000000000 : ℝ)^99
        have hw : |(1836932133/5000000000 : ℝ)|=(1836932133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3114013901/10000000000 : ℝ)|^131 ≤ (21357251908471/100000000000000 : ℝ)^99
        have hw : |(-3114013901/10000000000 : ℝ)|=(3114013901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6106208947/10000000000 : ℝ)|^131 ≤ (13015658531609/25000000000000 : ℝ)^99
        have hw : |(-6106208947/10000000000 : ℝ)|=(6106208947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302069_s0_19 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (741275849/1250000000 : ℝ)*x 0 + (-20267377/50000000 : ℝ)*x 1 + (730719433/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (741275849/1250000000 : ℝ)^131 ≤ (50086268161111/100000000000000 : ℝ)^99 := by
    have hnat : (741275849 : ℕ)^131*100000000000000^99 ≤ 50086268161111^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741275849 1250000000 50086268161111 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20267377/50000000 : ℝ)^131 ≤ (30273645903061/100000000000000 : ℝ)^99 := by
    have hnat : (20267377 : ℕ)^131*100000000000000^99 ≤ 30273645903061^99*50000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20267377 50000000 30273645903061 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (730719433/2500000000 : ℝ)^131 ≤ (19640085925793/100000000000000 : ℝ)^99 := by
    have hnat : (730719433 : ℕ)^131*100000000000000^99 ≤ 19640085925793^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730719433 2500000000 19640085925793 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(741275849/1250000000 : ℝ), (-20267377/50000000 : ℝ), (730719433/2500000000 : ℝ)] ![(50086268161111/100000000000000 : ℝ), (30273645903061/100000000000000 : ℝ), (19640085925793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(741275849/1250000000 : ℝ)|^131 ≤ (50086268161111/100000000000000 : ℝ)^99
        have hw : |(741275849/1250000000 : ℝ)|=(741275849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20267377/50000000 : ℝ)|^131 ≤ (30273645903061/100000000000000 : ℝ)^99
        have hw : |(-20267377/50000000 : ℝ)|=(20267377/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(730719433/2500000000 : ℝ)|^131 ≤ (19640085925793/100000000000000 : ℝ)^99
        have hw : |(730719433/2500000000 : ℝ)|=(730719433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302069_s0_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-45924663/400000000 : ℝ)*x 0 + (-8457156791/10000000000 : ℝ)*x 1 + (2285544027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (45924663/400000000 : ℝ)^131 ≤ (2851760686899/50000000000000 : ℝ)^99 := by
    have hnat : (45924663 : ℕ)^131*50000000000000^99 ≤ 2851760686899^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45924663 400000000 2851760686899 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8457156791/10000000000 : ℝ)^131 ≤ (40056311394999/50000000000000 : ℝ)^99 := by
    have hnat : (8457156791 : ℕ)^131*50000000000000^99 ≤ 40056311394999^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8457156791 10000000000 40056311394999 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2285544027/10000000000 : ℝ)^131 ≤ (7091927912217/50000000000000 : ℝ)^99 := by
    have hnat : (2285544027 : ℕ)^131*50000000000000^99 ≤ 7091927912217^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285544027 10000000000 7091927912217 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-45924663/400000000 : ℝ), (-8457156791/10000000000 : ℝ), (2285544027/10000000000 : ℝ)] ![(2851760686899/50000000000000 : ℝ), (40056311394999/50000000000000 : ℝ), (7091927912217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-45924663/400000000 : ℝ)|^131 ≤ (2851760686899/50000000000000 : ℝ)^99
        have hw : |(-45924663/400000000 : ℝ)|=(45924663/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8457156791/10000000000 : ℝ)|^131 ≤ (40056311394999/50000000000000 : ℝ)^99
        have hw : |(-8457156791/10000000000 : ℝ)|=(8457156791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2285544027/10000000000 : ℝ)|^131 ≤ (7091927912217/50000000000000 : ℝ)^99
        have hw : |(2285544027/10000000000 : ℝ)|=(2285544027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302069_s0_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (222804987/312500000 : ℝ)*x 0 + (33319041/156250000 : ℝ)*x 1 + (206833191/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (222804987/312500000 : ℝ)^131 ≤ (12782445074799/20000000000000 : ℝ)^99 := by
    have hnat : (222804987 : ℕ)^131*20000000000000^99 ≤ 12782445074799^99*312500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222804987 312500000 12782445074799 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33319041/156250000 : ℝ)^131 ≤ (6470120357469/50000000000000 : ℝ)^99 := by
    have hnat : (33319041 : ℕ)^131*50000000000000^99 ≤ 6470120357469^99*156250000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33319041 156250000 6470120357469 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206833191/625000000 : ℝ)^131 ≤ (23147533900899/100000000000000 : ℝ)^99 := by
    have hnat : (206833191 : ℕ)^131*100000000000000^99 ≤ 23147533900899^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206833191 625000000 23147533900899 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(222804987/312500000 : ℝ), (33319041/156250000 : ℝ), (206833191/625000000 : ℝ)] ![(12782445074799/20000000000000 : ℝ), (6470120357469/50000000000000 : ℝ), (23147533900899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(222804987/312500000 : ℝ)|^131 ≤ (12782445074799/20000000000000 : ℝ)^99
        have hw : |(222804987/312500000 : ℝ)|=(222804987/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33319041/156250000 : ℝ)|^131 ≤ (6470120357469/50000000000000 : ℝ)^99
        have hw : |(33319041/156250000 : ℝ)|=(33319041/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(206833191/625000000 : ℝ)|^131 ≤ (23147533900899/100000000000000 : ℝ)^99
        have hw : |(206833191/625000000 : ℝ)|=(206833191/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302069_s0_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3169255291/10000000000 : ℝ)*x 0 + (-844284711/2500000000 : ℝ)*x 1 + (-6309004379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3169255291/10000000000 : ℝ)^131 ≤ (21860015632299/100000000000000 : ℝ)^99 := by
    have hnat : (3169255291 : ℕ)^131*100000000000000^99 ≤ 21860015632299^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3169255291 10000000000 21860015632299 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844284711/2500000000 : ℝ)^131 ≤ (4755439738787/20000000000000 : ℝ)^99 := by
    have hnat : (844284711 : ℕ)^131*20000000000000^99 ≤ 4755439738787^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844284711 2500000000 4755439738787 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6309004379/10000000000 : ℝ)^131 ≤ (54362785666099/100000000000000 : ℝ)^99 := by
    have hnat : (6309004379 : ℕ)^131*100000000000000^99 ≤ 54362785666099^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6309004379 10000000000 54362785666099 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3169255291/10000000000 : ℝ), (-844284711/2500000000 : ℝ), (-6309004379/10000000000 : ℝ)] ![(21860015632299/100000000000000 : ℝ), (4755439738787/20000000000000 : ℝ), (54362785666099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3169255291/10000000000 : ℝ)|^131 ≤ (21860015632299/100000000000000 : ℝ)^99
        have hw : |(3169255291/10000000000 : ℝ)|=(3169255291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-844284711/2500000000 : ℝ)|^131 ≤ (4755439738787/20000000000000 : ℝ)^99
        have hw : |(-844284711/2500000000 : ℝ)|=(844284711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6309004379/10000000000 : ℝ)|^131 ≤ (54362785666099/100000000000000 : ℝ)^99
        have hw : |(-6309004379/10000000000 : ℝ)|=(6309004379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302069_s1_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-42374727/125000000 : ℝ)*x 0 + (-2769322299/5000000000 : ℝ)*x 1 + (4060745453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42374727/125000000 : ℝ)^131 ≤ (5974222065263/25000000000000 : ℝ)^99 := by
    have hnat : (42374727 : ℕ)^131*25000000000000^99 ≤ 5974222065263^99*125000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42374727 125000000 5974222065263 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2769322299/5000000000 : ℝ)^131 ≤ (22878798815167/50000000000000 : ℝ)^99 := by
    have hnat : (2769322299 : ℕ)^131*50000000000000^99 ≤ 22878798815167^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2769322299 5000000000 22878798815167 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4060745453/10000000000 : ℝ)^131 ≤ (94829731527/312500000000 : ℝ)^99 := by
    have hnat : (4060745453 : ℕ)^131*312500000000^99 ≤ 94829731527^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4060745453 10000000000 94829731527 312500000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42374727/125000000 : ℝ), (-2769322299/5000000000 : ℝ), (4060745453/10000000000 : ℝ)] ![(5974222065263/25000000000000 : ℝ), (22878798815167/50000000000000 : ℝ), (94829731527/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42374727/125000000 : ℝ)|^131 ≤ (5974222065263/25000000000000 : ℝ)^99
        have hw : |(-42374727/125000000 : ℝ)|=(42374727/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2769322299/5000000000 : ℝ)|^131 ≤ (22878798815167/50000000000000 : ℝ)^99
        have hw : |(-2769322299/5000000000 : ℝ)|=(2769322299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4060745453/10000000000 : ℝ)|^131 ≤ (94829731527/312500000000 : ℝ)^99
        have hw : |(4060745453/10000000000 : ℝ)|=(4060745453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302069_s1_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5268316547/10000000000 : ℝ)*x 0 + (3493210619/10000000000 : ℝ)*x 1 + (4257831767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5268316547/10000000000 : ℝ)^131 ≤ (42825970243233/100000000000000 : ℝ)^99 := by
    have hnat : (5268316547 : ℕ)^131*100000000000000^99 ≤ 42825970243233^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268316547 10000000000 42825970243233 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3493210619/10000000000 : ℝ)^131 ≤ (24864529944733/100000000000000 : ℝ)^99 := by
    have hnat : (3493210619 : ℕ)^131*100000000000000^99 ≤ 24864529944733^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3493210619 10000000000 24864529944733 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4257831767/10000000000 : ℝ)^131 ≤ (252417967183/781250000000 : ℝ)^99 := by
    have hnat : (4257831767 : ℕ)^131*781250000000^99 ≤ 252417967183^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257831767 10000000000 252417967183 781250000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5268316547/10000000000 : ℝ), (3493210619/10000000000 : ℝ), (4257831767/10000000000 : ℝ)] ![(42825970243233/100000000000000 : ℝ), (24864529944733/100000000000000 : ℝ), (252417967183/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5268316547/10000000000 : ℝ)|^131 ≤ (42825970243233/100000000000000 : ℝ)^99
        have hw : |(5268316547/10000000000 : ℝ)|=(5268316547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3493210619/10000000000 : ℝ)|^131 ≤ (24864529944733/100000000000000 : ℝ)^99
        have hw : |(3493210619/10000000000 : ℝ)|=(3493210619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4257831767/10000000000 : ℝ)|^131 ≤ (252417967183/781250000000 : ℝ)^99
        have hw : |(4257831767/10000000000 : ℝ)|=(4257831767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302069_s1_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4115478291/10000000000 : ℝ)*x 0 + (-1003623747/2500000000 : ℝ)*x 1 + (-4929798649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4115478291/10000000000 : ℝ)^131 ≤ (772197704887/2500000000000 : ℝ)^99 := by
    have hnat : (4115478291 : ℕ)^131*2500000000000^99 ≤ 772197704887^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4115478291 10000000000 772197704887 2500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003623747/2500000000 : ℝ)^131 ≤ (29889016272059/100000000000000 : ℝ)^99 := by
    have hnat : (1003623747 : ℕ)^131*100000000000000^99 ≤ 29889016272059^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003623747 2500000000 29889016272059 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4929798649/10000000000 : ℝ)^131 ≤ (39223075523221/100000000000000 : ℝ)^99 := by
    have hnat : (4929798649 : ℕ)^131*100000000000000^99 ≤ 39223075523221^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4929798649 10000000000 39223075523221 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4115478291/10000000000 : ℝ), (-1003623747/2500000000 : ℝ), (-4929798649/10000000000 : ℝ)] ![(772197704887/2500000000000 : ℝ), (29889016272059/100000000000000 : ℝ), (39223075523221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4115478291/10000000000 : ℝ)|^131 ≤ (772197704887/2500000000000 : ℝ)^99
        have hw : |(4115478291/10000000000 : ℝ)|=(4115478291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1003623747/2500000000 : ℝ)|^131 ≤ (29889016272059/100000000000000 : ℝ)^99
        have hw : |(-1003623747/2500000000 : ℝ)|=(1003623747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4929798649/10000000000 : ℝ)|^131 ≤ (39223075523221/100000000000000 : ℝ)^99
        have hw : |(-4929798649/10000000000 : ℝ)|=(4929798649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302069_s1_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (302584177/625000000 : ℝ)*x 0 + (-1077010087/2500000000 : ℝ)*x 1 + (3912756599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (302584177/625000000 : ℝ)^131 ≤ (19147280189693/50000000000000 : ℝ)^99 := by
    have hnat : (302584177 : ℕ)^131*50000000000000^99 ≤ 19147280189693^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302584177 625000000 19147280189693 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077010087/2500000000 : ℝ)^131 ≤ (16407301711027/50000000000000 : ℝ)^99 := by
    have hnat : (1077010087 : ℕ)^131*50000000000000^99 ≤ 16407301711027^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077010087 2500000000 16407301711027 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3912756599/10000000000 : ℝ)^131 ≤ (28890836185467/100000000000000 : ℝ)^99 := by
    have hnat : (3912756599 : ℕ)^131*100000000000000^99 ≤ 28890836185467^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3912756599 10000000000 28890836185467 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(302584177/625000000 : ℝ), (-1077010087/2500000000 : ℝ), (3912756599/10000000000 : ℝ)] ![(19147280189693/50000000000000 : ℝ), (16407301711027/50000000000000 : ℝ), (28890836185467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(302584177/625000000 : ℝ)|^131 ≤ (19147280189693/50000000000000 : ℝ)^99
        have hw : |(302584177/625000000 : ℝ)|=(302584177/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1077010087/2500000000 : ℝ)|^131 ≤ (16407301711027/50000000000000 : ℝ)^99
        have hw : |(-1077010087/2500000000 : ℝ)|=(1077010087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3912756599/10000000000 : ℝ)|^131 ≤ (28890836185467/100000000000000 : ℝ)^99
        have hw : |(3912756599/10000000000 : ℝ)|=(3912756599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302069 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1244837943679337/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1860409697374323/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (65/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^65 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^65*1^16 ≤ 1^16*1^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11860409697374323/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11860409697374323/10000000000000000 : ℝ)^65 := by
      have hnat : (2 : ℕ)^16*10000000000000000^65 ≤ 11860409697374323^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11860409697374323 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11860409697374323/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (655262382052683/500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (655262382052683/500000000000000 : ℝ)^65 := by
      have hnat : (3 : ℕ)^16*500000000000000^65 ≤ 655262382052683^65*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 655262382052683 500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (655262382052683/500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1860409697374323/10000000000000000 : ℝ)) (beta := (1244837943679337/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1860409697374323/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1244837943679337/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-2022446223/10000000000 : ℝ)*X 0 0+(-7553603811/10000000000 : ℝ)*X 0 1+(2844697837/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302069_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1423856201/10000000000 : ℝ)*X 0 0+(-264286143/312500000 : ℝ)*X 0 1+(256593811/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302069_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((175551019/312500000 : ℝ)*X 1 0+(338606333/1250000000 : ℝ)*X 1 1+(4583271027/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302069_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1056925563/2500000000 : ℝ)*X 2 0+(-7843999/31250000 : ℝ)*X 2 1+(-1523752513/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302069_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((-2447857513/10000000000 : ℝ)*X 0 0+(-187391533/250000000 : ℝ)*X 0 1+(315586719/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302069_s0_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((741275849/1250000000 : ℝ)*X 1 0+(123246431/500000000 : ℝ)*X 1 1+(556071219/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302069_s0_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1836932133/5000000000 : ℝ)*X 2 0+(-3114013901/10000000000 : ℝ)*X 2 1+(-6106208947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302069_s0_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_19 : ((741275849/1250000000 : ℝ)*X 0 0+(-20267377/50000000 : ℝ)*X 0 1+(730719433/2500000000 : ℝ)*X 0 2+(741275849/1250000000 : ℝ)*X 1 0+(-20267377/50000000 : ℝ)*X 1 1+(730719433/2500000000 : ℝ)*X 1 2+(741275849/1250000000 : ℝ)*X 2 0+(-20267377/50000000 : ℝ)*X 2 1+(730719433/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302069_s0_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-45924663/400000000 : ℝ)*X 0 0+(-8457156791/10000000000 : ℝ)*X 0 1+(2285544027/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302069_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((222804987/312500000 : ℝ)*X 1 0+(33319041/156250000 : ℝ)*X 1 1+(206833191/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302069_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3169255291/10000000000 : ℝ)*X 2 0+(-844284711/2500000000 : ℝ)*X 2 1+(-6309004379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302069_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((2869/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2869/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4703450712334626736851/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (153823293519/62500000000 : ℝ)*(base3) + (763013576783/1000000000000 : ℝ)*(base40) + (726827687427/250000000000 : ℝ)*(base49) + (99312987333/50000000000 : ℝ)*(base50) + (296539/50000000000 : ℝ)*(base60) + (917832827769/250000000000 : ℝ)*(major_s0_0) + (917832827769/250000000000 : ℝ)*(major_s0_1) + (917832827769/250000000000 : ℝ)*(major_s0_2) + (17569071/1000000000000 : ℝ)*(sp_s0_0) + (488124899943/100000000000 : ℝ)*(sp_s0_7) + (1835664401283/250000000000 : ℝ)*(sp_s0_8) + (1220337741913/250000000000 : ℝ)*(sp_s0_9) + (16742647/125000000000 : ℝ)*(sp_s0_15) + (218340327/1000000000000 : ℝ)*(sp_s0_20) + (153823293519/62500000000 : ℝ)*(f.failure) + (1220371227207/250000000000 : ℝ)*(f.sum) + (1559793365566883/1250000000000000000000000000 : ℝ)*base62 + (417215905609153/2500000000000000000000000000 : ℝ)*base64 + (569561894024613/2500000000000000000000000000 : ℝ)*base67 + (2233422482024613/2500000000000000000000000000 : ℝ)*base68 + (262813607566883/1250000000000000000000000000 : ℝ)*base70 + (1822488755890847/2500000000000000000000000000 : ℝ)*base72 + (2601031165109153/2500000000000000000000000000 : ℝ)*base74 + (1345113315975387/2500000000000000000000000000 : ℝ)*base77 + (220530098566883/1250000000000000000000000000 : ℝ)*base79 + (423/625000000000000 : ℝ)*base87 + (423/625000000000000 : ℝ)*base89 + (423/625000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-7067/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-7067/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18356803271714343807567/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1046939038583/1000000000000 : ℝ)*(base3) + (419741/40000000000 : ℝ)*(base39) + (334396804943/500000000000 : ℝ)*(base40) + (118999292211/200000000000 : ℝ)*(base49) + (614532869321/250000000000 : ℝ)*(major_s0_0) + (614532869321/250000000000 : ℝ)*(major_s0_1) + (614532869321/250000000000 : ℝ)*(major_s0_2) + (173381787/1000000000000 : ℝ)*(sp_s0_0) + (99411487/500000000000 : ℝ)*(sp_s0_9) + (3268212131349/1000000000000 : ℝ)*(sp_s0_13) + (215765415807/50000000000 : ℝ)*(sp_s0_14) + (3268186690161/1000000000000 : ℝ)*(sp_s0_15) + (37558344231/62500000000 : ℝ)*(sp_s0_19) + (8117789/500000000000 : ℝ)*(sp_s0_21) + (1647872546279/1000000000000 : ℝ)*(f.failure) + (204274094571/62500000000 : ℝ)*(f.sum) + (499666746287747/1250000000000000000000000000 : ℝ)*base62 + (70284785329823/2500000000000000000000000000 : ℝ)*base65 + (152319110405317/2500000000000000000000000000 : ℝ)*base67 + (1415499563844683/2500000000000000000000000000 : ℝ)*base69 + (48416418537747/1250000000000000000000000000 : ℝ)*base70 + (2857879268920177/2500000000000000000000000000 : ℝ)*base73 + (222563574579823/2500000000000000000000000000 : ℝ)*base75 + (1710213324905317/2500000000000000000000000000 : ℝ)*base76 + (83257239912747/1250000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (3843/10000000000000000 : ℝ)*base87 + (3843/10000000000000000 : ℝ)*base89 + (3843/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(509/1250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(509/1250 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (37586020255556733/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (558854242729/200000000000 : ℝ)*(base3) + (2044103/1000000000000 : ℝ)*(base22) + (152109162141/100000000000 : ℝ)*(base40) + (3611764018193/1000000000000 : ℝ)*(base49) + (859437362311/500000000000 : ℝ)*(base50) + (833643671831/200000000000 : ℝ)*(major_s0_0) + (833643671831/200000000000 : ℝ)*(major_s0_1) + (833643671831/200000000000 : ℝ)*(major_s0_2) + (82451/250000000000 : ℝ)*(sp_s0_0) + (8506333/100000000000 : ℝ)*(sp_s0_7) + (33433/12500000000 : ℝ)*(sp_s0_19) + (1108415236803/200000000000 : ℝ)*(sp_s0_20) + (4168216395397/500000000000 : ℝ)*(sp_s0_21) + (1108431906609/200000000000 : ℝ)*(sp_s0_22) + (558854777657/200000000000 : ℝ)*(f.failure) + (1385540394287/250000000000 : ℝ)*(f.sum) + (848991336230317/1000000000000000000000000000 : ℝ)*base62 + (2346723874143953/2000000000000000000000000000 : ℝ)*base65 + (135562152395413/2000000000000000000000000000 : ℝ)*base66 + (1606379537404587/2000000000000000000000000000 : ℝ)*base68 + (270286181469683/1000000000000000000000000000 : ℝ)*base71 + (2012368265143953/2000000000000000000000000000 : ℝ)*base72 + (2844023918656047/2000000000000000000000000000 : ℝ)*base74 + (853136573795413/2000000000000000000000000000 : ℝ)*base77 + (312273430430317/1000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (531/2000000000000000 : ℝ)*base86 + (531/2000000000000000 : ℝ)*base88 + (531/2000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (2869/12500 : ℝ) ^ (65/16 : ℝ) ≤ (63281014509802609/25000000000000000000 : ℝ) := by
    have hpowers : (2869/12500 : ℝ)^65 ≤ (63281014509802609/25000000000000000000 : ℝ)^16 := by
      have hnat : (2869 : ℕ)^65*25000000000000000000^16 ≤ 63281014509802609^16*12500^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2869 12500 63281014509802609 25000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2869/12500 : ℝ)) (X := (63281014509802609/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (25063281014509802609/25000000000000000000 : ℝ) ≤ (10006224810176843/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (25063281014509802609/25000000000000000000 : ℝ)^16 ≤ (10006224810176843/10000000000000000 : ℝ)^65 := by
      have hnat : (25063281014509802609 : ℕ)^16*10000000000000000^65 ≤ 10006224810176843^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25063281014509802609 25000000000000000000 10006224810176843 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006224810176843/10000000000000000 : ℝ)) (X := (25063281014509802609/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (12563281014509802609/12500000000000000000 : ℝ) ≤ (2002487556724751/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (12563281014509802609/12500000000000000000 : ℝ)^16 ≤ (2002487556724751/2000000000000000 : ℝ)^65 := by
      have hnat : (12563281014509802609 : ℕ)^16*2000000000000000^65 ≤ 2002487556724751^65*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12563281014509802609 12500000000000000000 2002487556724751 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002487556724751/2000000000000000 : ℝ)) (X := (12563281014509802609/12500000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(6224810176843/2295200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(24269427527/8965625000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (2869/12500 : ℝ)) (alpha := (6224810176843/2295200000000000 : ℝ)) (beta := (24269427527/8965625000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2869/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(6224810176843/2295200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(24269427527/8965625000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (7067/100000 : ℝ) ^ (65/16 : ℝ) ≤ (2113574489634653/100000000000000000000 : ℝ) := by
    have hpowers : (7067/100000 : ℝ)^65 ≤ (2113574489634653/100000000000000000000 : ℝ)^16 := by
      have hnat : (7067 : ℕ)^65*100000000000000000000^16 ≤ 2113574489634653^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7067 100000 2113574489634653 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7067/100000 : ℝ)) (X := (2113574489634653/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (100002113574489634653/100000000000000000000 : ℝ) ≤ (1000005202603451/1000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (100002113574489634653/100000000000000000000 : ℝ)^16 ≤ (1000005202603451/1000000000000000 : ℝ)^65 := by
      have hnat : (100002113574489634653 : ℕ)^16*1000000000000000^65 ≤ 1000005202603451^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100002113574489634653 100000000000000000000 1000005202603451 1000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000005202603451/1000000000000000 : ℝ)) (X := (100002113574489634653/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (50002113574489634653/50000000000000000000 : ℝ) ≤ (10000104051240107/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (50002113574489634653/50000000000000000000 : ℝ)^16 ≤ (10000104051240107/10000000000000000 : ℝ)^65 := by
      have hnat : (50002113574489634653 : ℕ)^16*10000000000000000^65 ≤ 10000104051240107^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002113574489634653 50000000000000000000 10000104051240107 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000104051240107/10000000000000000 : ℝ)) (X := (50002113574489634653/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(5202603451/70670000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(52025205597/706700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (7067/100000 : ℝ)) (alpha := (5202603451/70670000000000 : ℝ)) (beta := (52025205597/706700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (7067/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(5202603451/70670000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(52025205597/706700000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (509/1250 : ℝ) ^ (65/16 : ℝ) ≤ (2599226121501050799/100000000000000000000 : ℝ) := by
    have hpowers : (509/1250 : ℝ)^65 ≤ (2599226121501050799/100000000000000000000 : ℝ)^16 := by
      have hnat : (509 : ℕ)^65*100000000000000000000^16 ≤ 2599226121501050799^16*1250^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        509 1250 2599226121501050799 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (509/1250 : ℝ)) (X := (2599226121501050799/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (102599226121501050799/100000000000000000000 : ℝ) ≤ (10063363481737469/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (102599226121501050799/100000000000000000000 : ℝ)^16 ≤ (10063363481737469/10000000000000000 : ℝ)^65 := by
      have hnat : (102599226121501050799 : ℕ)^16*10000000000000000^65 ≤ 10063363481737469^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102599226121501050799 100000000000000000000 10063363481737469 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10063363481737469/10000000000000000 : ℝ)) (X := (102599226121501050799/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (52599226121501050799/50000000000000000000 : ℝ) ≤ (632845510571979/625000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (52599226121501050799/50000000000000000000 : ℝ)^16 ≤ (632845510571979/625000000000000 : ℝ)^65 := by
      have hnat : (52599226121501050799 : ℕ)^16*625000000000000^65 ≤ 632845510571979^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52599226121501050799 50000000000000000000 632845510571979 625000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (632845510571979/625000000000000 : ℝ)) (X := (52599226121501050799/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(63363481737469/4072000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(12432937482839/814400000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (509/1250 : ℝ)) (alpha := (63363481737469/4072000000000000 : ℝ)) (beta := (12432937482839/814400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (509/1250 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(63363481737469/4072000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(12432937482839/814400000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-42374727/125000000 : ℝ)*X 0 0+(-2769322299/5000000000 : ℝ)*X 0 1+(4060745453/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302069_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5268316547/10000000000 : ℝ)*X 1 0+(3493210619/10000000000 : ℝ)*X 1 1+(4257831767/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302069_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4115478291/10000000000 : ℝ)*X 2 0+(-1003623747/2500000000 : ℝ)*X 2 1+(-4929798649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302069_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((302584177/625000000 : ℝ)*X 0 0+(-1077010087/2500000000 : ℝ)*X 0 1+(3912756599/10000000000 : ℝ)*X 0 2+(302584177/625000000 : ℝ)*X 1 0+(-1077010087/2500000000 : ℝ)*X 1 1+(3912756599/10000000000 : ℝ)*X 1 2+(302584177/625000000 : ℝ)*X 2 0+(-1077010087/2500000000 : ℝ)*X 2 1+(3912756599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302069_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-29751/5000 : ℝ) < ((-14917/10000 : ℝ)*P 0+(-14917/10000 : ℝ)*P 1+(-14917/10000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-29751/5000 : ℝ) < (-151439043018311402839009095113967/25800221267500000000000000000000 : ℝ) := by norm_num
    linear_combination (1448111/1000000000000 : ℝ)*(base3) + (361017/500000000000 : ℝ)*(base21) + (814161/1000000000000 : ℝ)*(base24) + (8480996939/31250000000 : ℝ)*(base40) + (254022026303/500000000000 : ℝ)*(base49) + (152902938337/500000000000 : ℝ)*(base50) + (98619/250000000000 : ℝ)*(base60) + (36739/100000000000 : ℝ)*(ratio_s0_0) + (14917/10000 : ℝ)*(major_s1_0) + (14917/10000 : ℝ)*(major_s1_1) + (14917/10000 : ℝ)*(major_s1_2) + (1956560003213/1000000000000 : ℝ)*(sp_s1_0) + (489140362831/250000000000 : ℝ)*(sp_s1_1) + (978279233509/500000000000 : ℝ)*(sp_s1_2) + (999998551889/1000000000000 : ℝ)*(sp_s1_6) + (1956560003213/1000000000000 : ℝ)*(f.sum) + (3320039396036313/4496378750000000000000000000 : ℝ)*base62 + (223819052643/2545000000000000000000000 : ℝ)*base64 + (7171628501/35335000000000000000000 : ℝ)*base66 + (717946006971/1272500000000000000000000 : ℝ)*base68 + (17049873670123/456350312500000000000000000 : ℝ)*base71 + (332144770489/28690000000000000000000000 : ℝ)*base73 + (21434753709181/35335000000000000000000000 : ℝ)*base74 + (2119105071141/7172500000000000000000000 : ℝ)*base77 + (17615802492902133/202752230000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p002_b028 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (c : Fin 88) (hlo : 69 ≤ c.val) (hhi : c.val < 70)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=69 := by omega
  rcases hc with rfl
  · exact collision_c302069 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (c : Fin 88) (hlo : 69 ≤ c.val) (hhi : c.val < 70)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p002_b028 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

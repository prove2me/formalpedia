-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p015_b025
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:54:28.960823+00:00
-- url     : https://prove2.me/submissions/d2e9aa23-7eff-41a4-8fbf-b9c40ee5ee2d

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
theorem collision_support_c315064_s0_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3094493107/10000000000 : ℝ)*x 0 + (-458030581/1250000000 : ℝ)*x 1 + (-5724343173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3094493107/10000000000 : ℝ)^19 ≤ (22633239803057/100000000000000 : ℝ)^15 := by
    have hnat : (3094493107 : ℕ)^19*100000000000000^15 ≤ 22633239803057^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3094493107 10000000000 22633239803057 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458030581/1250000000 : ℝ)^19 ≤ (14017922559681/50000000000000 : ℝ)^15 := by
    have hnat : (458030581 : ℕ)^19*50000000000000^15 ≤ 14017922559681^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458030581 1250000000 14017922559681 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5724343173/10000000000 : ℝ)^19 ≤ (24665457533459/50000000000000 : ℝ)^15 := by
    have hnat : (5724343173 : ℕ)^19*50000000000000^15 ≤ 24665457533459^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5724343173 10000000000 24665457533459 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3094493107/10000000000 : ℝ), (-458030581/1250000000 : ℝ), (-5724343173/10000000000 : ℝ)] ![(22633239803057/100000000000000 : ℝ), (14017922559681/50000000000000 : ℝ), (24665457533459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3094493107/10000000000 : ℝ)|^19 ≤ (22633239803057/100000000000000 : ℝ)^15
        have hw : |(-3094493107/10000000000 : ℝ)|=(3094493107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-458030581/1250000000 : ℝ)|^19 ≤ (14017922559681/50000000000000 : ℝ)^15
        have hw : |(-458030581/1250000000 : ℝ)|=(458030581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5724343173/10000000000 : ℝ)|^19 ≤ (24665457533459/50000000000000 : ℝ)^15
        have hw : |(-5724343173/10000000000 : ℝ)|=(5724343173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315064_s0_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (427764567/1250000000 : ℝ)*x 0 + (5456461207/10000000000 : ℝ)*x 1 + (-3646553137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427764567/1250000000 : ℝ)^19 ≤ (3213784509543/12500000000000 : ℝ)^15 := by
    have hnat : (427764567 : ℕ)^19*12500000000000^15 ≤ 3213784509543^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427764567 1250000000 3213784509543 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456461207/10000000000 : ℝ)^19 ≤ (11606306442241/25000000000000 : ℝ)^15 := by
    have hnat : (5456461207 : ℕ)^19*25000000000000^15 ≤ 11606306442241^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456461207 10000000000 11606306442241 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3646553137/10000000000 : ℝ)^19 ≤ (27864498137383/100000000000000 : ℝ)^15 := by
    have hnat : (3646553137 : ℕ)^19*100000000000000^15 ≤ 27864498137383^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3646553137 10000000000 27864498137383 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(427764567/1250000000 : ℝ), (5456461207/10000000000 : ℝ), (-3646553137/10000000000 : ℝ)] ![(3213784509543/12500000000000 : ℝ), (11606306442241/25000000000000 : ℝ), (27864498137383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(427764567/1250000000 : ℝ)|^19 ≤ (3213784509543/12500000000000 : ℝ)^15
        have hw : |(427764567/1250000000 : ℝ)|=(427764567/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456461207/10000000000 : ℝ)|^19 ≤ (11606306442241/25000000000000 : ℝ)^15
        have hw : |(5456461207/10000000000 : ℝ)|=(5456461207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3646553137/10000000000 : ℝ)|^19 ≤ (27864498137383/100000000000000 : ℝ)^15
        have hw : |(-3646553137/10000000000 : ℝ)|=(3646553137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315064_s0_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3204559917/5000000000 : ℝ)*x 0 + (-354867381/1000000000 : ℝ)*x 1 + (118578939/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3204559917/5000000000 : ℝ)^19 ≤ (56921713229803/100000000000000 : ℝ)^15 := by
    have hnat : (3204559917 : ℕ)^19*100000000000000^15 ≤ 56921713229803^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3204559917 5000000000 56921713229803 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (354867381/1000000000 : ℝ)^19 ≤ (13460268012001/50000000000000 : ℝ)^15 := by
    have hnat : (354867381 : ℕ)^19*50000000000000^15 ≤ 13460268012001^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354867381 1000000000 13460268012001 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118578939/500000000 : ℝ)^19 ≤ (2019718841841/12500000000000 : ℝ)^15 := by
    have hnat : (118578939 : ℕ)^19*12500000000000^15 ≤ 2019718841841^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118578939 500000000 2019718841841 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3204559917/5000000000 : ℝ), (-354867381/1000000000 : ℝ), (118578939/500000000 : ℝ)] ![(56921713229803/100000000000000 : ℝ), (13460268012001/50000000000000 : ℝ), (2019718841841/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3204559917/5000000000 : ℝ)|^19 ≤ (56921713229803/100000000000000 : ℝ)^15
        have hw : |(3204559917/5000000000 : ℝ)|=(3204559917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-354867381/1000000000 : ℝ)|^19 ≤ (13460268012001/50000000000000 : ℝ)^15
        have hw : |(-354867381/1000000000 : ℝ)|=(354867381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(118578939/500000000 : ℝ)|^19 ≤ (2019718841841/12500000000000 : ℝ)^15
        have hw : |(118578939/500000000 : ℝ)|=(118578939/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315064_s0_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-307846647/1000000000 : ℝ)*x 0 + (-91997499/250000000 : ℝ)*x 1 + (-5724028517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (307846647/1000000000 : ℝ)^19 ≤ (22484864518973/100000000000000 : ℝ)^15 := by
    have hnat : (307846647 : ℕ)^19*100000000000000^15 ≤ 22484864518973^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307846647 1000000000 22484864518973 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91997499/250000000 : ℝ)^19 ≤ (5637531020443/20000000000000 : ℝ)^15 := by
    have hnat : (91997499 : ℕ)^19*20000000000000^15 ≤ 5637531020443^15*250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91997499 250000000 5637531020443 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5724028517/10000000000 : ℝ)^19 ≤ (24663740183949/50000000000000 : ℝ)^15 := by
    have hnat : (5724028517 : ℕ)^19*50000000000000^15 ≤ 24663740183949^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5724028517 10000000000 24663740183949 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-307846647/1000000000 : ℝ), (-91997499/250000000 : ℝ), (-5724028517/10000000000 : ℝ)] ![(22484864518973/100000000000000 : ℝ), (5637531020443/20000000000000 : ℝ), (24663740183949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-307846647/1000000000 : ℝ)|^19 ≤ (22484864518973/100000000000000 : ℝ)^15
        have hw : |(-307846647/1000000000 : ℝ)|=(307846647/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-91997499/250000000 : ℝ)|^19 ≤ (5637531020443/20000000000000 : ℝ)^15
        have hw : |(-91997499/250000000 : ℝ)|=(91997499/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5724028517/10000000000 : ℝ)|^19 ≤ (24663740183949/50000000000000 : ℝ)^15
        have hw : |(-5724028517/10000000000 : ℝ)|=(5724028517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315064_s0_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3415798179/10000000000 : ℝ)*x 0 + (2776924037/5000000000 : ℝ)*x 1 + (-3543680961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3415798179/10000000000 : ℝ)^19 ≤ (12825081325661/50000000000000 : ℝ)^15 := by
    have hnat : (3415798179 : ℕ)^19*50000000000000^15 ≤ 12825081325661^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3415798179 10000000000 12825081325661 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2776924037/5000000000 : ℝ)^19 ≤ (47477268794933/100000000000000 : ℝ)^15 := by
    have hnat : (2776924037 : ℕ)^19*100000000000000^15 ≤ 47477268794933^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2776924037 5000000000 47477268794933 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3543680961/10000000000 : ℝ)^19 ≤ (26872568545649/100000000000000 : ℝ)^15 := by
    have hnat : (3543680961 : ℕ)^19*100000000000000^15 ≤ 26872568545649^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3543680961 10000000000 26872568545649 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3415798179/10000000000 : ℝ), (2776924037/5000000000 : ℝ), (-3543680961/10000000000 : ℝ)] ![(12825081325661/50000000000000 : ℝ), (47477268794933/100000000000000 : ℝ), (26872568545649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3415798179/10000000000 : ℝ)|^19 ≤ (12825081325661/50000000000000 : ℝ)^15
        have hw : |(3415798179/10000000000 : ℝ)|=(3415798179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2776924037/5000000000 : ℝ)|^19 ≤ (47477268794933/100000000000000 : ℝ)^15
        have hw : |(2776924037/5000000000 : ℝ)|=(2776924037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3543680961/10000000000 : ℝ)|^19 ≤ (26872568545649/100000000000000 : ℝ)^15
        have hw : |(-3543680961/10000000000 : ℝ)|=(3543680961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315064_s0_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1277994491/2000000000 : ℝ)*x 0 + (-3459094359/10000000000 : ℝ)*x 1 + (2495087197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1277994491/2000000000 : ℝ)^19 ≤ (3544149771477/6250000000000 : ℝ)^15 := by
    have hnat : (1277994491 : ℕ)^19*6250000000000^15 ≤ 3544149771477^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1277994491 2000000000 3544149771477 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3459094359/10000000000 : ℝ)^19 ≤ (3257834848189/12500000000000 : ℝ)^15 := by
    have hnat : (3459094359 : ℕ)^19*12500000000000^15 ≤ 3257834848189^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3459094359 10000000000 3257834848189 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2495087197/10000000000 : ℝ)^19 ≤ (17230924854663/100000000000000 : ℝ)^15 := by
    have hnat : (2495087197 : ℕ)^19*100000000000000^15 ≤ 17230924854663^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495087197 10000000000 17230924854663 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1277994491/2000000000 : ℝ), (-3459094359/10000000000 : ℝ), (2495087197/10000000000 : ℝ)] ![(3544149771477/6250000000000 : ℝ), (3257834848189/12500000000000 : ℝ), (17230924854663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1277994491/2000000000 : ℝ)|^19 ≤ (3544149771477/6250000000000 : ℝ)^15
        have hw : |(1277994491/2000000000 : ℝ)|=(1277994491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3459094359/10000000000 : ℝ)|^19 ≤ (3257834848189/12500000000000 : ℝ)^15
        have hw : |(-3459094359/10000000000 : ℝ)|=(3459094359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2495087197/10000000000 : ℝ)|^19 ≤ (17230924854663/100000000000000 : ℝ)^15
        have hw : |(2495087197/10000000000 : ℝ)|=(2495087197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315064_s0_10 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (9999999977/10000000000 : ℝ)*x 0 + (1817/10000000000 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9999999977/10000000000 : ℝ)^19 ≤ (99999999708667/100000000000000 : ℝ)^15 := by
    have hnat : (9999999977 : ℕ)^19*100000000000000^15 ≤ 99999999708667^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9999999977 10000000000 99999999708667 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1817/10000000000 : ℝ)^19 ≤ (57927/20000000000000 : ℝ)^15 := by
    have hnat : (1817 : ℕ)^19*20000000000000^15 ≤ 57927^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1817 10000000000 57927 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^19 ≤ (0 : ℝ)^15 := by
    have hnat : (0 : ℕ)^19*1^15 ≤ 0^15*1^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9999999977/10000000000 : ℝ), (1817/10000000000 : ℝ), (0 : ℝ)] ![(99999999708667/100000000000000 : ℝ), (57927/20000000000000 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9999999977/10000000000 : ℝ)|^19 ≤ (99999999708667/100000000000000 : ℝ)^15
        have hw : |(9999999977/10000000000 : ℝ)|=(9999999977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1817/10000000000 : ℝ)|^19 ≤ (57927/20000000000000 : ℝ)^15
        have hw : |(1817/10000000000 : ℝ)|=(1817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^19 ≤ (0 : ℝ)^15
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315064_s0_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2876709337/10000000000 : ℝ)*x 0 + (-814932793/2500000000 : ℝ)*x 1 + (-390919599/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2876709337/10000000000 : ℝ)^19 ≤ (20634862456847/100000000000000 : ℝ)^15 := by
    have hnat : (2876709337 : ℕ)^19*100000000000000^15 ≤ 20634862456847^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2876709337 10000000000 20634862456847 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (814932793/2500000000 : ℝ)^19 ≤ (24174839255281/100000000000000 : ℝ)^15 := by
    have hnat : (814932793 : ℕ)^19*100000000000000^15 ≤ 24174839255281^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814932793 2500000000 24174839255281 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (390919599/625000000 : ℝ)^19 ≤ (55190298273577/100000000000000 : ℝ)^15 := by
    have hnat : (390919599 : ℕ)^19*100000000000000^15 ≤ 55190298273577^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      390919599 625000000 55190298273577 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2876709337/10000000000 : ℝ), (-814932793/2500000000 : ℝ), (-390919599/625000000 : ℝ)] ![(20634862456847/100000000000000 : ℝ), (24174839255281/100000000000000 : ℝ), (55190298273577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2876709337/10000000000 : ℝ)|^19 ≤ (20634862456847/100000000000000 : ℝ)^15
        have hw : |(-2876709337/10000000000 : ℝ)|=(2876709337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-814932793/2500000000 : ℝ)|^19 ≤ (24174839255281/100000000000000 : ℝ)^15
        have hw : |(-814932793/2500000000 : ℝ)|=(814932793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-390919599/625000000 : ℝ)|^19 ≤ (55190298273577/100000000000000 : ℝ)^15
        have hw : |(-390919599/625000000 : ℝ)|=(390919599/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315064_s0_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (482193807/1250000000 : ℝ)*x 0 + (5387643933/10000000000 : ℝ)*x 1 + (-1641461029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (482193807/1250000000 : ℝ)^19 ≤ (29922282073599/100000000000000 : ℝ)^15 := by
    have hnat : (482193807 : ℕ)^19*100000000000000^15 ≤ 29922282073599^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482193807 1250000000 29922282073599 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5387643933/10000000000 : ℝ)^19 ≤ (45684820392829/100000000000000 : ℝ)^15 := by
    have hnat : (5387643933 : ℕ)^19*100000000000000^15 ≤ 45684820392829^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387643933 10000000000 45684820392829 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1641461029/5000000000 : ℝ)^19 ≤ (12196448758809/50000000000000 : ℝ)^15 := by
    have hnat : (1641461029 : ℕ)^19*50000000000000^15 ≤ 12196448758809^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1641461029 5000000000 12196448758809 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(482193807/1250000000 : ℝ), (5387643933/10000000000 : ℝ), (-1641461029/5000000000 : ℝ)] ![(29922282073599/100000000000000 : ℝ), (45684820392829/100000000000000 : ℝ), (12196448758809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(482193807/1250000000 : ℝ)|^19 ≤ (29922282073599/100000000000000 : ℝ)^15
        have hw : |(482193807/1250000000 : ℝ)|=(482193807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5387643933/10000000000 : ℝ)|^19 ≤ (45684820392829/100000000000000 : ℝ)^15
        have hw : |(5387643933/10000000000 : ℝ)|=(5387643933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1641461029/5000000000 : ℝ)|^19 ≤ (12196448758809/50000000000000 : ℝ)^15
        have hw : |(-1641461029/5000000000 : ℝ)|=(1641461029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315064_s0_16 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6840218701/10000000000 : ℝ)*x 0 + (-417005231/1250000000 : ℝ)*x 1 + (508198273/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6840218701/10000000000 : ℝ)^19 ≤ (61814256638593/100000000000000 : ℝ)^15 := by
    have hnat : (6840218701 : ℕ)^19*100000000000000^15 ≤ 61814256638593^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6840218701 10000000000 61814256638593 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417005231/1250000000 : ℝ)^19 ≤ (1555869752677/6250000000000 : ℝ)^15 := by
    have hnat : (417005231 : ℕ)^19*6250000000000^15 ≤ 1555869752677^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417005231 1250000000 1555869752677 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508198273/2500000000 : ℝ)^19 ≤ (13291827298869/100000000000000 : ℝ)^15 := by
    have hnat : (508198273 : ℕ)^19*100000000000000^15 ≤ 13291827298869^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508198273 2500000000 13291827298869 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6840218701/10000000000 : ℝ), (-417005231/1250000000 : ℝ), (508198273/2500000000 : ℝ)] ![(61814256638593/100000000000000 : ℝ), (1555869752677/6250000000000 : ℝ), (13291827298869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6840218701/10000000000 : ℝ)|^19 ≤ (61814256638593/100000000000000 : ℝ)^15
        have hw : |(6840218701/10000000000 : ℝ)|=(6840218701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-417005231/1250000000 : ℝ)|^19 ≤ (1555869752677/6250000000000 : ℝ)^15
        have hw : |(-417005231/1250000000 : ℝ)|=(417005231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(508198273/2500000000 : ℝ)|^19 ≤ (13291827298869/100000000000000 : ℝ)^15
        have hw : |(508198273/2500000000 : ℝ)|=(508198273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315064_s0_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1664067003/5000000000 : ℝ)*x 0 + (-2034717889/5000000000 : ℝ)*x 1 + (-5151330767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1664067003/5000000000 : ℝ)^19 ≤ (24819194695731/100000000000000 : ℝ)^15 := by
    have hnat : (1664067003 : ℕ)^19*100000000000000^15 ≤ 24819194695731^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1664067003 5000000000 24819194695731 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2034717889/5000000000 : ℝ)^19 ≤ (1000598867769/3125000000000 : ℝ)^15 := by
    have hnat : (2034717889 : ℕ)^19*3125000000000^15 ≤ 1000598867769^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034717889 5000000000 1000598867769 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5151330767/10000000000 : ℝ)^19 ≤ (43161641514003/100000000000000 : ℝ)^15 := by
    have hnat : (5151330767 : ℕ)^19*100000000000000^15 ≤ 43161641514003^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151330767 10000000000 43161641514003 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1664067003/5000000000 : ℝ), (-2034717889/5000000000 : ℝ), (-5151330767/10000000000 : ℝ)] ![(24819194695731/100000000000000 : ℝ), (1000598867769/3125000000000 : ℝ), (43161641514003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1664067003/5000000000 : ℝ)|^19 ≤ (24819194695731/100000000000000 : ℝ)^15
        have hw : |(-1664067003/5000000000 : ℝ)|=(1664067003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2034717889/5000000000 : ℝ)|^19 ≤ (1000598867769/3125000000000 : ℝ)^15
        have hw : |(-2034717889/5000000000 : ℝ)|=(2034717889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5151330767/10000000000 : ℝ)|^19 ≤ (43161641514003/100000000000000 : ℝ)^15
        have hw : |(-5151330767/10000000000 : ℝ)|=(5151330767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315064_s0_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (628682043/2000000000 : ℝ)*x 0 + (2816371721/5000000000 : ℝ)*x 1 + (-232513847/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (628682043/2000000000 : ℝ)^19 ≤ (4617476266157/20000000000000 : ℝ)^15 := by
    have hnat : (628682043 : ℕ)^19*20000000000000^15 ≤ 4617476266157^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628682043 2000000000 4617476266157 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2816371721/5000000000 : ℝ)^19 ≤ (48333171803957/100000000000000 : ℝ)^15 := by
    have hnat : (2816371721 : ℕ)^19*100000000000000^15 ≤ 48333171803957^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2816371721 5000000000 48333171803957 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (232513847/625000000 : ℝ)^19 ≤ (3572430856581/12500000000000 : ℝ)^15 := by
    have hnat : (232513847 : ℕ)^19*12500000000000^15 ≤ 3572430856581^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232513847 625000000 3572430856581 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(628682043/2000000000 : ℝ), (2816371721/5000000000 : ℝ), (-232513847/625000000 : ℝ)] ![(4617476266157/20000000000000 : ℝ), (48333171803957/100000000000000 : ℝ), (3572430856581/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(628682043/2000000000 : ℝ)|^19 ≤ (4617476266157/20000000000000 : ℝ)^15
        have hw : |(628682043/2000000000 : ℝ)|=(628682043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2816371721/5000000000 : ℝ)|^19 ≤ (48333171803957/100000000000000 : ℝ)^15
        have hw : |(2816371721/5000000000 : ℝ)|=(2816371721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-232513847/625000000 : ℝ)|^19 ≤ (3572430856581/12500000000000 : ℝ)^15
        have hw : |(-232513847/625000000 : ℝ)|=(232513847/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315064_s0_22 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3443472471/5000000000 : ℝ)*x 0 + (-801203961/2500000000 : ℝ)*x 1 + (529165987/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3443472471/5000000000 : ℝ)^19 ≤ (31174802558877/50000000000000 : ℝ)^15 := by
    have hnat : (3443472471 : ℕ)^19*50000000000000^15 ≤ 31174802558877^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3443472471 5000000000 31174802558877 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (801203961/2500000000 : ℝ)^19 ≤ (11830067912249/50000000000000 : ℝ)^15 := by
    have hnat : (801203961 : ℕ)^19*50000000000000^15 ≤ 11830067912249^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801203961 2500000000 11830067912249 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529165987/2500000000 : ℝ)^19 ≤ (13990259050073/100000000000000 : ℝ)^15 := by
    have hnat : (529165987 : ℕ)^19*100000000000000^15 ≤ 13990259050073^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529165987 2500000000 13990259050073 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3443472471/5000000000 : ℝ), (-801203961/2500000000 : ℝ), (529165987/2500000000 : ℝ)] ![(31174802558877/50000000000000 : ℝ), (11830067912249/50000000000000 : ℝ), (13990259050073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3443472471/5000000000 : ℝ)|^19 ≤ (31174802558877/50000000000000 : ℝ)^15
        have hw : |(3443472471/5000000000 : ℝ)|=(3443472471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-801203961/2500000000 : ℝ)|^19 ≤ (11830067912249/50000000000000 : ℝ)^15
        have hw : |(-801203961/2500000000 : ℝ)|=(801203961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(529165987/2500000000 : ℝ)|^19 ≤ (13990259050073/100000000000000 : ℝ)^15
        have hw : |(529165987/2500000000 : ℝ)|=(529165987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315064_s1_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-114200063/312500000 : ℝ)*x 0 + (-3654401783/10000000000 : ℝ)*x 1 + (-2620664939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114200063/312500000 : ℝ)^19 ≤ (6985122330243/25000000000000 : ℝ)^15 := by
    have hnat : (114200063 : ℕ)^19*25000000000000^15 ≤ 6985122330243^15*312500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114200063 312500000 6985122330243 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3654401783/10000000000 : ℝ)^19 ≤ (27940487064469/100000000000000 : ℝ)^15 := by
    have hnat : (3654401783 : ℕ)^19*100000000000000^15 ≤ 27940487064469^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3654401783 10000000000 27940487064469 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620664939/5000000000 : ℝ)^19 ≤ (44119023606957/100000000000000 : ℝ)^15 := by
    have hnat : (2620664939 : ℕ)^19*100000000000000^15 ≤ 44119023606957^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620664939 5000000000 44119023606957 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-114200063/312500000 : ℝ), (-3654401783/10000000000 : ℝ), (-2620664939/5000000000 : ℝ)] ![(6985122330243/25000000000000 : ℝ), (27940487064469/100000000000000 : ℝ), (44119023606957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-114200063/312500000 : ℝ)|^19 ≤ (6985122330243/25000000000000 : ℝ)^15
        have hw : |(-114200063/312500000 : ℝ)|=(114200063/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3654401783/10000000000 : ℝ)|^19 ≤ (27940487064469/100000000000000 : ℝ)^15
        have hw : |(-3654401783/10000000000 : ℝ)|=(3654401783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2620664939/5000000000 : ℝ)|^19 ≤ (44119023606957/100000000000000 : ℝ)^15
        have hw : |(-2620664939/5000000000 : ℝ)|=(2620664939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315064_s1_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4564273677/10000000000 : ℝ)*x 0 + (2282136693/5000000000 : ℝ)*x 1 + (-1723262323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4564273677/10000000000 : ℝ)^19 ≤ (7405722820489/20000000000000 : ℝ)^15 := by
    have hnat : (4564273677 : ℕ)^19*20000000000000^15 ≤ 7405722820489^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4564273677 10000000000 7405722820489 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282136693/5000000000 : ℝ)^19 ≤ (37028611112101/100000000000000 : ℝ)^15 := by
    have hnat : (2282136693 : ℕ)^19*100000000000000^15 ≤ 37028611112101^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282136693 5000000000 37028611112101 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1723262323/5000000000 : ℝ)^19 ≤ (2594277478087/10000000000000 : ℝ)^15 := by
    have hnat : (1723262323 : ℕ)^19*10000000000000^15 ≤ 2594277478087^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1723262323 5000000000 2594277478087 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4564273677/10000000000 : ℝ), (2282136693/5000000000 : ℝ), (-1723262323/5000000000 : ℝ)] ![(7405722820489/20000000000000 : ℝ), (37028611112101/100000000000000 : ℝ), (2594277478087/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4564273677/10000000000 : ℝ)|^19 ≤ (7405722820489/20000000000000 : ℝ)^15
        have hw : |(4564273677/10000000000 : ℝ)|=(4564273677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2282136693/5000000000 : ℝ)|^19 ≤ (37028611112101/100000000000000 : ℝ)^15
        have hw : |(2282136693/5000000000 : ℝ)|=(2282136693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1723262323/5000000000 : ℝ)|^19 ≤ (2594277478087/10000000000000 : ℝ)^15
        have hw : |(-1723262323/5000000000 : ℝ)|=(1723262323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315064_s1_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4564273677/10000000000 : ℝ)*x 0 + (-2282136693/5000000000 : ℝ)*x 1 + (1723262323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4564273677/10000000000 : ℝ)^19 ≤ (7405722820489/20000000000000 : ℝ)^15 := by
    have hnat : (4564273677 : ℕ)^19*20000000000000^15 ≤ 7405722820489^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4564273677 10000000000 7405722820489 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282136693/5000000000 : ℝ)^19 ≤ (37028611112101/100000000000000 : ℝ)^15 := by
    have hnat : (2282136693 : ℕ)^19*100000000000000^15 ≤ 37028611112101^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282136693 5000000000 37028611112101 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1723262323/5000000000 : ℝ)^19 ≤ (2594277478087/10000000000000 : ℝ)^15 := by
    have hnat : (1723262323 : ℕ)^19*10000000000000^15 ≤ 2594277478087^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1723262323 5000000000 2594277478087 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4564273677/10000000000 : ℝ), (-2282136693/5000000000 : ℝ), (1723262323/5000000000 : ℝ)] ![(7405722820489/20000000000000 : ℝ), (37028611112101/100000000000000 : ℝ), (2594277478087/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4564273677/10000000000 : ℝ)|^19 ≤ (7405722820489/20000000000000 : ℝ)^15
        have hw : |(4564273677/10000000000 : ℝ)|=(4564273677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2282136693/5000000000 : ℝ)|^19 ≤ (37028611112101/100000000000000 : ℝ)^15
        have hw : |(-2282136693/5000000000 : ℝ)|=(2282136693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1723262323/5000000000 : ℝ)|^19 ≤ (2594277478087/10000000000000 : ℝ)^15
        have hw : |(1723262323/5000000000 : ℝ)|=(1723262323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315064_s1_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (114200063/312500000 : ℝ)*x 0 + (-3654401783/10000000000 : ℝ)*x 1 + (-2620664939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114200063/312500000 : ℝ)^19 ≤ (6985122330243/25000000000000 : ℝ)^15 := by
    have hnat : (114200063 : ℕ)^19*25000000000000^15 ≤ 6985122330243^15*312500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114200063 312500000 6985122330243 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3654401783/10000000000 : ℝ)^19 ≤ (27940487064469/100000000000000 : ℝ)^15 := by
    have hnat : (3654401783 : ℕ)^19*100000000000000^15 ≤ 27940487064469^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3654401783 10000000000 27940487064469 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620664939/5000000000 : ℝ)^19 ≤ (44119023606957/100000000000000 : ℝ)^15 := by
    have hnat : (2620664939 : ℕ)^19*100000000000000^15 ≤ 44119023606957^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620664939 5000000000 44119023606957 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(114200063/312500000 : ℝ), (-3654401783/10000000000 : ℝ), (-2620664939/5000000000 : ℝ)] ![(6985122330243/25000000000000 : ℝ), (27940487064469/100000000000000 : ℝ), (44119023606957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(114200063/312500000 : ℝ)|^19 ≤ (6985122330243/25000000000000 : ℝ)^15
        have hw : |(114200063/312500000 : ℝ)|=(114200063/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3654401783/10000000000 : ℝ)|^19 ≤ (27940487064469/100000000000000 : ℝ)^15
        have hw : |(-3654401783/10000000000 : ℝ)|=(3654401783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2620664939/5000000000 : ℝ)|^19 ≤ (44119023606957/100000000000000 : ℝ)^15
        have hw : |(-2620664939/5000000000 : ℝ)|=(2620664939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315064 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (34911/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(796818954377947/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(796818954377947/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(796818954377947/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(796818954377947/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-3094493107/10000000000 : ℝ)*X 0 0+(-458030581/1250000000 : ℝ)*X 0 1+(-5724343173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315064_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((427764567/1250000000 : ℝ)*X 1 0+(5456461207/10000000000 : ℝ)*X 1 1+(-3646553137/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315064_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((3204559917/5000000000 : ℝ)*X 2 0+(-354867381/1000000000 : ℝ)*X 2 1+(118578939/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315064_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-307846647/1000000000 : ℝ)*X 0 0+(-91997499/250000000 : ℝ)*X 0 1+(-5724028517/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315064_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((3415798179/10000000000 : ℝ)*X 1 0+(2776924037/5000000000 : ℝ)*X 1 1+(-3543680961/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315064_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((1277994491/2000000000 : ℝ)*X 2 0+(-3459094359/10000000000 : ℝ)*X 2 1+(2495087197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315064_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_10 : ((9999999977/10000000000 : ℝ)*X 1 0+(1817/10000000000 : ℝ)*X 1 1+(9999999977/10000000000 : ℝ)*X 2 0+(1817/10000000000 : ℝ)*X 2 1+(-1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315064_s0_10 p hpa hpb (pair X 0)
    change _ ≤ P 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-2876709337/10000000000 : ℝ)*X 0 0+(-814932793/2500000000 : ℝ)*X 0 1+(-390919599/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315064_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((482193807/1250000000 : ℝ)*X 1 0+(5387643933/10000000000 : ℝ)*X 1 1+(-1641461029/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315064_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((6840218701/10000000000 : ℝ)*X 2 0+(-417005231/1250000000 : ℝ)*X 2 1+(508198273/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315064_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((-1664067003/5000000000 : ℝ)*X 0 0+(-2034717889/5000000000 : ℝ)*X 0 1+(-5151330767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315064_s0_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((628682043/2000000000 : ℝ)*X 1 0+(2816371721/5000000000 : ℝ)*X 1 1+(-232513847/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315064_s0_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((3443472471/5000000000 : ℝ)*X 2 0+(-801203961/2500000000 : ℝ)*X 2 1+(529165987/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315064_s0_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((319/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(319/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3758439484137258490389/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (110233586117/62500000000 : ℝ)*(base1) + (1323282167/7812500000 : ℝ)*(base7) + (7193379/1000000000000 : ℝ)*(base22) + (1119294438691/1000000000000 : ℝ)*(base39) + (1000844691059/1000000000000 : ℝ)*(base60) + (2784688447609/1000000000000 : ℝ)*(major_s0_0) + (2784688447609/1000000000000 : ℝ)*(major_s0_1) + (2784688447609/1000000000000 : ℝ)*(major_s0_2) + (19183/160000000 : ℝ)*(sp_s0_1) + (5640200684031/1000000000000 : ℝ)*(sp_s0_7) + (3876106381923/1000000000000 : ℝ)*(sp_s0_8) + (969114027869/250000000000 : ℝ)*(sp_s0_9) + (237029181/1000000000000 : ℝ)*(sp_s0_21) + (99647328781/62500000000 : ℝ)*(f.failure) + (775292660971/200000000000 : ℝ)*(f.sum) + (1085175748294811629/2500000000000000000000000000 : ℝ)*base63 + (2656079121379101981/5000000000000000000000000000 : ℝ)*base65 + (3361023430319021277/5000000000000000000000000000 : ℝ)*base67 + (206051760478723/5000000000000000000000000000 : ℝ)*base68 + (93332059893147/156250000000000000000000000 : ℝ)*base71 + (2800366666601981/5000000000000000000000000000 : ℝ)*base72 + (1770344790898019/5000000000000000000000000000 : ℝ)*base74 + (1005207636478723/5000000000000000000000000000 : ℝ)*base77 + (77886377486897/156250000000000000000000000 : ℝ)*base78 + (163/125000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base82 + (4429/6250000000000000 : ℝ)*base87 + (4429/6250000000000000 : ℝ)*base89 + (4429/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-61589/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(-61589/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17074995439824182039079/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5358186394003/1000000000000 : ℝ)*(base1) + (703598031993/500000000000 : ℝ)*(base7) + (1785135433863/1000000000000 : ℝ)*(base39) + (2316986376609/1000000000000 : ℝ)*(base60) + (10265346817329/500000000000 : ℝ)*(major_s0_0) + (3450380100253/500000000000 : ℝ)*(major_s0_1) + (3450380100253/500000000000 : ℝ)*(major_s0_2) + (1153617/100000000000 : ℝ)*(sp_s0_0) + (107459761/1000000000000 : ℝ)*(sp_s0_2) + (1703741679269/125000000000 : ℝ)*(sp_s0_10) + (14389923345661/1000000000000 : ℝ)*(sp_s0_14) + (9031748487827/1000000000000 : ℝ)*(sp_s0_15) + (9031041573869/1000000000000 : ℝ)*(sp_s0_16) + (599454197/1000000000000 : ℝ)*(sp_s0_22) + (1975495165009/500000000000 : ℝ)*(f.failure) + (9031748487827/1000000000000 : ℝ)*(f.sum) + (311792149965593/1250000000000000000000000000 : ℝ)*base63 + (542451111498223/2500000000000000000000000000 : ℝ)*base64 + (70153496179409/2500000000000000000000000000 : ℝ)*base67 + (957268483679409/2500000000000000000000000000 : ℝ)*base69 + (10432191660233/125000000000000000000000000 : ℝ)*base70 + (1613863160309461/2500000000000000000000000000 : ℝ)*base72 + (661768195251777/2500000000000000000000000000 : ℝ)*base75 + (543894463456437/2500000000000000000000000000 : ℝ)*base76 + (250839208782513/625000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (6931/50000000000000000 : ℝ)*base87 + (6931/50000000000000000 : ℝ)*base89 + (6931/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-45887/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-45887/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11773737270685051375179/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (177466703301/40000000000 : ℝ)*(base1) + (1228245611689/1000000000000 : ℝ)*(base7) + (286067706899/1000000000000 : ℝ)*(base39) + (284186213623/200000000000 : ℝ)*(base60) + (4102870119173/200000000000 : ℝ)*(major_s0_0) + (2801898865021/500000000000 : ℝ)*(major_s0_1) + (2801898865021/500000000000 : ℝ)*(major_s0_2) + (17520607/1000000000000 : ℝ)*(sp_s0_7) + (9908291/125000000000 : ℝ)*(sp_s0_8) + (14910552865823/1000000000000 : ℝ)*(sp_s0_10) + (50427369/250000000000 : ℝ)*(sp_s0_16) + (11721165702339/1000000000000 : ℝ)*(sp_s0_20) + (7284436374093/1000000000000 : ℝ)*(sp_s0_21) + (1456862786189/200000000000 : ℝ)*(sp_s0_22) + (802105492709/250000000000 : ℝ)*(f.failure) + (7284515640421/1000000000000 : ℝ)*(f.sum) + (82914434617599/1250000000000000000000000000 : ℝ)*base62 + (958892787356689/2500000000000000000000000000 : ℝ)*base65 + (749750085908113/2500000000000000000000000000 : ℝ)*base67 + (694694066591887/2500000000000000000000000000 : ℝ)*base68 + (640644824602533/5000000000000000000000000000 : ℝ)*base71 + (319916140452057/1000000000000000000000000000 : ℝ)*base72 + (245254062393311/2500000000000000000000000000 : ℝ)*base74 + (50142356777831/1000000000000000000000000000 : ℝ)*base77 + (2049859544444059/5000000000000000000000000000 : ℝ)*base78 + (11231/25000000000000000 : ℝ)*base87 + (11231/25000000000000000 : ℝ)*base89 + (11231/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have s1_pow0 : (319/20000 : ℝ) ^ (75/16 : ℝ) ≤ (15048759911/4000000000000000000 : ℝ) := by
    have hpowers : (319/20000 : ℝ)^75 ≤ (15048759911/4000000000000000000 : ℝ)^16 := by
      have hnat : (319 : ℕ)^75*4000000000000000000^16 ≤ 15048759911^16*20000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        319 20000 15048759911 4000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (319/20000 : ℝ)) (X := (15048759911/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (4000000015048759911/4000000000000000000 : ℝ) ≤ (5000000004013003/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (4000000015048759911/4000000000000000000 : ℝ)^16 ≤ (5000000004013003/5000000000000000 : ℝ)^75 := by
      have hnat : (4000000015048759911 : ℕ)^16*5000000000000000^75 ≤ 5000000004013003^75*4000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4000000015048759911 4000000000000000000 5000000004013003 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000004013003/5000000000000000 : ℝ)) (X := (4000000015048759911/4000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (2000000015048759911/2000000000000000000 : ℝ) ≤ (10000000016052011/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2000000015048759911/2000000000000000000 : ℝ)^16 ≤ (10000000016052011/10000000000000000 : ℝ)^75 := by
      have hnat : (2000000015048759911 : ℕ)^16*10000000000000000^75 ≤ 10000000016052011^75*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000000015048759911 2000000000000000000 10000000016052011 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000016052011/10000000000000000 : ℝ)) (X := (2000000015048759911/2000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(4013003/79750000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1605201/31900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (319/20000 : ℝ)) (alpha := (4013003/79750000000000 : ℝ)) (beta := (1605201/31900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (319/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(4013003/79750000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1605201/31900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (61589/100000 : ℝ) ^ (75/16 : ℝ) ≤ (2577721754380861611/25000000000000000000 : ℝ) := by
    have hpowers : (61589/100000 : ℝ)^75 ≤ (2577721754380861611/25000000000000000000 : ℝ)^16 := by
      have hnat : (61589 : ℕ)^75*25000000000000000000^16 ≤ 2577721754380861611^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61589 100000 2577721754380861611 25000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61589/100000 : ℝ)) (X := (2577721754380861611/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (27577721754380861611/25000000000000000000 : ℝ) ≤ (5105777965082531/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (27577721754380861611/25000000000000000000 : ℝ)^16 ≤ (5105777965082531/5000000000000000 : ℝ)^75 := by
      have hnat : (27577721754380861611 : ℕ)^16*5000000000000000^75 ≤ 5105777965082531^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27577721754380861611 25000000000000000000 5105777965082531 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5105777965082531/5000000000000000 : ℝ)) (X := (27577721754380861611/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (15077721754380861611/12500000000000000000 : ℝ) ≤ (520404235773409/500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (15077721754380861611/12500000000000000000 : ℝ)^16 ≤ (520404235773409/500000000000000 : ℝ)^75 := by
      have hnat : (15077721754380861611 : ℕ)^16*500000000000000^75 ≤ 520404235773409^75*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15077721754380861611 12500000000000000000 520404235773409 500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (520404235773409/500000000000000 : ℝ)) (X := (15077721754380861611/12500000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(105777965082531/3079450000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(98264392651559/3079450000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (61589/100000 : ℝ)) (alpha := (105777965082531/3079450000000000 : ℝ)) (beta := (98264392651559/3079450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (61589/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(105777965082531/3079450000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(98264392651559/3079450000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (45887/100000 : ℝ) ^ (75/16 : ℝ) ≤ (1297598427385257563/50000000000000000000 : ℝ) := by
    have hpowers : (45887/100000 : ℝ)^75 ≤ (1297598427385257563/50000000000000000000 : ℝ)^16 := by
      have hnat : (45887 : ℕ)^75*50000000000000000000^16 ≤ 1297598427385257563^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45887 100000 1297598427385257563 50000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (45887/100000 : ℝ)) (X := (1297598427385257563/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (51297598427385257563/50000000000000000000 : ℝ) ≤ (2513701908556571/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (51297598427385257563/50000000000000000000 : ℝ)^16 ≤ (2513701908556571/2500000000000000 : ℝ)^75 := by
      have hnat : (51297598427385257563 : ℕ)^16*2500000000000000^75 ≤ 2513701908556571^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51297598427385257563 50000000000000000000 2513701908556571 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2513701908556571/2500000000000000 : ℝ)) (X := (51297598427385257563/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (26297598427385257563/25000000000000000000 : ℝ) ≤ (5054267632536861/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (26297598427385257563/25000000000000000000 : ℝ)^16 ≤ (5054267632536861/5000000000000000 : ℝ)^75 := by
      have hnat : (26297598427385257563 : ℕ)^16*5000000000000000^75 ≤ 5054267632536861^75*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26297598427385257563 25000000000000000000 5054267632536861 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5054267632536861/5000000000000000 : ℝ)) (X := (26297598427385257563/25000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(13701908556571/1147175000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(26863815423719/2294350000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (45887/100000 : ℝ)) (alpha := (13701908556571/1147175000000000 : ℝ)) (beta := (26863815423719/2294350000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (45887/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(13701908556571/1147175000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(26863815423719/2294350000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-114200063/312500000 : ℝ)*X 0 0+(-3654401783/10000000000 : ℝ)*X 0 1+(-2620664939/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315064_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4564273677/10000000000 : ℝ)*X 1 0+(2282136693/5000000000 : ℝ)*X 1 1+(-1723262323/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315064_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4564273677/10000000000 : ℝ)*X 2 0+(-2282136693/5000000000 : ℝ)*X 2 1+(1723262323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315064_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((114200063/312500000 : ℝ)*X 0 0+(-3654401783/10000000000 : ℝ)*X 0 1+(-2620664939/5000000000 : ℝ)*X 0 2+(114200063/312500000 : ℝ)*X 1 0+(-3654401783/10000000000 : ℝ)*X 1 1+(-2620664939/5000000000 : ℝ)*X 1 2+(114200063/312500000 : ℝ)*X 2 0+(-3654401783/10000000000 : ℝ)*X 2 1+(-2620664939/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315064_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-373977/50000 : ℝ) < ((-174659/100000 : ℝ)*P 0+(-174659/100000 : ℝ)*P 1+(-174659/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-373977/50000 : ℝ) < (-3008026315506876485768483890591047/409789494235000000000000000000000 : ℝ) := by norm_num
    linear_combination (144450145653/200000000000 : ℝ)*(base1) + (285309/1000000000000 : ℝ)*(base21) + (118237/500000000000 : ℝ)*(base22) + (160751825153/125000000000 : ℝ)*(base39) + (528299883179/1000000000000 : ℝ)*(base40) + (5431/40000000000 : ℝ)*(base44) + (472566783749/1000000000000 : ℝ)*(base49) + (507438741829/1000000000000 : ℝ)*(base60) + (174659/100000 : ℝ)*(major_s1_0) + (69863594569/40000000000 : ℝ)*(major_s1_1) + (174659/100000 : ℝ)*(major_s1_2) + (198066052421/62500000000 : ℝ)*(sp_s1_0) + (305850746837/125000000000 : ℝ)*(sp_s1_1) + (152925349293/62500000000 : ℝ)*(sp_s1_2) + (6943728399/25000000000 : ℝ)*(sp_s1_6) + (2446806110471/1000000000000 : ℝ)*(f.sum) + (3202823486311138597/28261344430000000000000000000000 : ℝ)*base62 + (22638043444077/57358750000000000000000000 : ℝ)*base65 + (93898813687863/615890000000000000000000000 : ℝ)*base66 + (9219084686703/57358750000000000000000000 : ℝ)*base68 + (15346980311954859/18297441250000000000000000000 : ℝ)*base71 + (20416359559/49843750000000000000000 : ℝ)*base72 + (256108589179541/615890000000000000000000000 : ℝ)*base75 + (159473510639/398750000000000000000000 : ℝ)*base77 + (3973324599615163/17860810000000000000000000000 : ℝ)*base78 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem collision_support_c315065_s0_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-65542341/156250000 : ℝ)*x 0 + (-4737173833/10000000000 : ℝ)*x 1 + (3651560577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65542341/156250000 : ℝ)^19 ≤ (831819527221/2500000000000 : ℝ)^15 := by
    have hnat : (65542341 : ℕ)^19*2500000000000^15 ≤ 831819527221^15*156250000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65542341 156250000 831819527221 2500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4737173833/10000000000 : ℝ)^19 ≤ (38814244815989/100000000000000 : ℝ)^15 := by
    have hnat : (4737173833 : ℕ)^19*100000000000000^15 ≤ 38814244815989^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4737173833 10000000000 38814244815989 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3651560577/10000000000 : ℝ)^19 ≤ (1395648703971/5000000000000 : ℝ)^15 := by
    have hnat : (3651560577 : ℕ)^19*5000000000000^15 ≤ 1395648703971^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3651560577 10000000000 1395648703971 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65542341/156250000 : ℝ), (-4737173833/10000000000 : ℝ), (3651560577/10000000000 : ℝ)] ![(831819527221/2500000000000 : ℝ), (38814244815989/100000000000000 : ℝ), (1395648703971/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65542341/156250000 : ℝ)|^19 ≤ (831819527221/2500000000000 : ℝ)^15
        have hw : |(-65542341/156250000 : ℝ)|=(65542341/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4737173833/10000000000 : ℝ)|^19 ≤ (38814244815989/100000000000000 : ℝ)^15
        have hw : |(-4737173833/10000000000 : ℝ)|=(4737173833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3651560577/10000000000 : ℝ)|^19 ≤ (1395648703971/5000000000000 : ℝ)^15
        have hw : |(3651560577/10000000000 : ℝ)|=(3651560577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315065_s0_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1822258989/5000000000 : ℝ)*x 0 + (4134679103/10000000000 : ℝ)*x 1 + (1200407439/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1822258989/5000000000 : ℝ)^19 ≤ (6961200318841/25000000000000 : ℝ)^15 := by
    have hnat : (1822258989 : ℕ)^19*25000000000000^15 ≤ 6961200318841^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1822258989 5000000000 6961200318841 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4134679103/10000000000 : ℝ)^19 ≤ (6534157831141/20000000000000 : ℝ)^15 := by
    have hnat : (4134679103 : ℕ)^19*20000000000000^15 ≤ 6534157831141^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134679103 10000000000 6534157831141 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1200407439/2500000000 : ℝ)^19 ≤ (3948440954999/10000000000000 : ℝ)^15 := by
    have hnat : (1200407439 : ℕ)^19*10000000000000^15 ≤ 3948440954999^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200407439 2500000000 3948440954999 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1822258989/5000000000 : ℝ), (4134679103/10000000000 : ℝ), (1200407439/2500000000 : ℝ)] ![(6961200318841/25000000000000 : ℝ), (6534157831141/20000000000000 : ℝ), (3948440954999/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1822258989/5000000000 : ℝ)|^19 ≤ (6961200318841/25000000000000 : ℝ)^15
        have hw : |(1822258989/5000000000 : ℝ)|=(1822258989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4134679103/10000000000 : ℝ)|^19 ≤ (6534157831141/20000000000000 : ℝ)^15
        have hw : |(4134679103/10000000000 : ℝ)|=(4134679103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1200407439/2500000000 : ℝ)|^19 ≤ (3948440954999/10000000000000 : ℝ)^15
        have hw : |(1200407439/2500000000 : ℝ)|=(1200407439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315065_s0_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (120404507/250000000 : ℝ)*x 0 + (-713733193/2000000000 : ℝ)*x 1 + (-4192560339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (120404507/250000000 : ℝ)^19 ≤ (39636028422559/100000000000000 : ℝ)^15 := by
    have hnat : (120404507 : ℕ)^19*100000000000000^15 ≤ 39636028422559^15*250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120404507 250000000 39636028422559 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (713733193/2000000000 : ℝ)^19 ≤ (27112785528017/100000000000000 : ℝ)^15 := by
    have hnat : (713733193 : ℕ)^19*100000000000000^15 ≤ 27112785528017^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713733193 2000000000 27112785528017 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4192560339/10000000000 : ℝ)^19 ≤ (33251186036407/100000000000000 : ℝ)^15 := by
    have hnat : (4192560339 : ℕ)^19*100000000000000^15 ≤ 33251186036407^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4192560339 10000000000 33251186036407 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(120404507/250000000 : ℝ), (-713733193/2000000000 : ℝ), (-4192560339/10000000000 : ℝ)] ![(39636028422559/100000000000000 : ℝ), (27112785528017/100000000000000 : ℝ), (33251186036407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(120404507/250000000 : ℝ)|^19 ≤ (39636028422559/100000000000000 : ℝ)^15
        have hw : |(120404507/250000000 : ℝ)|=(120404507/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-713733193/2000000000 : ℝ)|^19 ≤ (27112785528017/100000000000000 : ℝ)^15
        have hw : |(-713733193/2000000000 : ℝ)|=(713733193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4192560339/10000000000 : ℝ)|^19 ≤ (33251186036407/100000000000000 : ℝ)^15
        have hw : |(-4192560339/10000000000 : ℝ)|=(4192560339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315065_s0_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (190178953/500000000 : ℝ)*x 0 + (-3755917771/10000000000 : ℝ)*x 1 + (5011191741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (190178953/500000000 : ℝ)^19 ≤ (29392990020807/100000000000000 : ℝ)^15 := by
    have hnat : (190178953 : ℕ)^19*100000000000000^15 ≤ 29392990020807^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190178953 500000000 29392990020807 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3755917771/10000000000 : ℝ)^19 ≤ (28927242018059/100000000000000 : ℝ)^15 := by
    have hnat : (3755917771 : ℕ)^19*100000000000000^15 ≤ 28927242018059^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3755917771 10000000000 28927242018059 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5011191741/10000000000 : ℝ)^19 ≤ (8335953589331/20000000000000 : ℝ)^15 := by
    have hnat : (5011191741 : ℕ)^19*20000000000000^15 ≤ 8335953589331^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5011191741 10000000000 8335953589331 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(190178953/500000000 : ℝ), (-3755917771/10000000000 : ℝ), (5011191741/10000000000 : ℝ)] ![(29392990020807/100000000000000 : ℝ), (28927242018059/100000000000000 : ℝ), (8335953589331/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(190178953/500000000 : ℝ)|^19 ≤ (29392990020807/100000000000000 : ℝ)^15
        have hw : |(190178953/500000000 : ℝ)|=(190178953/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3755917771/10000000000 : ℝ)|^19 ≤ (28927242018059/100000000000000 : ℝ)^15
        have hw : |(-3755917771/10000000000 : ℝ)|=(3755917771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5011191741/10000000000 : ℝ)|^19 ≤ (8335953589331/20000000000000 : ℝ)^15
        have hw : |(5011191741/10000000000 : ℝ)|=(5011191741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315065 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s0_pow0 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(796818954377947/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(523745610258491/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(796818954377947/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(796818954377947/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (75/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^75 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^75*1^16 ≤ 1^16*1^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5796818954377947/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (5796818954377947/5000000000000000 : ℝ)^75 := by
      have hnat : (2 : ℕ)^16*5000000000000000^75 ≤ 5796818954377947^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5796818954377947 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5796818954377947/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3160282282318219/2500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3160282282318219/2500000000000000 : ℝ)^75 := by
      have hnat : (3 : ℕ)^16*2500000000000000^75 ≤ 3160282282318219^75*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3160282282318219 2500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3160282282318219/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(796818954377947/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (796818954377947/5000000000000000 : ℝ)) (beta := (523745610258491/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, false], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(796818954377947/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(523745610258491/5000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-65542341/156250000 : ℝ)*X 0 0+(-4737173833/10000000000 : ℝ)*X 0 1+(3651560577/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315065_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((1822258989/5000000000 : ℝ)*X 1 0+(4134679103/10000000000 : ℝ)*X 1 1+(1200407439/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315065_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((120404507/250000000 : ℝ)*X 2 0+(-713733193/2000000000 : ℝ)*X 2 1+(-4192560339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315065_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((190178953/500000000 : ℝ)*X 0 0+(-3755917771/10000000000 : ℝ)*X 0 1+(5011191741/10000000000 : ℝ)*X 0 2+(190178953/500000000 : ℝ)*X 1 0+(-3755917771/10000000000 : ℝ)*X 1 1+(5011191741/10000000000 : ℝ)*X 1 2+(190178953/500000000 : ℝ)*X 2 0+(-3755917771/10000000000 : ℝ)*X 2 1+(5011191741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315065_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-373977/50000 : ℝ) < ((-174659/100000 : ℝ)*P 0+(-174659/100000 : ℝ)*P 1+(-174659/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-373977/50000 : ℝ) < (-73297877267958066645663/10000000000000000000000 : ℝ) := by norm_num
    linear_combination (66667233901/100000000000 : ℝ)*(base1) + (333327532859/1000000000000 : ℝ)*(base3) + (58883/1000000000000 : ℝ)*(base22) + (71699/1000000000000 : ℝ)*(base24) + (298163968189/500000000000 : ℝ)*(base40) + (71955210069/100000000000 : ℝ)*(base49) + (83158789791/250000000000 : ℝ)*(base50) + (456313490979/1000000000000 : ℝ)*(base60) + (174659/100000 : ℝ)*(major_s0_0) + (174659/100000 : ℝ)*(major_s0_1) + (174659/100000 : ℝ)*(major_s0_2) + (1554967457303/500000000000 : ℝ)*(sp_s0_0) + (555318021691/200000000000 : ℝ)*(sp_s0_1) + (1221631222507/500000000000 : ℝ)*(sp_s0_2) + (128131/1000000000000 : ℝ)*(sp_s0_6) + (610815643899/250000000000 : ℝ)*(f.sum) + (1177935089/2500000000000000000000 : ℝ)*base62 + (1377029419/10000000000000000000000 : ℝ)*base65 + (5903044807/10000000000000000000000 : ℝ)*base67 + (156274231/1000000000000000000000 : ℝ)*base68 + (663638777/1250000000000000000000 : ℝ)*base71 + (951438329/10000000000000000000000 : ℝ)*base73 + (485163/31250000000000000000 : ℝ)*base74 + (2397434029/10000000000000000000000 : ℝ)*base76 + (730884719/2000000000000000000000 : ℝ)*base79 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p015_b025 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (c : Fin 88) (hlo : 63 ≤ c.val) (hhi : c.val < 66)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=63 ∨ c=64 ∨ c=65 := by omega
  rcases hc with rfl|rfl|rfl
  · exact (hn63 rfl).elim
  · exact collision_c315064 p hpa (by linarith only [hpb]) X hX
  · exact collision_c315065 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (c : Fin 88) (hlo : 63 ≤ c.val) (hhi : c.val < 66)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p015_b025 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

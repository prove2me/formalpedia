-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p017_b023
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:17:33.260468+00:00
-- url     : https://prove2.me/submissions/7a328f94-af01-4db3-9f99-b3c8d70a5674

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
theorem collision_support_c317048_s0_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-95908271/400000000 : ℝ)*x 0 + (1198853279/5000000000 : ℝ)*x 1 + (-3617171857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (95908271/400000000 : ℝ)^79 ≤ (8341688452401/50000000000000 : ℝ)^63 := by
    have hnat : (95908271 : ℕ)^79*50000000000000^63 ≤ 8341688452401^63*400000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95908271 400000000 8341688452401 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1198853279/5000000000 : ℝ)^79 ≤ (8341687505719/50000000000000 : ℝ)^63 := by
    have hnat : (1198853279 : ℕ)^79*50000000000000^63 ≤ 8341687505719^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198853279 5000000000 8341687505719 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3617171857/5000000000 : ℝ)^79 ≤ (66633248066781/100000000000000 : ℝ)^63 := by
    have hnat : (3617171857 : ℕ)^79*100000000000000^63 ≤ 66633248066781^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3617171857 5000000000 66633248066781 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-95908271/400000000 : ℝ), (1198853279/5000000000 : ℝ), (-3617171857/5000000000 : ℝ)] ![(8341688452401/50000000000000 : ℝ), (8341687505719/50000000000000 : ℝ), (66633248066781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-95908271/400000000 : ℝ)|^79 ≤ (8341688452401/50000000000000 : ℝ)^63
        have hw : |(-95908271/400000000 : ℝ)|=(95908271/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1198853279/5000000000 : ℝ)|^79 ≤ (8341687505719/50000000000000 : ℝ)^63
        have hw : |(1198853279/5000000000 : ℝ)|=(1198853279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3617171857/5000000000 : ℝ)|^79 ≤ (66633248066781/100000000000000 : ℝ)^63
        have hw : |(-3617171857/5000000000 : ℝ)|=(3617171857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317048_s0_1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (828568993/2500000000 : ℝ)*x 0 + (-414284459/1250000000 : ℝ)*x 1 + (-2873392213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (828568993/2500000000 : ℝ)^79 ≤ (25037018819041/100000000000000 : ℝ)^63 := by
    have hnat : (828568993 : ℕ)^79*100000000000000^63 ≤ 25037018819041^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828568993 2500000000 25037018819041 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (414284459/1250000000 : ℝ)^79 ≤ (25037015977187/100000000000000 : ℝ)^63 := by
    have hnat : (414284459 : ℕ)^79*100000000000000^63 ≤ 25037015977187^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414284459 1250000000 25037015977187 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2873392213/5000000000 : ℝ)^79 ≤ (12481491297831/25000000000000 : ℝ)^63 := by
    have hnat : (2873392213 : ℕ)^79*25000000000000^63 ≤ 12481491297831^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2873392213 5000000000 12481491297831 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(828568993/2500000000 : ℝ), (-414284459/1250000000 : ℝ), (-2873392213/5000000000 : ℝ)] ![(25037018819041/100000000000000 : ℝ), (25037015977187/100000000000000 : ℝ), (12481491297831/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(828568993/2500000000 : ℝ)|^79 ≤ (25037018819041/100000000000000 : ℝ)^63
        have hw : |(828568993/2500000000 : ℝ)|=(828568993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-414284459/1250000000 : ℝ)|^79 ≤ (25037015977187/100000000000000 : ℝ)^63
        have hw : |(-414284459/1250000000 : ℝ)|=(414284459/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2873392213/5000000000 : ℝ)|^79 ≤ (12481491297831/25000000000000 : ℝ)^63
        have hw : |(-2873392213/5000000000 : ℝ)|=(2873392213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317048_s0_7 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-304508787/2500000000 : ℝ)*x 0 + (788326797/10000000000 : ℝ)*x 1 + (-9090408559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (304508787/2500000000 : ℝ)^79 ≤ (3567930992339/50000000000000 : ℝ)^63 := by
    have hnat : (304508787 : ℕ)^79*50000000000000^63 ≤ 3567930992339^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304508787 2500000000 3567930992339 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (788326797/10000000000 : ℝ)^79 ≤ (2067639005901/50000000000000 : ℝ)^63 := by
    have hnat : (788326797 : ℕ)^79*50000000000000^63 ≤ 2067639005901^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788326797 10000000000 2067639005901 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9090408559/10000000000 : ℝ)^79 ≤ (11091107499003/12500000000000 : ℝ)^63 := by
    have hnat : (9090408559 : ℕ)^79*12500000000000^63 ≤ 11091107499003^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9090408559 10000000000 11091107499003 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-304508787/2500000000 : ℝ), (788326797/10000000000 : ℝ), (-9090408559/10000000000 : ℝ)] ![(3567930992339/50000000000000 : ℝ), (2067639005901/50000000000000 : ℝ), (11091107499003/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-304508787/2500000000 : ℝ)|^79 ≤ (3567930992339/50000000000000 : ℝ)^63
        have hw : |(-304508787/2500000000 : ℝ)|=(304508787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(788326797/10000000000 : ℝ)|^79 ≤ (2067639005901/50000000000000 : ℝ)^63
        have hw : |(788326797/10000000000 : ℝ)|=(788326797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9090408559/10000000000 : ℝ)|^79 ≤ (11091107499003/12500000000000 : ℝ)^63
        have hw : |(-9090408559/10000000000 : ℝ)|=(9090408559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317048_s0_8 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2715423959/10000000000 : ℝ)*x 0 + (-474727021/2500000000 : ℝ)*x 1 + (-7356443313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2715423959/10000000000 : ℝ)^79 ≤ (609397127351/3125000000000 : ℝ)^63 := by
    have hnat : (2715423959 : ℕ)^79*3125000000000^63 ≤ 609397127351^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715423959 10000000000 609397127351 3125000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (474727021/2500000000 : ℝ)^79 ≤ (6226397656173/50000000000000 : ℝ)^63 := by
    have hnat : (474727021 : ℕ)^79*50000000000000^63 ≤ 6226397656173^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474727021 2500000000 6226397656173 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7356443313/10000000000 : ℝ)^79 ≤ (17011624149121/25000000000000 : ℝ)^63 := by
    have hnat : (7356443313 : ℕ)^79*25000000000000^63 ≤ 17011624149121^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7356443313 10000000000 17011624149121 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2715423959/10000000000 : ℝ), (-474727021/2500000000 : ℝ), (-7356443313/10000000000 : ℝ)] ![(609397127351/3125000000000 : ℝ), (6226397656173/50000000000000 : ℝ), (17011624149121/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2715423959/10000000000 : ℝ)|^79 ≤ (609397127351/3125000000000 : ℝ)^63
        have hw : |(2715423959/10000000000 : ℝ)|=(2715423959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-474727021/2500000000 : ℝ)|^79 ≤ (6226397656173/50000000000000 : ℝ)^63
        have hw : |(-474727021/2500000000 : ℝ)|=(474727021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7356443313/10000000000 : ℝ)|^79 ≤ (17011624149121/25000000000000 : ℝ)^63
        have hw : |(-7356443313/10000000000 : ℝ)|=(7356443313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317048_s0_9 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3599064353/10000000000 : ℝ)*x 0 + (3845741069/5000000000 : ℝ)*x 1 + (92484259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3599064353/10000000000 : ℝ)^79 ≤ (6940901343629/25000000000000 : ℝ)^63 := by
    have hnat : (3599064353 : ℕ)^79*25000000000000^63 ≤ 6940901343629^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3599064353 10000000000 6940901343629 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3845741069/5000000000 : ℝ)^79 ≤ (71954871781317/100000000000000 : ℝ)^63 := by
    have hnat : (3845741069 : ℕ)^79*100000000000000^63 ≤ 71954871781317^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3845741069 5000000000 71954871781317 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (92484259/10000000000 : ℝ)^79 ≤ (14076141421/5000000000000 : ℝ)^63 := by
    have hnat : (92484259 : ℕ)^79*5000000000000^63 ≤ 14076141421^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92484259 10000000000 14076141421 5000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3599064353/10000000000 : ℝ), (3845741069/5000000000 : ℝ), (92484259/10000000000 : ℝ)] ![(6940901343629/25000000000000 : ℝ), (71954871781317/100000000000000 : ℝ), (14076141421/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3599064353/10000000000 : ℝ)|^79 ≤ (6940901343629/25000000000000 : ℝ)^63
        have hw : |(3599064353/10000000000 : ℝ)|=(3599064353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3845741069/5000000000 : ℝ)|^79 ≤ (71954871781317/100000000000000 : ℝ)^63
        have hw : |(3845741069/5000000000 : ℝ)|=(3845741069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(92484259/10000000000 : ℝ)|^79 ≤ (14076141421/5000000000000 : ℝ)^63
        have hw : |(92484259/10000000000 : ℝ)|=(92484259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317048_s0_13 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3513630639/10000000000 : ℝ)*x 0 + (3845741069/5000000000 : ℝ)*x 1 + (-27528401/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3513630639/10000000000 : ℝ)^79 ≤ (13469844468059/50000000000000 : ℝ)^63 := by
    have hnat : (3513630639 : ℕ)^79*50000000000000^63 ≤ 13469844468059^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3513630639 10000000000 13469844468059 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3845741069/5000000000 : ℝ)^79 ≤ (71954871781317/100000000000000 : ℝ)^63 := by
    have hnat : (3845741069 : ℕ)^79*100000000000000^63 ≤ 71954871781317^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3845741069 5000000000 71954871781317 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27528401/1000000000 : ℝ)^79 ≤ (1105439266367/100000000000000 : ℝ)^63 := by
    have hnat : (27528401 : ℕ)^79*100000000000000^63 ≤ 1105439266367^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27528401 1000000000 1105439266367 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3513630639/10000000000 : ℝ), (3845741069/5000000000 : ℝ), (-27528401/1000000000 : ℝ)] ![(13469844468059/50000000000000 : ℝ), (71954871781317/100000000000000 : ℝ), (1105439266367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3513630639/10000000000 : ℝ)|^79 ≤ (13469844468059/50000000000000 : ℝ)^63
        have hw : |(3513630639/10000000000 : ℝ)|=(3513630639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3845741069/5000000000 : ℝ)|^79 ≤ (71954871781317/100000000000000 : ℝ)^63
        have hw : |(3845741069/5000000000 : ℝ)|=(3845741069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27528401/1000000000 : ℝ)|^79 ≤ (1105439266367/100000000000000 : ℝ)^63
        have hw : |(-27528401/1000000000 : ℝ)|=(27528401/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317048_s0_14 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-824771731/10000000000 : ℝ)*x 0 + (240039079/2000000000 : ℝ)*x 1 + (-4540697509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (824771731/10000000000 : ℝ)^79 ≤ (4376399362147/100000000000000 : ℝ)^63 := by
    have hnat : (824771731 : ℕ)^79*100000000000000^63 ≤ 4376399362147^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824771731 10000000000 4376399362147 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240039079/2000000000 : ℝ)^79 ≤ (1401009817881/20000000000000 : ℝ)^63 := by
    have hnat : (240039079 : ℕ)^79*20000000000000^63 ≤ 1401009817881^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240039079 2000000000 1401009817881 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4540697509/5000000000 : ℝ)^79 ≤ (88618551542479/100000000000000 : ℝ)^63 := by
    have hnat : (4540697509 : ℕ)^79*100000000000000^63 ≤ 88618551542479^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540697509 5000000000 88618551542479 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-824771731/10000000000 : ℝ), (240039079/2000000000 : ℝ), (-4540697509/5000000000 : ℝ)] ![(4376399362147/100000000000000 : ℝ), (1401009817881/20000000000000 : ℝ), (88618551542479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-824771731/10000000000 : ℝ)|^79 ≤ (4376399362147/100000000000000 : ℝ)^63
        have hw : |(-824771731/10000000000 : ℝ)|=(824771731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(240039079/2000000000 : ℝ)|^79 ≤ (1401009817881/20000000000000 : ℝ)^63
        have hw : |(240039079/2000000000 : ℝ)|=(240039079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4540697509/5000000000 : ℝ)|^79 ≤ (88618551542479/100000000000000 : ℝ)^63
        have hw : |(-4540697509/5000000000 : ℝ)|=(4540697509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317048_s0_15 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1844386463/10000000000 : ℝ)*x 0 + (-42716477/156250000 : ℝ)*x 1 + (-1476124753/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1844386463/10000000000 : ℝ)^79 ≤ (12006090744623/100000000000000 : ℝ)^63 := by
    have hnat : (1844386463 : ℕ)^79*100000000000000^63 ≤ 12006090744623^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844386463 10000000000 12006090744623 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42716477/156250000 : ℝ)^79 ≤ (3933364821003/20000000000000 : ℝ)^63 := by
    have hnat : (42716477 : ℕ)^79*20000000000000^63 ≤ 3933364821003^63*156250000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42716477 156250000 3933364821003 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1476124753/2000000000 : ℝ)^79 ≤ (8540885641329/12500000000000 : ℝ)^63 := by
    have hnat : (1476124753 : ℕ)^79*12500000000000^63 ≤ 8540885641329^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1476124753 2000000000 8540885641329 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1844386463/10000000000 : ℝ), (-42716477/156250000 : ℝ), (-1476124753/2000000000 : ℝ)] ![(12006090744623/100000000000000 : ℝ), (3933364821003/20000000000000 : ℝ), (8540885641329/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1844386463/10000000000 : ℝ)|^79 ≤ (12006090744623/100000000000000 : ℝ)^63
        have hw : |(1844386463/10000000000 : ℝ)|=(1844386463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-42716477/156250000 : ℝ)|^79 ≤ (3933364821003/20000000000000 : ℝ)^63
        have hw : |(-42716477/156250000 : ℝ)|=(42716477/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1476124753/2000000000 : ℝ)|^79 ≤ (8540885641329/12500000000000 : ℝ)^63
        have hw : |(-1476124753/2000000000 : ℝ)|=(1476124753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317048_s0_16 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7706250621/10000000000 : ℝ)*x 0 + (222941447/625000000 : ℝ)*x 1 + (63309099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7706250621/10000000000 : ℝ)^79 ≤ (4508010234107/6250000000000 : ℝ)^63 := by
    have hnat : (7706250621 : ℕ)^79*6250000000000^63 ≤ 4508010234107^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7706250621 10000000000 4508010234107 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222941447/625000000 : ℝ)^79 ≤ (27454399776041/100000000000000 : ℝ)^63 := by
    have hnat : (222941447 : ℕ)^79*100000000000000^63 ≤ 27454399776041^63*625000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222941447 625000000 27454399776041 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63309099/5000000000 : ℝ)^79 ≤ (83487292863/20000000000000 : ℝ)^63 := by
    have hnat : (63309099 : ℕ)^79*20000000000000^63 ≤ 83487292863^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63309099 5000000000 83487292863 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7706250621/10000000000 : ℝ), (222941447/625000000 : ℝ), (63309099/5000000000 : ℝ)] ![(4508010234107/6250000000000 : ℝ), (27454399776041/100000000000000 : ℝ), (83487292863/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7706250621/10000000000 : ℝ)|^79 ≤ (4508010234107/6250000000000 : ℝ)^63
        have hw : |(7706250621/10000000000 : ℝ)|=(7706250621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(222941447/625000000 : ℝ)|^79 ≤ (27454399776041/100000000000000 : ℝ)^63
        have hw : |(222941447/625000000 : ℝ)|=(222941447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(63309099/5000000000 : ℝ)|^79 ≤ (83487292863/20000000000000 : ℝ)^63
        have hw : |(63309099/5000000000 : ℝ)|=(63309099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317048_s0_20 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (767345829/1000000000 : ℝ)*x 0 + (222941447/625000000 : ℝ)*x 1 + (-213152441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (767345829/1000000000 : ℝ)^79 ≤ (71743496159167/100000000000000 : ℝ)^63 := by
    have hnat : (767345829 : ℕ)^79*100000000000000^63 ≤ 71743496159167^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      767345829 1000000000 71743496159167 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222941447/625000000 : ℝ)^79 ≤ (27454399776041/100000000000000 : ℝ)^63 := by
    have hnat : (222941447 : ℕ)^79*100000000000000^63 ≤ 27454399776041^63*625000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222941447 625000000 27454399776041 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (213152441/10000000000 : ℝ)^79 ≤ (802104045629/100000000000000 : ℝ)^63 := by
    have hnat : (213152441 : ℕ)^79*100000000000000^63 ≤ 802104045629^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213152441 10000000000 802104045629 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(767345829/1000000000 : ℝ), (222941447/625000000 : ℝ), (-213152441/10000000000 : ℝ)] ![(71743496159167/100000000000000 : ℝ), (27454399776041/100000000000000 : ℝ), (802104045629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(767345829/1000000000 : ℝ)|^79 ≤ (71743496159167/100000000000000 : ℝ)^63
        have hw : |(767345829/1000000000 : ℝ)|=(767345829/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(222941447/625000000 : ℝ)|^79 ≤ (27454399776041/100000000000000 : ℝ)^63
        have hw : |(222941447/625000000 : ℝ)|=(222941447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-213152441/10000000000 : ℝ)|^79 ≤ (802104045629/100000000000000 : ℝ)^63
        have hw : |(-213152441/10000000000 : ℝ)|=(213152441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317048_s0_21 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3758038383/10000000000 : ℝ)*x 0 + (613531209/5000000000 : ℝ)*x 1 + (-6960683181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3758038383/10000000000 : ℝ)^79 ≤ (7327483702483/25000000000000 : ℝ)^63 := by
    have hnat : (3758038383 : ℕ)^79*25000000000000^63 ≤ 7327483702483^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3758038383 10000000000 7327483702483 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (613531209/5000000000 : ℝ)^79 ≤ (7202242004371/100000000000000 : ℝ)^63 := by
    have hnat : (613531209 : ℕ)^79*100000000000000^63 ≤ 7202242004371^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613531209 5000000000 7202242004371 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6960683181/10000000000 : ℝ)^79 ≤ (6348782316679/10000000000000 : ℝ)^63 := by
    have hnat : (6960683181 : ℕ)^79*10000000000000^63 ≤ 6348782316679^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6960683181 10000000000 6348782316679 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3758038383/10000000000 : ℝ), (613531209/5000000000 : ℝ), (-6960683181/10000000000 : ℝ)] ![(7327483702483/25000000000000 : ℝ), (7202242004371/100000000000000 : ℝ), (6348782316679/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3758038383/10000000000 : ℝ)|^79 ≤ (7327483702483/25000000000000 : ℝ)^63
        have hw : |(-3758038383/10000000000 : ℝ)|=(3758038383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(613531209/5000000000 : ℝ)|^79 ≤ (7202242004371/100000000000000 : ℝ)^63
        have hw : |(613531209/5000000000 : ℝ)|=(613531209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6960683181/10000000000 : ℝ)|^79 ≤ (6348782316679/10000000000000 : ℝ)^63
        have hw : |(-6960683181/10000000000 : ℝ)|=(6960683181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317048_s0_22 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (536741081/2500000000 : ℝ)*x 0 + (-9355879/20000000 : ℝ)*x 1 + (-1093523831/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536741081/2500000000 : ℝ)^79 ≤ (7262724168347/50000000000000 : ℝ)^63 := by
    have hnat : (536741081 : ℕ)^79*50000000000000^63 ≤ 7262724168347^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536741081 2500000000 7262724168347 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9355879/20000000 : ℝ)^79 ≤ (38570826387471/100000000000000 : ℝ)^63 := by
    have hnat : (9355879 : ℕ)^79*100000000000000^63 ≤ 38570826387471^63*20000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9355879 20000000 38570826387471 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093523831/2000000000 : ℝ)^79 ≤ (11725931315213/25000000000000 : ℝ)^63 := by
    have hnat : (1093523831 : ℕ)^79*25000000000000^63 ≤ 11725931315213^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093523831 2000000000 11725931315213 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536741081/2500000000 : ℝ), (-9355879/20000000 : ℝ), (-1093523831/2000000000 : ℝ)] ![(7262724168347/50000000000000 : ℝ), (38570826387471/100000000000000 : ℝ), (11725931315213/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536741081/2500000000 : ℝ)|^79 ≤ (7262724168347/50000000000000 : ℝ)^63
        have hw : |(536741081/2500000000 : ℝ)|=(536741081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9355879/20000000 : ℝ)|^79 ≤ (38570826387471/100000000000000 : ℝ)^63
        have hw : |(-9355879/20000000 : ℝ)|=(9355879/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1093523831/2000000000 : ℝ)|^79 ≤ (11725931315213/25000000000000 : ℝ)^63
        have hw : |(-1093523831/2000000000 : ℝ)|=(1093523831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317048_s0_23 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (574716483/1000000000 : ℝ)*x 0 + (1149433133/2000000000 : ℝ)*x 1 + (330707/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (574716483/1000000000 : ℝ)^79 ≤ (49930109354341/100000000000000 : ℝ)^63 := by
    have hnat : (574716483 : ℕ)^79*100000000000000^63 ≤ 49930109354341^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574716483 1000000000 49930109354341 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1149433133/2000000000 : ℝ)^79 ≤ (49930118451/100000000000 : ℝ)^63 := by
    have hnat : (1149433133 : ℕ)^79*100000000000^63 ≤ 49930118451^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149433133 2000000000 49930118451 100000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (330707/62500000 : ℝ)^79 ≤ (69886089249/50000000000000 : ℝ)^63 := by
    have hnat : (330707 : ℕ)^79*50000000000000^63 ≤ 69886089249^63*62500000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330707 62500000 69886089249 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(574716483/1000000000 : ℝ), (1149433133/2000000000 : ℝ), (330707/62500000 : ℝ)] ![(49930109354341/100000000000000 : ℝ), (49930118451/100000000000 : ℝ), (69886089249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(574716483/1000000000 : ℝ)|^79 ≤ (49930109354341/100000000000000 : ℝ)^63
        have hw : |(574716483/1000000000 : ℝ)|=(574716483/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1149433133/2000000000 : ℝ)|^79 ≤ (49930118451/100000000000 : ℝ)^63
        have hw : |(1149433133/2000000000 : ℝ)|=(1149433133/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(330707/62500000 : ℝ)|^79 ≤ (69886089249/50000000000000 : ℝ)^63
        have hw : |(330707/62500000 : ℝ)|=(330707/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317048_s1_0 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2844598/9765625 : ℝ)*x 0 + (145602473/500000000 : ℝ)*x 1 + (-642461089/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2844598/9765625 : ℝ)^79 ≤ (5323722001303/25000000000000 : ℝ)^63 := by
    have hnat : (2844598 : ℕ)^79*25000000000000^63 ≤ 5323722001303^63*9765625^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2844598 9765625 5323722001303 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (145602473/500000000 : ℝ)^79 ≤ (21287381251483/100000000000000 : ℝ)^63 := by
    have hnat : (145602473 : ℕ)^79*100000000000000^63 ≤ 21287381251483^63*500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145602473 500000000 21287381251483 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (642461089/1000000000 : ℝ)^79 ≤ (4593418459/8000000000 : ℝ)^63 := by
    have hnat : (642461089 : ℕ)^79*8000000000^63 ≤ 4593418459^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642461089 1000000000 4593418459 8000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2844598/9765625 : ℝ), (145602473/500000000 : ℝ), (-642461089/1000000000 : ℝ)] ![(5323722001303/25000000000000 : ℝ), (21287381251483/100000000000000 : ℝ), (4593418459/8000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2844598/9765625 : ℝ)|^79 ≤ (5323722001303/25000000000000 : ℝ)^63
        have hw : |(-2844598/9765625 : ℝ)|=(2844598/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(145602473/500000000 : ℝ)|^79 ≤ (21287381251483/100000000000000 : ℝ)^63
        have hw : |(145602473/500000000 : ℝ)|=(145602473/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-642461089/1000000000 : ℝ)|^79 ≤ (4593418459/8000000000 : ℝ)^63
        have hw : |(-642461089/1000000000 : ℝ)|=(642461089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317048_s1_1 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (56971823/156250000 : ℝ)*x 0 + (-182258581/500000000 : ℝ)*x 1 + (-1288838719/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56971823/156250000 : ℝ)^79 ≤ (28220284200021/100000000000000 : ℝ)^63 := by
    have hnat : (56971823 : ℕ)^79*100000000000000^63 ≤ 28220284200021^63*156250000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56971823 156250000 28220284200021 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (182258581/500000000 : ℝ)^79 ≤ (14105168071949/50000000000000 : ℝ)^63 := by
    have hnat : (182258581 : ℕ)^79*50000000000000^63 ≤ 14105168071949^63*500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182258581 500000000 14105168071949 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1288838719/2500000000 : ℝ)^79 ≤ (544617245497/1250000000000 : ℝ)^63 := by
    have hnat : (1288838719 : ℕ)^79*1250000000000^63 ≤ 544617245497^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1288838719 2500000000 544617245497 1250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(56971823/156250000 : ℝ), (-182258581/500000000 : ℝ), (-1288838719/2500000000 : ℝ)] ![(28220284200021/100000000000000 : ℝ), (14105168071949/50000000000000 : ℝ), (544617245497/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(56971823/156250000 : ℝ)|^79 ≤ (28220284200021/100000000000000 : ℝ)^63
        have hw : |(56971823/156250000 : ℝ)|=(56971823/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-182258581/500000000 : ℝ)|^79 ≤ (14105168071949/50000000000000 : ℝ)^63
        have hw : |(-182258581/500000000 : ℝ)|=(182258581/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1288838719/2500000000 : ℝ)|^79 ≤ (544617245497/1250000000000 : ℝ)^63
        have hw : |(-1288838719/2500000000 : ℝ)|=(1288838719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317048_s1_2 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (66775593/125000000 : ℝ)*x 0 + (534339731/1000000000 : ℝ)*x 1 + (1449009957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66775593/125000000 : ℝ)^79 ≤ (11389224649867/25000000000000 : ℝ)^63 := by
    have hnat : (66775593 : ℕ)^79*25000000000000^63 ≤ 11389224649867^63*125000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66775593 125000000 11389224649867 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (534339731/1000000000 : ℝ)^79 ≤ (45571334332171/100000000000000 : ℝ)^63 := by
    have hnat : (534339731 : ℕ)^79*100000000000000^63 ≤ 45571334332171^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534339731 1000000000 45571334332171 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1449009957/10000000000 : ℝ)^79 ≤ (4435883530391/50000000000000 : ℝ)^63 := by
    have hnat : (1449009957 : ℕ)^79*50000000000000^63 ≤ 4435883530391^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1449009957 10000000000 4435883530391 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66775593/125000000 : ℝ), (534339731/1000000000 : ℝ), (1449009957/10000000000 : ℝ)] ![(11389224649867/25000000000000 : ℝ), (45571334332171/100000000000000 : ℝ), (4435883530391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66775593/125000000 : ℝ)|^79 ≤ (11389224649867/25000000000000 : ℝ)^63
        have hw : |(66775593/125000000 : ℝ)|=(66775593/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(534339731/1000000000 : ℝ)|^79 ≤ (45571334332171/100000000000000 : ℝ)^63
        have hw : |(534339731/1000000000 : ℝ)|=(534339731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1449009957/10000000000 : ℝ)|^79 ≤ (4435883530391/50000000000000 : ℝ)^63
        have hw : |(1449009957/10000000000 : ℝ)|=(1449009957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c317048_s1_6 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (317234461/625000000 : ℝ)*x 0 + (1269258489/2500000000 : ℝ)*x 1 + (-2147689369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (317234461/625000000 : ℝ)^79 ≤ (2670464408799/6250000000000 : ℝ)^63 := by
    have hnat : (317234461 : ℕ)^79*6250000000000^63 ≤ 2670464408799^63*625000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317234461 625000000 2670464408799 6250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1269258489/2500000000 : ℝ)^79 ≤ (42740969690021/100000000000000 : ℝ)^63 := by
    have hnat : (1269258489 : ℕ)^79*100000000000000^63 ≤ 42740969690021^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269258489 2500000000 42740969690021 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2147689369/10000000000 : ℝ)^79 ≤ (7265799874549/50000000000000 : ℝ)^63 := by
    have hnat : (2147689369 : ℕ)^79*50000000000000^63 ≤ 7265799874549^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147689369 10000000000 7265799874549 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(317234461/625000000 : ℝ), (1269258489/2500000000 : ℝ), (-2147689369/10000000000 : ℝ)] ![(2670464408799/6250000000000 : ℝ), (42740969690021/100000000000000 : ℝ), (7265799874549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(317234461/625000000 : ℝ)|^79 ≤ (2670464408799/6250000000000 : ℝ)^63
        have hw : |(317234461/625000000 : ℝ)|=(317234461/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1269258489/2500000000 : ℝ)|^79 ≤ (42740969690021/100000000000000 : ℝ)^63
        have hw : |(1269258489/2500000000 : ℝ)|=(1269258489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2147689369/10000000000 : ℝ)|^79 ≤ (7265799874549/50000000000000 : ℝ)^63
        have hw : |(-2147689369/10000000000 : ℝ)|=(2147689369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c317048 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19897/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19897/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19897/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19897/25000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (34473/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
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
  have s0_pow0 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1015215107108913/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1549194288550923/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (77/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^77 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^77*1^16 ≤ 1^16*1^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11549194288550923/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11549194288550923/10000000000000000 : ℝ)^77 := by
      have hnat : (2 : ℕ)^16*10000000000000000^77 ≤ 11549194288550923^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11549194288550923 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11549194288550923/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (3141102348914959/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (3141102348914959/2500000000000000 : ℝ)^77 := by
      have hnat : (3 : ℕ)^16*2500000000000000^77 ≤ 3141102348914959^77*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 3141102348914959 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3141102348914959/2500000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1549194288550923/10000000000000000 : ℝ)) (beta := (1015215107108913/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(1549194288550923/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1015215107108913/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-95908271/400000000 : ℝ)*X 0 0+(1198853279/5000000000 : ℝ)*X 0 1+(-3617171857/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317048_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((828568993/2500000000 : ℝ)*X 1 0+(-414284459/1250000000 : ℝ)*X 1 1+(-2873392213/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317048_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-304508787/2500000000 : ℝ)*X 0 0+(788326797/10000000000 : ℝ)*X 0 1+(-9090408559/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317048_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((2715423959/10000000000 : ℝ)*X 1 0+(-474727021/2500000000 : ℝ)*X 1 1+(-7356443313/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317048_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((3599064353/10000000000 : ℝ)*X 2 0+(3845741069/5000000000 : ℝ)*X 2 1+(92484259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317048_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3513630639/10000000000 : ℝ)*X 0 0+(3845741069/5000000000 : ℝ)*X 0 1+(-27528401/1000000000 : ℝ)*X 0 2+(3513630639/10000000000 : ℝ)*X 1 0+(3845741069/5000000000 : ℝ)*X 1 1+(-27528401/1000000000 : ℝ)*X 1 2+(3513630639/10000000000 : ℝ)*X 2 0+(3845741069/5000000000 : ℝ)*X 2 1+(-27528401/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317048_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-824771731/10000000000 : ℝ)*X 0 0+(240039079/2000000000 : ℝ)*X 0 1+(-4540697509/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317048_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((1844386463/10000000000 : ℝ)*X 1 0+(-42716477/156250000 : ℝ)*X 1 1+(-1476124753/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317048_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((7706250621/10000000000 : ℝ)*X 2 0+(222941447/625000000 : ℝ)*X 2 1+(63309099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317048_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((767345829/1000000000 : ℝ)*X 0 0+(222941447/625000000 : ℝ)*X 0 1+(-213152441/10000000000 : ℝ)*X 0 2+(767345829/1000000000 : ℝ)*X 1 0+(222941447/625000000 : ℝ)*X 1 1+(-213152441/10000000000 : ℝ)*X 1 2+(767345829/1000000000 : ℝ)*X 2 0+(222941447/625000000 : ℝ)*X 2 1+(-213152441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317048_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-3758038383/10000000000 : ℝ)*X 0 0+(613531209/5000000000 : ℝ)*X 0 1+(-6960683181/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317048_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((536741081/2500000000 : ℝ)*X 1 0+(-9355879/20000000 : ℝ)*X 1 1+(-1093523831/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317048_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((574716483/1000000000 : ℝ)*X 2 0+(1149433133/2000000000 : ℝ)*X 2 1+(330707/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317048_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((35709/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(35709/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23561135433736867895943/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1083457211819/1000000000000 : ℝ)*(base5) + (163027370077/200000000000 : ℝ)*(base7) + (4672447351/500000000000 : ℝ)*(base39) + (926126461073/1000000000000 : ℝ)*(base59) + (956319548247/500000000000 : ℝ)*(major_s0_0) + (956319548247/500000000000 : ℝ)*(major_s0_1) + (956319548247/500000000000 : ℝ)*(major_s0_2) + (381699/125000000000 : ℝ)*(sp_s0_0) + (556293/125000000000 : ℝ)*(sp_s0_1) + (2293459134309/1000000000000 : ℝ)*(sp_s0_7) + (1146770590159/500000000000 : ℝ)*(sp_s0_8) + (3377002842481/1000000000000 : ℝ)*(sp_s0_9) + (795072182013/1000000000000 : ℝ)*(sp_s0_13) + (41721381/500000000000 : ℝ)*(sp_s0_14) + (1063392543447/1000000000000 : ℝ)*(f.failure) + (1146772815331/500000000000 : ℝ)*(f.sum) + (2033843247/10000000000000000000000 : ℝ)*base63 + (3997148083725511/5000000000000000000000000000 : ℝ)*base64 + (6303573245274489/5000000000000000000000000000 : ℝ)*base67 + (993382433381981/5000000000000000000000000000 : ℝ)*base68 + (210978172934353/500000000000000000000000000 : ℝ)*base70 + (46417508774489/5000000000000000000000000000 : ℝ)*base72 + (1400090435118019/5000000000000000000000000000 : ℝ)*base74 + (1905496471118019/5000000000000000000000000000 : ℝ)*base76 + (3760494449/10000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (32157/50000000000000000 : ℝ)*base87 + (32157/50000000000000000 : ℝ)*base89 + (32157/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17829/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17829/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18161780471057274325869/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (168188353461/500000000000 : ℝ)*(base5) + (103396985969/125000000000 : ℝ)*(base7) + (189991/1000000000000 : ℝ)*(base39) + (21201247203/125000000000 : ℝ)*(base59) + (379921956671/200000000000 : ℝ)*(major_s0_0) + (379921956671/200000000000 : ℝ)*(major_s0_1) + (379921956671/200000000000 : ℝ)*(major_s0_2) + (1508511/200000000000 : ℝ)*(sp_s0_0) + (683599/100000000000 : ℝ)*(sp_s0_1) + (7422213/100000000000 : ℝ)*(sp_s0_8) + (2267803581549/1000000000000 : ℝ)*(sp_s0_14) + (453546013197/200000000000 : ℝ)*(sp_s0_15) + (1302093915513/500000000000 : ℝ)*(sp_s0_16) + (1546947663197/1000000000000 : ℝ)*(sp_s0_20) + (1056148482367/1000000000000 : ℝ)*(f.failure) + (283476390513/125000000000 : ℝ)*(f.sum) + (1122574157/5000000000000000000000 : ℝ)*base63 + (77019238291377/2000000000000000000000000000 : ℝ)*base65 + (559628341891377/2000000000000000000000000000 : ℝ)*base67 + (498471210057333/2000000000000000000000000000 : ℝ)*base68 + (109247998634871/200000000000000000000000000 : ℝ)*base71 + (2052860030308623/2000000000000000000000000000 : ℝ)*base73 + (176184672142667/2000000000000000000000000000 : ℝ)*base74 + (629994796142667/2000000000000000000000000000 : ℝ)*base76 + (1645802729/10000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (3323/50000000000000000 : ℝ)*base86 + (3323/50000000000000000 : ℝ)*base88 + (3323/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-19591/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-19591/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10080403023692724222009/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1075487343429/1000000000000 : ℝ)*(base5) + (41726248899/1000000000000 : ℝ)*(base7) + (509843/62500000000 : ℝ)*(base8) + (1142121/1000000000000 : ℝ)*(base15) + (5177373/500000000000 : ℝ)*(base16) + (19770656867/1000000000000 : ℝ)*(base39) + (10500515319/7812500000 : ℝ)*(base59) + (464835844961/250000000000 : ℝ)*(major_s0_0) + (464835844961/250000000000 : ℝ)*(major_s0_1) + (464835844961/250000000000 : ℝ)*(major_s0_2) + (753753/1000000000000 : ℝ)*(sp_s0_16) + (2660941003251/1000000000000 : ℝ)*(sp_s0_21) + (20788575499/7812500000 : ℝ)*(sp_s0_22) + (233527234401/62500000000 : ℝ)*(sp_s0_23) + (103376109453/100000000000 : ℝ)*(f.failure) + (2660949160739/1000000000000 : ℝ)*(f.sum) + (4214216867/10000000000000000000000 : ℝ)*base62 + (1273172438737393/2500000000000000000000000000 : ℝ)*base64 + (481813148512607/2500000000000000000000000000 : ℝ)*base67 + (95466613449003/2500000000000000000000000000 : ℝ)*base68 + (168221522778839/250000000000000000000000000 : ℝ)*base70 + (481640750762607/2500000000000000000000000000 : ℝ)*base72 + (1430808991800997/2500000000000000000000000000 : ℝ)*base74 + (1150628042550997/2500000000000000000000000000 : ℝ)*base76 + (1449227507/5000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (2257/5000000000000000 : ℝ)*base86 + (2257/5000000000000000 : ℝ)*base88 + (2257/5000000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (35709/50000 : ℝ) ^ (77/16 : ℝ) ≤ (77305343427051833/390625000000000000 : ℝ) := by
    have hpowers : (35709/50000 : ℝ)^77 ≤ (77305343427051833/390625000000000000 : ℝ)^16 := by
      have hnat : (35709 : ℕ)^77*390625000000000000^16 ≤ 77305343427051833^16*50000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35709 50000 77305343427051833 390625000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35709/50000 : ℝ)) (X := (77305343427051833/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (467930343427051833/390625000000000000 : ℝ) ≤ (519117073875153/500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (467930343427051833/390625000000000000 : ℝ)^16 ≤ (519117073875153/500000000000000 : ℝ)^77 := by
      have hnat : (467930343427051833 : ℕ)^16*500000000000000^77 ≤ 519117073875153^77*390625000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        467930343427051833 390625000000000000 519117073875153 500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (519117073875153/500000000000000 : ℝ)) (X := (467930343427051833/390625000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (272617843427051833/195312500000000000 : ℝ) ≤ (2679374112604123/2500000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (272617843427051833/195312500000000000 : ℝ)^16 ≤ (2679374112604123/2500000000000000 : ℝ)^77 := by
      have hnat : (272617843427051833 : ℕ)^16*2500000000000000^77 ≤ 2679374112604123^77*195312500000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        272617843427051833 195312500000000000 2679374112604123 2500000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2679374112604123/2500000000000000 : ℝ)) (X := (272617843427051833/195312500000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(19117073875153/357090000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(41894371614179/892725000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (35709/50000 : ℝ)) (alpha := (19117073875153/357090000000000 : ℝ)) (beta := (41894371614179/892725000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (35709/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(19117073875153/357090000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(41894371614179/892725000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (17829/25000 : ℝ) ^ (77/16 : ℝ) ≤ (4913628658907946277/25000000000000000000 : ℝ) := by
    have hpowers : (17829/25000 : ℝ)^77 ≤ (4913628658907946277/25000000000000000000 : ℝ)^16 := by
      have hnat : (17829 : ℕ)^77*25000000000000000000^16 ≤ 4913628658907946277^16*25000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17829 25000 4913628658907946277 25000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17829/25000 : ℝ)) (X := (4913628658907946277/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (29913628658907946277/25000000000000000000 : ℝ) ≤ (1297487165420147/1250000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (29913628658907946277/25000000000000000000 : ℝ)^16 ≤ (1297487165420147/1250000000000000 : ℝ)^77 := by
      have hnat : (29913628658907946277 : ℕ)^16*1250000000000000^77 ≤ 1297487165420147^77*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29913628658907946277 25000000000000000000 1297487165420147 1250000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1297487165420147/1250000000000000 : ℝ)) (X := (29913628658907946277/25000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (17413628658907946277/12500000000000000000 : ℝ) ≤ (2142632880406243/2000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (17413628658907946277/12500000000000000000 : ℝ)^16 ≤ (2142632880406243/2000000000000000 : ℝ)^77 := by
      have hnat : (17413628658907946277 : ℕ)^16*2000000000000000^77 ≤ 2142632880406243^77*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17413628658907946277 12500000000000000000 2142632880406243 2000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2142632880406243/2000000000000000 : ℝ)) (X := (17413628658907946277/12500000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(15829055140049/297150000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(333267078670039/7131600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (17829/25000 : ℝ)) (alpha := (15829055140049/297150000000000 : ℝ)) (beta := (333267078670039/7131600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (17829/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(15829055140049/297150000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(333267078670039/7131600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (19591/100000 : ℝ) ^ (77/16 : ℝ) ≤ (39176209164146579/100000000000000000000 : ℝ) := by
    have hpowers : (19591/100000 : ℝ)^77 ≤ (39176209164146579/100000000000000000000 : ℝ)^16 := by
      have hnat : (19591 : ℕ)^77*100000000000000000000^16 ≤ 39176209164146579^16*100000^77 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19591 100000 39176209164146579 100000000000000000000 77 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19591/100000 : ℝ)) (X := (39176209164146579/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100039176209164146579/100000000000000000000 : ℝ) ≤ (10000813924805851/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (100039176209164146579/100000000000000000000 : ℝ)^16 ≤ (10000813924805851/10000000000000000 : ℝ)^77 := by
      have hnat : (100039176209164146579 : ℕ)^16*10000000000000000^77 ≤ 10000813924805851^77*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039176209164146579 100000000000000000000 10000813924805851 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000813924805851/10000000000000000 : ℝ)) (X := (100039176209164146579/100000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50039176209164146579/50000000000000000000 : ℝ) ≤ (10001627597142533/10000000000000000 : ℝ) ^ (77/16 : ℝ) := by
    have hpowers : (50039176209164146579/50000000000000000000 : ℝ)^16 ≤ (10001627597142533/10000000000000000 : ℝ)^77 := by
      have hnat : (50039176209164146579 : ℕ)^16*10000000000000000^77 ≤ 10001627597142533^77*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039176209164146579 50000000000000000000 10001627597142533 10000000000000000 16 77 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001627597142533/10000000000000000 : ℝ)) (X := (50039176209164146579/50000000000000000000 : ℝ)) (by norm_num) 77 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(813924805851/1959100000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(406836168341/979550000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (77/16 : ℝ)) (rho := (19591/100000 : ℝ)) (alpha := (813924805851/1959100000000000 : ℝ)) (beta := (406836168341/979550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (19591/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(813924805851/1959100000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(406836168341/979550000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2844598/9765625 : ℝ)*X 0 0+(145602473/500000000 : ℝ)*X 0 1+(-642461089/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c317048_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((56971823/156250000 : ℝ)*X 1 0+(-182258581/500000000 : ℝ)*X 1 1+(-1288838719/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c317048_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((66775593/125000000 : ℝ)*X 2 0+(534339731/1000000000 : ℝ)*X 2 1+(1449009957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c317048_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((317234461/625000000 : ℝ)*X 0 0+(1269258489/2500000000 : ℝ)*X 0 1+(-2147689369/10000000000 : ℝ)*X 0 2+(317234461/625000000 : ℝ)*X 1 0+(1269258489/2500000000 : ℝ)*X 1 1+(-2147689369/10000000000 : ℝ)*X 1 2+(317234461/625000000 : ℝ)*X 2 0+(1269258489/2500000000 : ℝ)*X 2 1+(-2147689369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c317048_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-194793/25000 : ℝ) < ((-89931/50000 : ℝ)*P 0+(-89931/50000 : ℝ)*P 1+(-89931/50000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-194793/25000 : ℝ) < (-431741533656301803810891533339846363/55434324505560000000000000000000000 : ℝ) := by norm_num
    linear_combination (61/100000000000 : ℝ)*(base7) + (1153/200000000000 : ℝ)*(base12) + (221/125000000000 : ℝ)*(base15) + (2713/1000000000000 : ℝ)*(base23) + (5032975113/31250000000 : ℝ)*(base39) + (4157/1000000000000 : ℝ)*(base44) + (877871516103/1000000000000 : ℝ)*(base59) + (171851633759/500000000000 : ℝ)*(base60) + (89931/50000 : ℝ)*(major_s1_0) + (1798619995843/1000000000000 : ℝ)*(major_s1_1) + (89931/50000 : ℝ)*(major_s1_2) + (2596114329821/1000000000000 : ℝ)*(sp_s1_0) + (2596114329661/1000000000000 : ℝ)*(sp_s1_1) + (1298057166437/500000000000 : ℝ)*(sp_s1_2) + (999999996453/1000000000000 : ℝ)*(sp_s1_6) + (1298057167793/500000000000 : ℝ)*(f.sum) + (4037613570187335403/5821465650000000000000000000000 : ℝ)*base62 + (14935701609219/24488750000000000000000000 : ℝ)*base65 + (882766174678643/7131600000000000000000000000 : ℝ)*base67 + (1848353734679/2448875000000000000000000 : ℝ)*base68 + (15262106658445753/72872397812500000000000000000 : ℝ)*base71 + (22889088552279/119030000000000000000000000 : ℝ)*base73 + (97678911435613/297150000000000000000000000 : ℝ)*base74 + (2323963799257/3719687500000000000000000 : ℝ)*base76 + (15453156425691631789/84887434800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem wide_coarse_distinct_p017_b023 (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (c : Fin 88) (hlo : 48 ≤ c.val) (hhi : c.val < 49)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=48 := by omega
  rcases hc with rfl
  · exact collision_c317048 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (77/16 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (c : Fin 88) (hlo : 48 ≤ c.val) (hhi : c.val < 49)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (89931/50000 : ℝ) (34473/20000 : ℝ) (19897/25000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.wide_coarse_distinct_p017_b023 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

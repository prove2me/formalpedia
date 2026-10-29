-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b017
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:02:14.53468+00:00
-- url     : https://prove2.me/submissions/9a98b185-1ab1-4c32-a624-e331629f7447

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
theorem collision_support_c325037_s0_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-19829381/250000000 : ℝ)*x 0 + (-6806591241/10000000000 : ℝ)*x 1 + (4056915803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19829381/250000000 : ℝ)^87 ≤ (896127194069/20000000000000 : ℝ)^71 := by
    have hnat : (19829381 : ℕ)^87*20000000000000^71 ≤ 896127194069^71*250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19829381 250000000 896127194069 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6806591241/10000000000 : ℝ)^87 ≤ (7801714111093/12500000000000 : ℝ)^71 := by
    have hnat : (6806591241 : ℕ)^87*12500000000000^71 ≤ 7801714111093^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6806591241 10000000000 7801714111093 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4056915803/10000000000 : ℝ)^87 ≤ (16552825563627/50000000000000 : ℝ)^71 := by
    have hnat : (4056915803 : ℕ)^87*50000000000000^71 ≤ 16552825563627^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4056915803 10000000000 16552825563627 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19829381/250000000 : ℝ), (-6806591241/10000000000 : ℝ), (4056915803/10000000000 : ℝ)] ![(896127194069/20000000000000 : ℝ), (7801714111093/12500000000000 : ℝ), (16552825563627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19829381/250000000 : ℝ)|^87 ≤ (896127194069/20000000000000 : ℝ)^71
        have hw : |(-19829381/250000000 : ℝ)|=(19829381/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6806591241/10000000000 : ℝ)|^87 ≤ (7801714111093/12500000000000 : ℝ)^71
        have hw : |(-6806591241/10000000000 : ℝ)|=(6806591241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4056915803/10000000000 : ℝ)|^87 ≤ (16552825563627/50000000000000 : ℝ)^71
        have hw : |(4056915803/10000000000 : ℝ)|=(4056915803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s0_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2460082701/5000000000 : ℝ)*x 0 + (3057030269/10000000000 : ℝ)*x 1 + (4211786649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2460082701/5000000000 : ℝ)^87 ≤ (41934037384181/100000000000000 : ℝ)^71 := by
    have hnat : (2460082701 : ℕ)^87*100000000000000^71 ≤ 41934037384181^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2460082701 5000000000 41934037384181 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3057030269/10000000000 : ℝ)^87 ≤ (2925640508731/12500000000000 : ℝ)^71 := by
    have hnat : (3057030269 : ℕ)^87*12500000000000^71 ≤ 2925640508731^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3057030269 10000000000 2925640508731 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4211786649/10000000000 : ℝ)^87 ≤ (34660838536907/100000000000000 : ℝ)^71 := by
    have hnat : (4211786649 : ℕ)^87*100000000000000^71 ≤ 34660838536907^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211786649 10000000000 34660838536907 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2460082701/5000000000 : ℝ), (3057030269/10000000000 : ℝ), (4211786649/10000000000 : ℝ)] ![(41934037384181/100000000000000 : ℝ), (2925640508731/12500000000000 : ℝ), (34660838536907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2460082701/5000000000 : ℝ)|^87 ≤ (41934037384181/100000000000000 : ℝ)^71
        have hw : |(2460082701/5000000000 : ℝ)|=(2460082701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3057030269/10000000000 : ℝ)|^87 ≤ (2925640508731/12500000000000 : ℝ)^71
        have hw : |(3057030269/10000000000 : ℝ)|=(3057030269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4211786649/10000000000 : ℝ)|^87 ≤ (34660838536907/100000000000000 : ℝ)^71
        have hw : |(4211786649/10000000000 : ℝ)|=(4211786649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s0_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2460082699/5000000000 : ℝ)*x 0 + (-2981630697/10000000000 : ℝ)*x 1 + (-856321463/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2460082699/5000000000 : ℝ)^87 ≤ (41934037342407/100000000000000 : ℝ)^71 := by
    have hnat : (2460082699 : ℕ)^87*100000000000000^71 ≤ 41934037342407^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2460082699 5000000000 41934037342407 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2981630697/10000000000 : ℝ)^87 ≤ (22699741732073/100000000000000 : ℝ)^71 := by
    have hnat : (2981630697 : ℕ)^87*100000000000000^71 ≤ 22699741732073^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2981630697 10000000000 22699741732073 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (856321463/2000000000 : ℝ)^87 ≤ (17683110457411/50000000000000 : ℝ)^71 := by
    have hnat : (856321463 : ℕ)^87*50000000000000^71 ≤ 17683110457411^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856321463 2000000000 17683110457411 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2460082699/5000000000 : ℝ), (-2981630697/10000000000 : ℝ), (-856321463/2000000000 : ℝ)] ![(41934037342407/100000000000000 : ℝ), (22699741732073/100000000000000 : ℝ), (17683110457411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2460082699/5000000000 : ℝ)|^87 ≤ (41934037342407/100000000000000 : ℝ)^71
        have hw : |(2460082699/5000000000 : ℝ)|=(2460082699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2981630697/10000000000 : ℝ)|^87 ≤ (22699741732073/100000000000000 : ℝ)^71
        have hw : |(-2981630697/10000000000 : ℝ)|=(2981630697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-856321463/2000000000 : ℝ)|^87 ≤ (17683110457411/50000000000000 : ℝ)^71
        have hw : |(-856321463/2000000000 : ℝ)|=(856321463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s0_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4000882059/5000000000 : ℝ)*x 0 + (-1307138731/10000000000 : ℝ)*x 1 + (1099942557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4000882059/5000000000 : ℝ)^87 ≤ (38048579905919/50000000000000 : ℝ)^71 := by
    have hnat : (4000882059 : ℕ)^87*50000000000000^71 ≤ 38048579905919^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4000882059 5000000000 38048579905919 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1307138731/10000000000 : ℝ)^87 ≤ (8263859171019/100000000000000 : ℝ)^71 := by
    have hnat : (1307138731 : ℕ)^87*100000000000000^71 ≤ 8263859171019^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307138731 10000000000 8263859171019 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099942557/5000000000 : ℝ)^87 ≤ (15638980995853/100000000000000 : ℝ)^71 := by
    have hnat : (1099942557 : ℕ)^87*100000000000000^71 ≤ 15638980995853^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099942557 5000000000 15638980995853 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4000882059/5000000000 : ℝ), (-1307138731/10000000000 : ℝ), (1099942557/5000000000 : ℝ)] ![(38048579905919/50000000000000 : ℝ), (8263859171019/100000000000000 : ℝ), (15638980995853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4000882059/5000000000 : ℝ)|^87 ≤ (38048579905919/50000000000000 : ℝ)^71
        have hw : |(4000882059/5000000000 : ℝ)|=(4000882059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1307138731/10000000000 : ℝ)|^87 ≤ (8263859171019/100000000000000 : ℝ)^71
        have hw : |(-1307138731/10000000000 : ℝ)|=(1307138731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1099942557/5000000000 : ℝ)|^87 ≤ (15638980995853/100000000000000 : ℝ)^71
        have hw : |(1099942557/5000000000 : ℝ)|=(1099942557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s0_7 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-727359649/10000000000 : ℝ)*x 0 + (-1913093679/2500000000 : ℝ)*x 1 + (389037037/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (727359649/10000000000 : ℝ)^87 ≤ (4029414852691/100000000000000 : ℝ)^71 := by
    have hnat : (727359649 : ℕ)^87*100000000000000^71 ≤ 4029414852691^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      727359649 10000000000 4029414852691 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1913093679/2500000000 : ℝ)^87 ≤ (14409186358521/20000000000000 : ℝ)^71 := by
    have hnat : (1913093679 : ℕ)^87*20000000000000^71 ≤ 14409186358521^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913093679 2500000000 14409186358521 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (389037037/1250000000 : ℝ)^87 ≤ (23924653345481/100000000000000 : ℝ)^71 := by
    have hnat : (389037037 : ℕ)^87*100000000000000^71 ≤ 23924653345481^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389037037 1250000000 23924653345481 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-727359649/10000000000 : ℝ), (-1913093679/2500000000 : ℝ), (389037037/1250000000 : ℝ)] ![(4029414852691/100000000000000 : ℝ), (14409186358521/20000000000000 : ℝ), (23924653345481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-727359649/10000000000 : ℝ)|^87 ≤ (4029414852691/100000000000000 : ℝ)^71
        have hw : |(-727359649/10000000000 : ℝ)|=(727359649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1913093679/2500000000 : ℝ)|^87 ≤ (14409186358521/20000000000000 : ℝ)^71
        have hw : |(-1913093679/2500000000 : ℝ)|=(1913093679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(389037037/1250000000 : ℝ)|^87 ≤ (23924653345481/100000000000000 : ℝ)^71
        have hw : |(389037037/1250000000 : ℝ)|=(389037037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s0_8 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (603176821/1250000000 : ℝ)*x 0 + (579647941/2000000000 : ℝ)*x 1 + (4454993889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (603176821/1250000000 : ℝ)^87 ≤ (127958315207/312500000000 : ℝ)^71 := by
    have hnat : (603176821 : ℕ)^87*312500000000^71 ≤ 127958315207^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603176821 1250000000 127958315207 312500000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (579647941/2000000000 : ℝ)^87 ≤ (21924269425701/100000000000000 : ℝ)^71 := by
    have hnat : (579647941 : ℕ)^87*100000000000000^71 ≤ 21924269425701^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579647941 2000000000 21924269425701 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4454993889/10000000000 : ℝ)^87 ≤ (9282267421909/25000000000000 : ℝ)^71 := by
    have hnat : (4454993889 : ℕ)^87*25000000000000^71 ≤ 9282267421909^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4454993889 10000000000 9282267421909 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(603176821/1250000000 : ℝ), (579647941/2000000000 : ℝ), (4454993889/10000000000 : ℝ)] ![(127958315207/312500000000 : ℝ), (21924269425701/100000000000000 : ℝ), (9282267421909/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(603176821/1250000000 : ℝ)|^87 ≤ (127958315207/312500000000 : ℝ)^71
        have hw : |(603176821/1250000000 : ℝ)|=(603176821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(579647941/2000000000 : ℝ)|^87 ≤ (21924269425701/100000000000000 : ℝ)^71
        have hw : |(579647941/2000000000 : ℝ)|=(579647941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4454993889/10000000000 : ℝ)|^87 ≤ (9282267421909/25000000000000 : ℝ)^71
        have hw : |(4454993889/10000000000 : ℝ)|=(4454993889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s0_9 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4825414567/10000000000 : ℝ)*x 0 + (-81576311/312500000 : ℝ)*x 1 + (-2355787333/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4825414567/10000000000 : ℝ)^87 ≤ (20473330427921/50000000000000 : ℝ)^71 := by
    have hnat : (4825414567 : ℕ)^87*50000000000000^71 ≤ 20473330427921^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4825414567 10000000000 20473330427921 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81576311/312500000 : ℝ)^87 ≤ (9643602954451/50000000000000 : ℝ)^71 := by
    have hnat : (81576311 : ℕ)^87*50000000000000^71 ≤ 9643602954451^71*312500000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81576311 312500000 9643602954451 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2355787333/5000000000 : ℝ)^87 ≤ (1988306660957/5000000000000 : ℝ)^71 := by
    have hnat : (2355787333 : ℕ)^87*5000000000000^71 ≤ 1988306660957^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2355787333 5000000000 1988306660957 5000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4825414567/10000000000 : ℝ), (-81576311/312500000 : ℝ), (-2355787333/5000000000 : ℝ)] ![(20473330427921/50000000000000 : ℝ), (9643602954451/50000000000000 : ℝ), (1988306660957/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4825414567/10000000000 : ℝ)|^87 ≤ (20473330427921/50000000000000 : ℝ)^71
        have hw : |(4825414567/10000000000 : ℝ)|=(4825414567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-81576311/312500000 : ℝ)|^87 ≤ (9643602954451/50000000000000 : ℝ)^71
        have hw : |(-81576311/312500000 : ℝ)|=(81576311/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2355787333/5000000000 : ℝ)|^87 ≤ (1988306660957/5000000000000 : ℝ)^71
        have hw : |(-2355787333/5000000000 : ℝ)|=(2355787333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s0_13 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3898339863/5000000000 : ℝ)*x 0 + (-114366577/2500000000 : ℝ)*x 1 + (195038017/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3898339863/5000000000 : ℝ)^87 ≤ (73714227023297/100000000000000 : ℝ)^71 := by
    have hnat : (3898339863 : ℕ)^87*100000000000000^71 ≤ 73714227023297^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3898339863 5000000000 73714227023297 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114366577/2500000000 : ℝ)^87 ≤ (2282801820999/100000000000000 : ℝ)^71 := by
    have hnat : (114366577 : ℕ)^87*100000000000000^71 ≤ 2282801820999^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114366577 2500000000 2282801820999 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (195038017/625000000 : ℝ)^87 ≤ (24002971145931/100000000000000 : ℝ)^71 := by
    have hnat : (195038017 : ℕ)^87*100000000000000^71 ≤ 24002971145931^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195038017 625000000 24002971145931 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3898339863/5000000000 : ℝ), (-114366577/2500000000 : ℝ), (195038017/625000000 : ℝ)] ![(73714227023297/100000000000000 : ℝ), (2282801820999/100000000000000 : ℝ), (24002971145931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3898339863/5000000000 : ℝ)|^87 ≤ (73714227023297/100000000000000 : ℝ)^71
        have hw : |(3898339863/5000000000 : ℝ)|=(3898339863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-114366577/2500000000 : ℝ)|^87 ≤ (2282801820999/100000000000000 : ℝ)^71
        have hw : |(-114366577/2500000000 : ℝ)|=(114366577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(195038017/625000000 : ℝ)|^87 ≤ (24002971145931/100000000000000 : ℝ)^71
        have hw : |(195038017/625000000 : ℝ)|=(195038017/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s0_14 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-61422229/2500000000 : ℝ)*x 0 + (-6669156547/10000000000 : ℝ)*x 1 + (2273030743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61422229/2500000000 : ℝ)^87 ≤ (1065750513257/100000000000000 : ℝ)^71 := by
    have hnat : (61422229 : ℕ)^87*100000000000000^71 ≤ 1065750513257^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61422229 2500000000 1065750513257 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6669156547/10000000000 : ℝ)^87 ≤ (60873030075929/100000000000000 : ℝ)^71 := by
    have hnat : (6669156547 : ℕ)^87*100000000000000^71 ≤ 60873030075929^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6669156547 10000000000 60873030075929 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273030743/5000000000 : ℝ)^87 ≤ (7612243880311/20000000000000 : ℝ)^71 := by
    have hnat : (2273030743 : ℕ)^87*20000000000000^71 ≤ 7612243880311^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273030743 5000000000 7612243880311 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61422229/2500000000 : ℝ), (-6669156547/10000000000 : ℝ), (2273030743/5000000000 : ℝ)] ![(1065750513257/100000000000000 : ℝ), (60873030075929/100000000000000 : ℝ), (7612243880311/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61422229/2500000000 : ℝ)|^87 ≤ (1065750513257/100000000000000 : ℝ)^71
        have hw : |(-61422229/2500000000 : ℝ)|=(61422229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6669156547/10000000000 : ℝ)|^87 ≤ (60873030075929/100000000000000 : ℝ)^71
        have hw : |(-6669156547/10000000000 : ℝ)|=(6669156547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2273030743/5000000000 : ℝ)|^87 ≤ (7612243880311/20000000000000 : ℝ)^71
        have hw : |(2273030743/5000000000 : ℝ)|=(2273030743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s0_15 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4678538119/10000000000 : ℝ)*x 0 + (389323277/1250000000 : ℝ)*x 1 + (4405969769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4678538119/10000000000 : ℝ)^87 ≤ (7884947360357/20000000000000 : ℝ)^71 := by
    have hnat : (4678538119 : ℕ)^87*20000000000000^71 ≤ 7884947360357^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4678538119 10000000000 7884947360357 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389323277/1250000000 : ℝ)^87 ≤ (11973112462049/50000000000000 : ℝ)^71 := by
    have hnat : (389323277 : ℕ)^87*50000000000000^71 ≤ 11973112462049^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389323277 1250000000 11973112462049 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4405969769/10000000000 : ℝ)^87 ≤ (3662903826063/10000000000000 : ℝ)^71 := by
    have hnat : (4405969769 : ℕ)^87*10000000000000^71 ≤ 3662903826063^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4405969769 10000000000 3662903826063 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4678538119/10000000000 : ℝ), (389323277/1250000000 : ℝ), (4405969769/10000000000 : ℝ)] ![(7884947360357/20000000000000 : ℝ), (11973112462049/50000000000000 : ℝ), (3662903826063/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4678538119/10000000000 : ℝ)|^87 ≤ (7884947360357/20000000000000 : ℝ)^71
        have hw : |(4678538119/10000000000 : ℝ)|=(4678538119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(389323277/1250000000 : ℝ)|^87 ≤ (11973112462049/50000000000000 : ℝ)^71
        have hw : |(389323277/1250000000 : ℝ)|=(389323277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4405969769/10000000000 : ℝ)|^87 ≤ (3662903826063/10000000000000 : ℝ)^71
        have hw : |(4405969769/10000000000 : ℝ)|=(4405969769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s0_16 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2741463283/5000000000 : ℝ)*x 0 + (-1358132631/5000000000 : ℝ)*x 1 + (-1966229837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2741463283/5000000000 : ℝ)^87 ≤ (47884871783417/100000000000000 : ℝ)^71 := by
    have hnat : (2741463283 : ℕ)^87*100000000000000^71 ≤ 47884871783417^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741463283 5000000000 47884871783417 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358132631/5000000000 : ℝ)^87 ≤ (20249607718453/100000000000000 : ℝ)^71 := by
    have hnat : (1358132631 : ℕ)^87*100000000000000^71 ≤ 20249607718453^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358132631 5000000000 20249607718453 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1966229837/5000000000 : ℝ)^87 ≤ (497898757443/1562500000000 : ℝ)^71 := by
    have hnat : (1966229837 : ℕ)^87*1562500000000^71 ≤ 497898757443^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966229837 5000000000 497898757443 1562500000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2741463283/5000000000 : ℝ), (-1358132631/5000000000 : ℝ), (-1966229837/5000000000 : ℝ)] ![(47884871783417/100000000000000 : ℝ), (20249607718453/100000000000000 : ℝ), (497898757443/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2741463283/5000000000 : ℝ)|^87 ≤ (47884871783417/100000000000000 : ℝ)^71
        have hw : |(2741463283/5000000000 : ℝ)|=(2741463283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1358132631/5000000000 : ℝ)|^87 ≤ (20249607718453/100000000000000 : ℝ)^71
        have hw : |(-1358132631/5000000000 : ℝ)|=(1358132631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1966229837/5000000000 : ℝ)|^87 ≤ (497898757443/1562500000000 : ℝ)^71
        have hw : |(-1966229837/5000000000 : ℝ)|=(1966229837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s0_20 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8770896037/10000000000 : ℝ)*x 0 + (-137611713/1250000000 : ℝ)*x 1 + (646178397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8770896037/10000000000 : ℝ)^87 ≤ (10644341833213/12500000000000 : ℝ)^71 := by
    have hnat : (8770896037 : ℕ)^87*12500000000000^71 ≤ 10644341833213^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8770896037 10000000000 10644341833213 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137611713/1250000000 : ℝ)^87 ≤ (6695772459157/100000000000000 : ℝ)^71 := by
    have hnat : (137611713 : ℕ)^87*100000000000000^71 ≤ 6695772459157^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137611713 1250000000 6695772459157 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (646178397/5000000000 : ℝ)^87 ≤ (2037373214953/25000000000000 : ℝ)^71 := by
    have hnat : (646178397 : ℕ)^87*25000000000000^71 ≤ 2037373214953^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646178397 5000000000 2037373214953 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8770896037/10000000000 : ℝ), (-137611713/1250000000 : ℝ), (646178397/5000000000 : ℝ)] ![(10644341833213/12500000000000 : ℝ), (6695772459157/100000000000000 : ℝ), (2037373214953/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8770896037/10000000000 : ℝ)|^87 ≤ (10644341833213/12500000000000 : ℝ)^71
        have hw : |(8770896037/10000000000 : ℝ)|=(8770896037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-137611713/1250000000 : ℝ)|^87 ≤ (6695772459157/100000000000000 : ℝ)^71
        have hw : |(-137611713/1250000000 : ℝ)|=(137611713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(646178397/5000000000 : ℝ)|^87 ≤ (2037373214953/25000000000000 : ℝ)^71
        have hw : |(646178397/5000000000 : ℝ)|=(646178397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s0_21 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-305727201/10000000000 : ℝ)*x 0 + (-3635839717/5000000000 : ℝ)*x 1 + (767553409/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (305727201/10000000000 : ℝ)^87 ≤ (1393159738961/100000000000000 : ℝ)^71 := by
    have hnat : (305727201 : ℕ)^87*100000000000000^71 ≤ 1393159738961^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305727201 10000000000 1393159738961 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3635839717/5000000000 : ℝ)^87 ≤ (2707159283173/4000000000000 : ℝ)^71 := by
    have hnat : (3635839717 : ℕ)^87*4000000000000^71 ≤ 2707159283173^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3635839717 5000000000 2707159283173 4000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (767553409/2000000000 : ℝ)^87 ≤ (30927858172451/100000000000000 : ℝ)^71 := by
    have hnat : (767553409 : ℕ)^87*100000000000000^71 ≤ 30927858172451^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      767553409 2000000000 30927858172451 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-305727201/10000000000 : ℝ), (-3635839717/5000000000 : ℝ), (767553409/2000000000 : ℝ)] ![(1393159738961/100000000000000 : ℝ), (2707159283173/4000000000000 : ℝ), (30927858172451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-305727201/10000000000 : ℝ)|^87 ≤ (1393159738961/100000000000000 : ℝ)^71
        have hw : |(-305727201/10000000000 : ℝ)|=(305727201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3635839717/5000000000 : ℝ)|^87 ≤ (2707159283173/4000000000000 : ℝ)^71
        have hw : |(-3635839717/5000000000 : ℝ)|=(3635839717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(767553409/2000000000 : ℝ)|^87 ≤ (30927858172451/100000000000000 : ℝ)^71
        have hw : |(767553409/2000000000 : ℝ)|=(767553409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s0_22 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2711444441/5000000000 : ℝ)*x 0 + (284351243/1000000000 : ℝ)*x 1 + (1939663871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2711444441/5000000000 : ℝ)^87 ≤ (47243170292323/100000000000000 : ℝ)^71 := by
    have hnat : (2711444441 : ℕ)^87*100000000000000^71 ≤ 47243170292323^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711444441 5000000000 47243170292323 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284351243/1000000000 : ℝ)^87 ≤ (21418064938981/100000000000000 : ℝ)^71 := by
    have hnat : (284351243 : ℕ)^87*100000000000000^71 ≤ 21418064938981^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284351243 1000000000 21418064938981 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1939663871/5000000000 : ℝ)^87 ≤ (31338764754603/100000000000000 : ℝ)^71 := by
    have hnat : (1939663871 : ℕ)^87*100000000000000^71 ≤ 31338764754603^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939663871 5000000000 31338764754603 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2711444441/5000000000 : ℝ), (284351243/1000000000 : ℝ), (1939663871/5000000000 : ℝ)] ![(47243170292323/100000000000000 : ℝ), (21418064938981/100000000000000 : ℝ), (31338764754603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2711444441/5000000000 : ℝ)|^87 ≤ (47243170292323/100000000000000 : ℝ)^71
        have hw : |(2711444441/5000000000 : ℝ)|=(2711444441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(284351243/1000000000 : ℝ)|^87 ≤ (21418064938981/100000000000000 : ℝ)^71
        have hw : |(284351243/1000000000 : ℝ)|=(284351243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1939663871/5000000000 : ℝ)|^87 ≤ (31338764754603/100000000000000 : ℝ)^71
        have hw : |(1939663871/5000000000 : ℝ)|=(1939663871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s0_23 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4663138137/10000000000 : ℝ)*x 0 + (-760918021/2500000000 : ℝ)*x 1 + (-224341009/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4663138137/10000000000 : ℝ)^87 ≤ (9816445055809/25000000000000 : ℝ)^71 := by
    have hnat : (4663138137 : ℕ)^87*25000000000000^71 ≤ 9816445055809^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4663138137 10000000000 9816445055809 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (760918021/2500000000 : ℝ)^87 ≤ (2909983259763/12500000000000 : ℝ)^71 := by
    have hnat : (760918021 : ℕ)^87*12500000000000^71 ≤ 2909983259763^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760918021 2500000000 2909983259763 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224341009/500000000 : ℝ)^87 ≤ (37454353680253/100000000000000 : ℝ)^71 := by
    have hnat : (224341009 : ℕ)^87*100000000000000^71 ≤ 37454353680253^71*500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224341009 500000000 37454353680253 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4663138137/10000000000 : ℝ), (-760918021/2500000000 : ℝ), (-224341009/500000000 : ℝ)] ![(9816445055809/25000000000000 : ℝ), (2909983259763/12500000000000 : ℝ), (37454353680253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4663138137/10000000000 : ℝ)|^87 ≤ (9816445055809/25000000000000 : ℝ)^71
        have hw : |(4663138137/10000000000 : ℝ)|=(4663138137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-760918021/2500000000 : ℝ)|^87 ≤ (2909983259763/12500000000000 : ℝ)^71
        have hw : |(-760918021/2500000000 : ℝ)|=(760918021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-224341009/500000000 : ℝ)|^87 ≤ (37454353680253/100000000000000 : ℝ)^71
        have hw : |(-224341009/500000000 : ℝ)|=(224341009/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s0_27 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1102172607/1250000000 : ℝ)*x 0 + (-464087039/10000000000 : ℝ)*x 1 + (1768470013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102172607/1250000000 : ℝ)^87 ≤ (85708079425881/100000000000000 : ℝ)^71 := by
    have hnat : (1102172607 : ℕ)^87*100000000000000^71 ≤ 85708079425881^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102172607 1250000000 85708079425881 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (464087039/10000000000 : ℝ)^87 ≤ (1161675448009/50000000000000 : ℝ)^71 := by
    have hnat : (464087039 : ℕ)^87*50000000000000^71 ≤ 1161675448009^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464087039 10000000000 1161675448009 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1768470013/10000000000 : ℝ)^87 ≤ (11968569671471/100000000000000 : ℝ)^71 := by
    have hnat : (1768470013 : ℕ)^87*100000000000000^71 ≤ 11968569671471^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768470013 10000000000 11968569671471 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1102172607/1250000000 : ℝ), (-464087039/10000000000 : ℝ), (1768470013/10000000000 : ℝ)] ![(85708079425881/100000000000000 : ℝ), (1161675448009/50000000000000 : ℝ), (11968569671471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1102172607/1250000000 : ℝ)|^87 ≤ (85708079425881/100000000000000 : ℝ)^71
        have hw : |(1102172607/1250000000 : ℝ)|=(1102172607/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-464087039/10000000000 : ℝ)|^87 ≤ (1161675448009/50000000000000 : ℝ)^71
        have hw : |(-464087039/10000000000 : ℝ)|=(464087039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1768470013/10000000000 : ℝ)|^87 ≤ (11968569671471/100000000000000 : ℝ)^71
        have hw : |(1768470013/10000000000 : ℝ)|=(1768470013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s1_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2041560471/10000000000 : ℝ)*x 0 + (-2821320687/5000000000 : ℝ)*x 1 + (4356836887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2041560471/10000000000 : ℝ)^87 ≤ (7135604774249/50000000000000 : ℝ)^71 := by
    have hnat : (2041560471 : ℕ)^87*50000000000000^71 ≤ 7135604774249^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041560471 10000000000 7135604774249 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2821320687/5000000000 : ℝ)^87 ≤ (49599636510267/100000000000000 : ℝ)^71 := by
    have hnat : (2821320687 : ℕ)^87*100000000000000^71 ≤ 49599636510267^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2821320687 5000000000 49599636510267 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4356836887/10000000000 : ℝ)^87 ≤ (2258072120081/6250000000000 : ℝ)^71 := by
    have hnat : (4356836887 : ℕ)^87*6250000000000^71 ≤ 2258072120081^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356836887 10000000000 2258072120081 6250000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2041560471/10000000000 : ℝ), (-2821320687/5000000000 : ℝ), (4356836887/10000000000 : ℝ)] ![(7135604774249/50000000000000 : ℝ), (49599636510267/100000000000000 : ℝ), (2258072120081/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2041560471/10000000000 : ℝ)|^87 ≤ (7135604774249/50000000000000 : ℝ)^71
        have hw : |(-2041560471/10000000000 : ℝ)|=(2041560471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2821320687/5000000000 : ℝ)|^87 ≤ (49599636510267/100000000000000 : ℝ)^71
        have hw : |(-2821320687/5000000000 : ℝ)|=(2821320687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4356836887/10000000000 : ℝ)|^87 ≤ (2258072120081/6250000000000 : ℝ)^71
        have hw : |(4356836887/10000000000 : ℝ)|=(4356836887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s1_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2353244967/5000000000 : ℝ)*x 0 + (3368427909/10000000000 : ℝ)*x 1 + (1034724339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2353244967/5000000000 : ℝ)^87 ≤ (7942710574897/20000000000000 : ℝ)^71 := by
    have hnat : (2353244967 : ℕ)^87*20000000000000^71 ≤ 7942710574897^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2353244967 5000000000 7942710574897 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3368427909/10000000000 : ℝ)^87 ≤ (26359185779059/100000000000000 : ℝ)^71 := by
    have hnat : (3368427909 : ℕ)^87*100000000000000^71 ≤ 26359185779059^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3368427909 10000000000 26359185779059 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034724339/2500000000 : ℝ)^87 ≤ (8481815331147/25000000000000 : ℝ)^71 := by
    have hnat : (1034724339 : ℕ)^87*25000000000000^71 ≤ 8481815331147^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034724339 2500000000 8481815331147 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2353244967/5000000000 : ℝ), (3368427909/10000000000 : ℝ), (1034724339/2500000000 : ℝ)] ![(7942710574897/20000000000000 : ℝ), (26359185779059/100000000000000 : ℝ), (8481815331147/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2353244967/5000000000 : ℝ)|^87 ≤ (7942710574897/20000000000000 : ℝ)^71
        have hw : |(2353244967/5000000000 : ℝ)|=(2353244967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3368427909/10000000000 : ℝ)|^87 ≤ (26359185779059/100000000000000 : ℝ)^71
        have hw : |(3368427909/10000000000 : ℝ)|=(3368427909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034724339/2500000000 : ℝ)|^87 ≤ (8481815331147/25000000000000 : ℝ)^71
        have hw : |(1034724339/2500000000 : ℝ)|=(1034724339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s1_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (187954287/400000000 : ℝ)*x 0 + (-674405079/2000000000 : ℝ)*x 1 + (-828663541/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (187954287/400000000 : ℝ)^87 ≤ (19817323924783/50000000000000 : ℝ)^71 := by
    have hnat : (187954287 : ℕ)^87*50000000000000^71 ≤ 19817323924783^71*400000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187954287 400000000 19817323924783 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674405079/2000000000 : ℝ)^87 ≤ (5278737122447/20000000000000 : ℝ)^71 := by
    have hnat : (674405079 : ℕ)^87*20000000000000^71 ≤ 5278737122447^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674405079 2000000000 5278737122447 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (828663541/2000000000 : ℝ)^87 ≤ (42464583159/125000000000 : ℝ)^71 := by
    have hnat : (828663541 : ℕ)^87*125000000000^71 ≤ 42464583159^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828663541 2000000000 42464583159 125000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(187954287/400000000 : ℝ), (-674405079/2000000000 : ℝ), (-828663541/2000000000 : ℝ)] ![(19817323924783/50000000000000 : ℝ), (5278737122447/20000000000000 : ℝ), (42464583159/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(187954287/400000000 : ℝ)|^87 ≤ (19817323924783/50000000000000 : ℝ)^71
        have hw : |(187954287/400000000 : ℝ)|=(187954287/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-674405079/2000000000 : ℝ)|^87 ≤ (5278737122447/20000000000000 : ℝ)^71
        have hw : |(-674405079/2000000000 : ℝ)|=(674405079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-828663541/2000000000 : ℝ)|^87 ≤ (42464583159/125000000000 : ℝ)^71
        have hw : |(-828663541/2000000000 : ℝ)|=(828663541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325037_s1_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6127795791/10000000000 : ℝ)*x 0 + (-3342193183/10000000000 : ℝ)*x 1 + (1290299133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6127795791/10000000000 : ℝ)^87 ≤ (27437393974799/50000000000000 : ℝ)^71 := by
    have hnat : (6127795791 : ℕ)^87*50000000000000^71 ≤ 27437393974799^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6127795791 10000000000 27437393974799 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3342193183/10000000000 : ℝ)^87 ≤ (26107846647359/100000000000000 : ℝ)^71 := by
    have hnat : (3342193183 : ℕ)^87*100000000000000^71 ≤ 26107846647359^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3342193183 10000000000 26107846647359 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1290299133/5000000000 : ℝ)^87 ≤ (9508682690223/50000000000000 : ℝ)^71 := by
    have hnat : (1290299133 : ℕ)^87*50000000000000^71 ≤ 9508682690223^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1290299133 5000000000 9508682690223 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6127795791/10000000000 : ℝ), (-3342193183/10000000000 : ℝ), (1290299133/5000000000 : ℝ)] ![(27437393974799/50000000000000 : ℝ), (26107846647359/100000000000000 : ℝ), (9508682690223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6127795791/10000000000 : ℝ)|^87 ≤ (27437393974799/50000000000000 : ℝ)^71
        have hw : |(6127795791/10000000000 : ℝ)|=(6127795791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3342193183/10000000000 : ℝ)|^87 ≤ (26107846647359/100000000000000 : ℝ)^71
        have hw : |(-3342193183/10000000000 : ℝ)|=(3342193183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1290299133/5000000000 : ℝ)|^87 ≤ (9508682690223/50000000000000 : ℝ)^71
        have hw : |(1290299133/5000000000 : ℝ)|=(1290299133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c325037 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81317/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81317/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s0_pow0 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(903644717251831/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (85/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^85 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^85*1^16 ≤ 1^16*1^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11393691857257931/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11393691857257931/10000000000000000 : ℝ)^85 := by
      have hnat : (2 : ℕ)^16*10000000000000000^85 ≤ 11393691857257931^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11393691857257931 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11393691857257931/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (6148668287254881/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (6148668287254881/5000000000000000 : ℝ)^85 := by
      have hnat : (3 : ℕ)^16*5000000000000000^85 ≤ 6148668287254881^85*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 6148668287254881 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6148668287254881/5000000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1393691857257931/10000000000000000 : ℝ)) (beta := (903644717251831/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1393691857257931/10000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(903644717251831/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-19829381/250000000 : ℝ)*X 0 0+(-6806591241/10000000000 : ℝ)*X 0 1+(4056915803/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((2460082701/5000000000 : ℝ)*X 1 0+(3057030269/10000000000 : ℝ)*X 1 1+(4211786649/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((2460082699/5000000000 : ℝ)*X 2 0+(-2981630697/10000000000 : ℝ)*X 2 1+(-856321463/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_6 : ((4000882059/5000000000 : ℝ)*X 0 0+(-1307138731/10000000000 : ℝ)*X 0 1+(1099942557/5000000000 : ℝ)*X 0 2+(4000882059/5000000000 : ℝ)*X 1 0+(-1307138731/10000000000 : ℝ)*X 1 1+(1099942557/5000000000 : ℝ)*X 1 2+(4000882059/5000000000 : ℝ)*X 2 0+(-1307138731/10000000000 : ℝ)*X 2 1+(1099942557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s0_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-727359649/10000000000 : ℝ)*X 0 0+(-1913093679/2500000000 : ℝ)*X 0 1+(389037037/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((603176821/1250000000 : ℝ)*X 1 0+(579647941/2000000000 : ℝ)*X 1 1+(4454993889/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((4825414567/10000000000 : ℝ)*X 2 0+(-81576311/312500000 : ℝ)*X 2 1+(-2355787333/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((3898339863/5000000000 : ℝ)*X 0 0+(-114366577/2500000000 : ℝ)*X 0 1+(195038017/625000000 : ℝ)*X 0 2+(3898339863/5000000000 : ℝ)*X 1 0+(-114366577/2500000000 : ℝ)*X 1 1+(195038017/625000000 : ℝ)*X 1 2+(3898339863/5000000000 : ℝ)*X 2 0+(-114366577/2500000000 : ℝ)*X 2 1+(195038017/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-61422229/2500000000 : ℝ)*X 0 0+(-6669156547/10000000000 : ℝ)*X 0 1+(2273030743/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((4678538119/10000000000 : ℝ)*X 1 0+(389323277/1250000000 : ℝ)*X 1 1+(4405969769/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((2741463283/5000000000 : ℝ)*X 2 0+(-1358132631/5000000000 : ℝ)*X 2 1+(-1966229837/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((8770896037/10000000000 : ℝ)*X 0 0+(-137611713/1250000000 : ℝ)*X 0 1+(646178397/5000000000 : ℝ)*X 0 2+(8770896037/10000000000 : ℝ)*X 1 0+(-137611713/1250000000 : ℝ)*X 1 1+(646178397/5000000000 : ℝ)*X 1 2+(8770896037/10000000000 : ℝ)*X 2 0+(-137611713/1250000000 : ℝ)*X 2 1+(646178397/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-305727201/10000000000 : ℝ)*X 0 0+(-3635839717/5000000000 : ℝ)*X 0 1+(767553409/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((2711444441/5000000000 : ℝ)*X 1 0+(284351243/1000000000 : ℝ)*X 1 1+(1939663871/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((4663138137/10000000000 : ℝ)*X 2 0+(-760918021/2500000000 : ℝ)*X 2 1+(-224341009/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((1102172607/1250000000 : ℝ)*X 0 0+(-464087039/10000000000 : ℝ)*X 0 1+(1768470013/10000000000 : ℝ)*X 0 2+(1102172607/1250000000 : ℝ)*X 1 0+(-464087039/10000000000 : ℝ)*X 1 1+(1768470013/10000000000 : ℝ)*X 1 2+(1102172607/1250000000 : ℝ)*X 2 0+(-464087039/10000000000 : ℝ)*X 2 1+(1768470013/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((3671/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3671/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8377922205917373315537/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1477238016761/1000000000000 : ℝ)*(base40) + (1593888149879/1000000000000 : ℝ)*(base49) + (456019097911/1000000000000 : ℝ)*(base59) + (694781644703/125000000000 : ℝ)*(major_s0_0) + (694781644703/125000000000 : ℝ)*(major_s0_1) + (694781644703/125000000000 : ℝ)*(major_s0_2) + (12286149/100000000000 : ℝ)*(sp_s0_0) + (4175113989673/500000000000 : ℝ)*(sp_s0_7) + (8350087960721/1000000000000 : ℝ)*(sp_s0_8) + (8350114046263/1000000000000 : ℝ)*(sp_s0_9) + (345767444201/125000000000 : ℝ)*(sp_s0_13) + (274332691/1000000000000 : ℝ)*(sp_s0_15) + (357893/31250000000 : ℝ)*(sp_s0_21) + (248247149/1000000000000 : ℝ)*(sp_s0_23) + (345767444201/125000000000 : ℝ)*(f.failure) + (2087590573353/250000000000 : ℝ)*(f.sum) + (110724283985507/625000000000000000000000000 : ℝ)*base62 + (342482841048807/1250000000000000000000000000 : ℝ)*base65 + (752105559048807/1250000000000000000000000000 : ℝ)*base67 + (11027524735507/1250000000000000000000000000 : ℝ)*base68 + (4082705405633/12500000000000000000000000 : ℝ)*base71 + (250328202701193/1250000000000000000000000000 : ℝ)*base73 + (15902871860507/1250000000000000000000000000 : ℝ)*base74 + (335022984610507/1250000000000000000000000000 : ℝ)*base76 + (2875597301/5000000000000000000000 : ℝ)*base79 + (4739/12500000000000000 : ℝ)*base87 + (4739/12500000000000000 : ℝ)*base89 + (4739/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-13921/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-13921/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (49356371635297188483423/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3013123044741/1000000000000 : ℝ)*(base40) + (41982246979/31250000000 : ℝ)*(base49) + (1591599/500000000000 : ℝ)*(base59) + (8275010893089/1000000000000 : ℝ)*(major_s0_0) + (8275010893089/1000000000000 : ℝ)*(major_s0_1) + (8275010893089/1000000000000 : ℝ)*(major_s0_2) + (6395729/200000000000 : ℝ)*(sp_s0_0) + (4147667/100000000000 : ℝ)*(sp_s0_6) + (236891057/1000000000000 : ℝ)*(sp_s0_8) + (12431815881693/1000000000000 : ℝ)*(sp_s0_14) + (12431610969281/1000000000000 : ℝ)*(sp_s0_15) + (6215923930169/500000000000 : ℝ)*(sp_s0_16) + (1029528371179/250000000000 : ℝ)*(sp_s0_20) + (626961/40000000000 : ℝ)*(sp_s0_27) + (4118170635411/1000000000000 : ℝ)*(f.failure) + (6215923930169/500000000000 : ℝ)*(f.sum) + (1130761756338859/5000000000000000000000000000 : ℝ)*base63 + (159509294504041/10000000000000000000000000000 : ℝ)*base65 + (2985705027504041/10000000000000000000000000000 : ℝ)*base67 + (2109407171338859/10000000000000000000000000000 : ℝ)*base69 + (15850711641571/100000000000000000000000000 : ℝ)*base70 + (1218949059495959/10000000000000000000000000000 : ℝ)*base73 + (1804708678338859/10000000000000000000000000000 : ℝ)*base75 + (1058314696661141/10000000000000000000000000000 : ℝ)*base76 + (4524446603/10000000000000000000000 : ℝ)*base79 + (49071/100000000000000000 : ℝ)*base86 + (49071/100000000000000000 : ℝ)*base88 + (49071/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34411/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(34411/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (45287917005573393690627/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83291146967/25000000000 : ℝ)*(base40) + (360590373457/200000000000 : ℝ)*(base49) + (220631429281/1000000000000 : ℝ)*(base59) + (4380601181313/500000000000 : ℝ)*(major_s0_0) + (4380601181313/500000000000 : ℝ)*(major_s0_1) + (4380601181313/500000000000 : ℝ)*(major_s0_2) + (2471959/250000000000 : ℝ)*(sp_s0_1) + (74290481/500000000000 : ℝ)*(sp_s0_2) + (8962611/125000000000 : ℝ)*(sp_s0_7) + (38498237/500000000000 : ℝ)*(sp_s0_20) + (13162196616737/1000000000000 : ℝ)*(sp_s0_21) + (13162258429789/1000000000000 : ℝ)*(sp_s0_22) + (6581059868331/500000000000 : ℝ)*(sp_s0_23) + (1090013343189/250000000000 : ℝ)*(sp_s0_27) + (4360130369229/1000000000000 : ℝ)*(f.failure) + (1645283539703/125000000000 : ℝ)*(f.sum) + (1162113768006597/2500000000000000000000000000 : ℝ)*base62 + (112177589234103/5000000000000000000000000000 : ℝ)*base64 + (1036523889265897/5000000000000000000000000000 : ℝ)*base67 + (3493232783756597/5000000000000000000000000000 : ℝ)*base68 + (19705259609907/50000000000000000000000000 : ℝ)*base70 + (1509409580765897/5000000000000000000000000000 : ℝ)*base72 + (928070583756597/5000000000000000000000000000 : ℝ)*base74 + (297566810756597/5000000000000000000000000000 : ℝ)*base76 + (165633003/5000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (93969/100000000000000000 : ℝ)*base86 + (93969/100000000000000000 : ℝ)*base88 + (93969/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have s1_pow0 : (3671/25000 : ℝ) ^ (85/16 : ℝ) ≤ (117141496603439/3125000000000000000 : ℝ) := by
    have hpowers : (3671/25000 : ℝ)^85 ≤ (117141496603439/3125000000000000000 : ℝ)^16 := by
      have hnat : (3671 : ℕ)^85*3125000000000000000^16 ≤ 117141496603439^16*25000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3671 25000 117141496603439 3125000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3671/25000 : ℝ)) (X := (117141496603439/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (3125117141496603439/3125000000000000000 : ℝ) ≤ (10000070559451487/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (3125117141496603439/3125000000000000000 : ℝ)^16 ≤ (10000070559451487/10000000000000000 : ℝ)^85 := by
      have hnat : (3125117141496603439 : ℕ)^16*10000000000000000^85 ≤ 10000070559451487^85*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125117141496603439 3125000000000000000 10000070559451487 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000070559451487/10000000000000000 : ℝ)) (X := (3125117141496603439/3125000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (1562617141496603439/1562500000000000000 : ℝ) ≤ (625008819797251/625000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (1562617141496603439/1562500000000000000 : ℝ)^16 ≤ (625008819797251/625000000000000 : ℝ)^85 := by
      have hnat : (1562617141496603439 : ℕ)^16*625000000000000^85 ≤ 625008819797251^85*1562500000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562617141496603439 1562500000000000000 625008819797251 625000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625008819797251/625000000000000 : ℝ)) (X := (1562617141496603439/1562500000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(70559451487/1468400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(70557304529/1468400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (3671/25000 : ℝ)) (alpha := (70559451487/1468400000000000 : ℝ)) (beta := (70557304529/1468400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (3671/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(70559451487/1468400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(70557304529/1468400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (13921/50000 : ℝ) ^ (85/16 : ℝ) ≤ (22438872219550747/20000000000000000000 : ℝ) := by
    have hpowers : (13921/50000 : ℝ)^85 ≤ (22438872219550747/20000000000000000000 : ℝ)^16 := by
      have hnat : (13921 : ℕ)^85*20000000000000000000^16 ≤ 22438872219550747^16*50000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13921 50000 22438872219550747 20000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13921/50000 : ℝ)) (X := (22438872219550747/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (20022438872219550747/20000000000000000000 : ℝ) ≤ (10002110932798939/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (20022438872219550747/20000000000000000000 : ℝ)^16 ≤ (10002110932798939/10000000000000000 : ℝ)^85 := by
      have hnat : (20022438872219550747 : ℕ)^16*10000000000000000^85 ≤ 10002110932798939^85*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20022438872219550747 20000000000000000000 10002110932798939 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002110932798939/10000000000000000 : ℝ)) (X := (20022438872219550747/20000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (10022438872219550747/10000000000000000000 : ℝ) ≤ (10004219946084167/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (10022438872219550747/10000000000000000000 : ℝ)^16 ≤ (10004219946084167/10000000000000000 : ℝ)^85 := by
      have hnat : (10022438872219550747 : ℕ)^16*10000000000000000^85 ≤ 10004219946084167^85*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10022438872219550747 10000000000000000000 10004219946084167 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004219946084167/10000000000000000 : ℝ)) (X := (10022438872219550747/10000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(2110932798939/2784200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(527253321307/696050000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (13921/50000 : ℝ)) (alpha := (2110932798939/2784200000000000 : ℝ)) (beta := (527253321307/696050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (13921/50000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(2110932798939/2784200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(527253321307/696050000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (34411/100000 : ℝ) ^ (85/16 : ℝ) ≤ (345703974271007641/100000000000000000000 : ℝ) := by
    have hpowers : (34411/100000 : ℝ)^85 ≤ (345703974271007641/100000000000000000000 : ℝ)^16 := by
      have hnat : (34411 : ℕ)^85*100000000000000000000^16 ≤ 345703974271007641^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34411 100000 345703974271007641 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34411/100000 : ℝ)) (X := (345703974271007641/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100345703974271007641/100000000000000000000 : ℝ) ≤ (10006498257120427/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (100345703974271007641/100000000000000000000 : ℝ)^16 ≤ (10006498257120427/10000000000000000 : ℝ)^85 := by
      have hnat : (100345703974271007641 : ℕ)^16*10000000000000000^85 ≤ 10006498257120427^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100345703974271007641 100000000000000000000 10006498257120427 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006498257120427/10000000000000000 : ℝ)) (X := (100345703974271007641/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50345703974271007641/50000000000000000000 : ℝ) ≤ (2503244591581733/2500000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (50345703974271007641/50000000000000000000 : ℝ)^16 ≤ (2503244591581733/2500000000000000 : ℝ)^85 := by
      have hnat : (50345703974271007641 : ℕ)^16*2500000000000000^85 ≤ 2503244591581733^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50345703974271007641 50000000000000000000 2503244591581733 2500000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503244591581733/2500000000000000 : ℝ)) (X := (50345703974271007641/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(6498257120427/3441100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(1296021841301/688220000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (34411/100000 : ℝ)) (alpha := (6498257120427/3441100000000000 : ℝ)) (beta := (1296021841301/688220000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (34411/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(6498257120427/3441100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(1296021841301/688220000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2041560471/10000000000 : ℝ)*X 0 0+(-2821320687/5000000000 : ℝ)*X 0 1+(4356836887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2353244967/5000000000 : ℝ)*X 1 0+(3368427909/10000000000 : ℝ)*X 1 1+(1034724339/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((187954287/400000000 : ℝ)*X 2 0+(-674405079/2000000000 : ℝ)*X 2 1+(-828663541/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6127795791/10000000000 : ℝ)*X 0 0+(-3342193183/10000000000 : ℝ)*X 0 1+(1290299133/5000000000 : ℝ)*X 0 2+(6127795791/10000000000 : ℝ)*X 1 0+(-3342193183/10000000000 : ℝ)*X 1 1+(1290299133/5000000000 : ℝ)*X 1 2+(6127795791/10000000000 : ℝ)*X 2 0+(-3342193183/10000000000 : ℝ)*X 2 1+(1290299133/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325037_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-452817/50000 : ℝ) < ((-200939/100000 : ℝ)*P 0+(-200939/100000 : ℝ)*P 1+(-200939/100000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-452817/50000 : ℝ) < (-78487390725671246076901009766508597/8792697171505000000000000000000000 : ℝ) := by norm_num
    linear_combination (1037/250000000000 : ℝ)*(base13) + (577/200000000000 : ℝ)*(base21) + (75914175891/500000000000 : ℝ)*(base39) + (335867953139/500000000000 : ℝ)*(base40) + (45344150553/100000000000 : ℝ)*(base49) + (1479/1000000000000 : ℝ)*(base59) + (5327/1000000000000 : ℝ)*(base60) + (1337/200000000000 : ℝ)*(ratio_s0_1) + (200939/100000 : ℝ)*(major_s1_0) + (200939/100000 : ℝ)*(major_s1_1) + (200939/100000 : ℝ)*(major_s1_2) + (1487738234831/500000000000 : ℝ)*(sp_s1_0) + (2975476473811/1000000000000 : ℝ)*(sp_s1_1) + (119019058837/40000000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (2975476473811/1000000000000 : ℝ)*(f.sum) + (2076883547626087069/2395177655000000000000000000000 : ℝ)*base62 + (72557916705333/86027500000000000000000000 : ℝ)*base64 + (29382123518663/69605000000000000000000000 : ℝ)*base67 + (92344834904407/172055000000000000000000000 : ℝ)*base68 + (1328902704252454419/1263227810000000000000000000000 : ℝ)*base70 + (5222233542141/9177500000000000000000000 : ℝ)*base73 + (17264735899/222736000000000000000000 : ℝ)*base74 + (194518955467/293680000000000000000000 : ℝ)*base76 + (1991386163685647/4088319280000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p025_b017 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 38)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=37 := by omega
  rcases hc with rfl
  · exact collision_c325037 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (c : Fin 88) (hlo : 37 ≤ c.val) (hhi : c.val < 38)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p025_b017 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution

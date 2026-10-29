-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b027
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:27:21.419331+00:00
-- url     : https://prove2.me/submissions/e43a7662-6e44-4c56-9d02-36129d43b06d

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
theorem collision_support_c329057_s0_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1445994231/5000000000 : ℝ)*x 0 + (1445994813/5000000000 : ℝ)*x 1 + (6083679339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1445994231/5000000000 : ℝ)^95 ≤ (562356625803/2500000000000 : ℝ)^79 := by
    have hnat : (1445994231 : ℕ)^95*2500000000000^79 ≤ 562356625803^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445994231 5000000000 562356625803 2500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1445994813/5000000000 : ℝ)^95 ≤ (4498855183907/20000000000000 : ℝ)^79 := by
    have hnat : (1445994813 : ℕ)^95*20000000000000^79 ≤ 4498855183907^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1445994813 5000000000 4498855183907 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6083679339/10000000000 : ℝ)^95 ≤ (55011459035141/100000000000000 : ℝ)^79 := by
    have hnat : (6083679339 : ℕ)^95*100000000000000^79 ≤ 55011459035141^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6083679339 10000000000 55011459035141 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1445994231/5000000000 : ℝ), (1445994813/5000000000 : ℝ), (6083679339/10000000000 : ℝ)] ![(562356625803/2500000000000 : ℝ), (4498855183907/20000000000000 : ℝ), (55011459035141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1445994231/5000000000 : ℝ)|^95 ≤ (562356625803/2500000000000 : ℝ)^79
        have hw : |(-1445994231/5000000000 : ℝ)|=(1445994231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1445994813/5000000000 : ℝ)|^95 ≤ (4498855183907/20000000000000 : ℝ)^79
        have hw : |(1445994813/5000000000 : ℝ)|=(1445994813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6083679339/10000000000 : ℝ)|^95 ≤ (55011459035141/100000000000000 : ℝ)^79
        have hw : |(6083679339/10000000000 : ℝ)|=(6083679339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329057_s0_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (578397693/2000000000 : ℝ)*x 0 + (-2891989629/10000000000 : ℝ)*x 1 + (6083679333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (578397693/2000000000 : ℝ)^95 ≤ (1124713253009/5000000000000 : ℝ)^79 := by
    have hnat : (578397693 : ℕ)^95*5000000000000^79 ≤ 1124713253009^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578397693 2000000000 1124713253009 5000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2891989629/10000000000 : ℝ)^95 ≤ (4498855189519/20000000000000 : ℝ)^79 := by
    have hnat : (2891989629 : ℕ)^95*20000000000000^79 ≤ 4498855189519^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2891989629 10000000000 4498855189519 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6083679333/10000000000 : ℝ)^95 ≤ (55011458969897/100000000000000 : ℝ)^79 := by
    have hnat : (6083679333 : ℕ)^95*100000000000000^79 ≤ 55011458969897^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6083679333 10000000000 55011458969897 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(578397693/2000000000 : ℝ), (-2891989629/10000000000 : ℝ), (6083679333/10000000000 : ℝ)] ![(1124713253009/5000000000000 : ℝ), (4498855189519/20000000000000 : ℝ), (55011458969897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(578397693/2000000000 : ℝ)|^95 ≤ (1124713253009/5000000000000 : ℝ)^79
        have hw : |(578397693/2000000000 : ℝ)|=(578397693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2891989629/10000000000 : ℝ)|^95 ≤ (4498855189519/20000000000000 : ℝ)^79
        have hw : |(-2891989629/10000000000 : ℝ)|=(2891989629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6083679333/10000000000 : ℝ)|^95 ≤ (55011458969897/100000000000000 : ℝ)^79
        have hw : |(6083679333/10000000000 : ℝ)|=(6083679333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329057_s0_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5619139651/10000000000 : ℝ)*x 0 + (351196149/625000000 : ℝ)*x 1 + (-3909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5619139651/10000000000 : ℝ)^95 ≤ (50000004507287/100000000000000 : ℝ)^79 := by
    have hnat : (5619139651 : ℕ)^95*100000000000000^79 ≤ 50000004507287^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5619139651 10000000000 50000004507287 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (351196149/625000000 : ℝ)^95 ≤ (49999990949983/100000000000000 : ℝ)^79 := by
    have hnat : (351196149 : ℕ)^95*100000000000000^79 ≤ 49999990949983^79*625000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351196149 625000000 49999990949983 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3909/5000000000 : ℝ)^95 ≤ (4531629/100000000000000 : ℝ)^79 := by
    have hnat : (3909 : ℕ)^95*100000000000000^79 ≤ 4531629^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3909 5000000000 4531629 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5619139651/10000000000 : ℝ), (351196149/625000000 : ℝ), (-3909/5000000000 : ℝ)] ![(50000004507287/100000000000000 : ℝ), (49999990949983/100000000000000 : ℝ), (4531629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5619139651/10000000000 : ℝ)|^95 ≤ (50000004507287/100000000000000 : ℝ)^79
        have hw : |(5619139651/10000000000 : ℝ)|=(5619139651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(351196149/625000000 : ℝ)|^95 ≤ (49999990949983/100000000000000 : ℝ)^79
        have hw : |(351196149/625000000 : ℝ)|=(351196149/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3909/5000000000 : ℝ)|^95 ≤ (4531629/100000000000000 : ℝ)^79
        have hw : |(-3909/5000000000 : ℝ)|=(3909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329057_s0_7 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2432330631/10000000000 : ℝ)*x 0 + (741351921/10000000000 : ℝ)*x 1 + (8077430869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2432330631/10000000000 : ℝ)^95 ≤ (365344651103/2000000000000 : ℝ)^79 := by
    have hnat : (2432330631 : ℕ)^95*2000000000000^79 ≤ 365344651103^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2432330631 10000000000 365344651103 2000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (741351921/10000000000 : ℝ)^95 ≤ (4376919941877/100000000000000 : ℝ)^79 := by
    have hnat : (741351921 : ℕ)^95*100000000000000^79 ≤ 4376919941877^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      741351921 10000000000 4376919941877 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8077430869/10000000000 : ℝ)^95 ≤ (77355847484031/100000000000000 : ℝ)^79 := by
    have hnat : (8077430869 : ℕ)^95*100000000000000^79 ≤ 77355847484031^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8077430869 10000000000 77355847484031 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2432330631/10000000000 : ℝ), (741351921/10000000000 : ℝ), (8077430869/10000000000 : ℝ)] ![(365344651103/2000000000000 : ℝ), (4376919941877/100000000000000 : ℝ), (77355847484031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2432330631/10000000000 : ℝ)|^95 ≤ (365344651103/2000000000000 : ℝ)^79
        have hw : |(-2432330631/10000000000 : ℝ)|=(2432330631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(741351921/10000000000 : ℝ)|^95 ≤ (4376919941877/100000000000000 : ℝ)^79
        have hw : |(741351921/10000000000 : ℝ)|=(741351921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8077430869/10000000000 : ℝ)|^95 ≤ (77355847484031/100000000000000 : ℝ)^79
        have hw : |(8077430869/10000000000 : ℝ)|=(8077430869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329057_s0_8 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1885965857/10000000000 : ℝ)*x 0 + (-171745959/1250000000 : ℝ)*x 1 + (323097161/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1885965857/10000000000 : ℝ)^95 ≤ (6726304192731/50000000000000 : ℝ)^79 := by
    have hnat : (1885965857 : ℕ)^95*50000000000000^79 ≤ 6726304192731^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885965857 10000000000 6726304192731 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171745959/1250000000 : ℝ)^95 ≤ (9191565350113/100000000000000 : ℝ)^79 := by
    have hnat : (171745959 : ℕ)^95*100000000000000^79 ≤ 9191565350113^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171745959 1250000000 9191565350113 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323097161/400000000 : ℝ)^95 ≤ (38677913123903/50000000000000 : ℝ)^79 := by
    have hnat : (323097161 : ℕ)^95*50000000000000^79 ≤ 38677913123903^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323097161 400000000 38677913123903 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1885965857/10000000000 : ℝ), (-171745959/1250000000 : ℝ), (323097161/400000000 : ℝ)] ![(6726304192731/50000000000000 : ℝ), (9191565350113/100000000000000 : ℝ), (38677913123903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1885965857/10000000000 : ℝ)|^95 ≤ (6726304192731/50000000000000 : ℝ)^79
        have hw : |(1885965857/10000000000 : ℝ)|=(1885965857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-171745959/1250000000 : ℝ)|^95 ≤ (9191565350113/100000000000000 : ℝ)^79
        have hw : |(-171745959/1250000000 : ℝ)|=(171745959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323097161/400000000 : ℝ)|^95 ≤ (38677913123903/50000000000000 : ℝ)^79
        have hw : |(323097161/400000000 : ℝ)|=(323097161/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329057_s0_9 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (72998077/200000000 : ℝ)*x 0 + (3727233727/5000000000 : ℝ)*x 1 + (-947943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (72998077/200000000 : ℝ)^95 ≤ (14879884657027/50000000000000 : ℝ)^79 := by
    have hnat : (72998077 : ℕ)^95*50000000000000^79 ≤ 14879884657027^79*200000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72998077 200000000 14879884657027 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3727233727/5000000000 : ℝ)^95 ≤ (14047755744661/20000000000000 : ℝ)^79 := by
    have hnat : (3727233727 : ℕ)^95*20000000000000^79 ≤ 14047755744661^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3727233727 5000000000 14047755744661 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (947943/10000000000 : ℝ)^95 ≤ (90747219/6250000000000 : ℝ)^79 := by
    have hnat : (947943 : ℕ)^95*6250000000000^79 ≤ 90747219^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947943 10000000000 90747219 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(72998077/200000000 : ℝ), (3727233727/5000000000 : ℝ), (-947943/10000000000 : ℝ)] ![(14879884657027/50000000000000 : ℝ), (14047755744661/20000000000000 : ℝ), (90747219/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(72998077/200000000 : ℝ)|^95 ≤ (14879884657027/50000000000000 : ℝ)^79
        have hw : |(72998077/200000000 : ℝ)|=(72998077/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3727233727/5000000000 : ℝ)|^95 ≤ (14047755744661/20000000000000 : ℝ)^79
        have hw : |(3727233727/5000000000 : ℝ)|=(3727233727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-947943/10000000000 : ℝ)|^95 ≤ (90747219/6250000000000 : ℝ)^79
        have hw : |(-947943/10000000000 : ℝ)|=(947943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329057_s0_13 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1281970921/5000000000 : ℝ)*x 0 + (3727233727/5000000000 : ℝ)*x 1 + (1510287543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1281970921/5000000000 : ℝ)^95 ≤ (19462264423629/100000000000000 : ℝ)^79 := by
    have hnat : (1281970921 : ℕ)^95*100000000000000^79 ≤ 19462264423629^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281970921 5000000000 19462264423629 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3727233727/5000000000 : ℝ)^95 ≤ (14047755744661/20000000000000 : ℝ)^79 := by
    have hnat : (3727233727 : ℕ)^95*20000000000000^79 ≤ 14047755744661^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3727233727 5000000000 14047755744661 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1510287543/10000000000 : ℝ)^95 ≤ (2059791368941/20000000000000 : ℝ)^79 := by
    have hnat : (1510287543 : ℕ)^95*20000000000000^79 ≤ 2059791368941^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510287543 10000000000 2059791368941 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1281970921/5000000000 : ℝ), (3727233727/5000000000 : ℝ), (1510287543/10000000000 : ℝ)] ![(19462264423629/100000000000000 : ℝ), (14047755744661/20000000000000 : ℝ), (2059791368941/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1281970921/5000000000 : ℝ)|^95 ≤ (19462264423629/100000000000000 : ℝ)^79
        have hw : |(1281970921/5000000000 : ℝ)|=(1281970921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3727233727/5000000000 : ℝ)|^95 ≤ (14047755744661/20000000000000 : ℝ)^79
        have hw : |(3727233727/5000000000 : ℝ)|=(3727233727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1510287543/10000000000 : ℝ)|^95 ≤ (2059791368941/20000000000000 : ℝ)^79
        have hw : |(1510287543/10000000000 : ℝ)|=(1510287543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329057_s0_14 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1232642869/10000000000 : ℝ)*x 0 + (15506517/78125000 : ℝ)*x 1 + (8101060727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1232642869/10000000000 : ℝ)^95 ≤ (8066832574093/100000000000000 : ℝ)^79 := by
    have hnat : (1232642869 : ℕ)^95*100000000000000^79 ≤ 8066832574093^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232642869 10000000000 8066832574093 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15506517/78125000 : ℝ)^95 ≤ (14305108684999/100000000000000 : ℝ)^79 := by
    have hnat : (15506517 : ℕ)^95*100000000000000^79 ≤ 14305108684999^79*78125000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15506517 78125000 14305108684999 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8101060727/10000000000 : ℝ)^95 ≤ (7762805872977/10000000000000 : ℝ)^79 := by
    have hnat : (8101060727 : ℕ)^95*10000000000000^79 ≤ 7762805872977^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8101060727 10000000000 7762805872977 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1232642869/10000000000 : ℝ), (15506517/78125000 : ℝ), (8101060727/10000000000 : ℝ)] ![(8066832574093/100000000000000 : ℝ), (14305108684999/100000000000000 : ℝ), (7762805872977/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1232642869/10000000000 : ℝ)|^95 ≤ (8066832574093/100000000000000 : ℝ)^79
        have hw : |(-1232642869/10000000000 : ℝ)|=(1232642869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(15506517/78125000 : ℝ)|^95 ≤ (14305108684999/100000000000000 : ℝ)^79
        have hw : |(15506517/78125000 : ℝ)|=(15506517/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8101060727/10000000000 : ℝ)|^95 ≤ (7762805872977/10000000000000 : ℝ)^79
        have hw : |(8101060727/10000000000 : ℝ)|=(8101060727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329057_s0_15 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (417178441/5000000000 : ℝ)*x 0 + (-2327715031/10000000000 : ℝ)*x 1 + (4050530393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417178441/5000000000 : ℝ)^95 ≤ (2522675982757/50000000000000 : ℝ)^79 := by
    have hnat : (417178441 : ℕ)^95*50000000000000^79 ≤ 2522675982757^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417178441 5000000000 2522675982757 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2327715031/10000000000 : ℝ)^95 ≤ (17326588607297/100000000000000 : ℝ)^79 := by
    have hnat : (2327715031 : ℕ)^95*100000000000000^79 ≤ 17326588607297^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2327715031 10000000000 17326588607297 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4050530393/5000000000 : ℝ)^95 ≤ (1940701485241/2500000000000 : ℝ)^79 := by
    have hnat : (4050530393 : ℕ)^95*2500000000000^79 ≤ 1940701485241^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4050530393 5000000000 1940701485241 2500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(417178441/5000000000 : ℝ), (-2327715031/10000000000 : ℝ), (4050530393/5000000000 : ℝ)] ![(2522675982757/50000000000000 : ℝ), (17326588607297/100000000000000 : ℝ), (1940701485241/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(417178441/5000000000 : ℝ)|^95 ≤ (2522675982757/50000000000000 : ℝ)^79
        have hw : |(417178441/5000000000 : ℝ)|=(417178441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2327715031/10000000000 : ℝ)|^95 ≤ (17326588607297/100000000000000 : ℝ)^79
        have hw : |(-2327715031/10000000000 : ℝ)|=(2327715031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4050530393/5000000000 : ℝ)|^95 ≤ (1940701485241/2500000000000 : ℝ)^79
        have hw : |(4050530393/5000000000 : ℝ)|=(4050530393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329057_s0_16 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3881884921/5000000000 : ℝ)*x 0 + (1643615927/5000000000 : ℝ)*x 1 + (-48059/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3881884921/5000000000 : ℝ)^95 ≤ (36878979071221/50000000000000 : ℝ)^79 := by
    have hnat : (3881884921 : ℕ)^95*50000000000000^79 ≤ 36878979071221^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3881884921 5000000000 36878979071221 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1643615927/5000000000 : ℝ)^95 ≤ (2624056547403/10000000000000 : ℝ)^79 := by
    have hnat : (1643615927 : ℕ)^95*10000000000000^79 ≤ 2624056547403^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1643615927 5000000000 2624056547403 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (48059/500000000 : ℝ)^95 ≤ (1476371171/100000000000000 : ℝ)^79 := by
    have hnat : (48059 : ℕ)^95*100000000000000^79 ≤ 1476371171^79*500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48059 500000000 1476371171 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3881884921/5000000000 : ℝ), (1643615927/5000000000 : ℝ), (-48059/500000000 : ℝ)] ![(36878979071221/50000000000000 : ℝ), (2624056547403/10000000000000 : ℝ), (1476371171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3881884921/5000000000 : ℝ)|^95 ≤ (36878979071221/50000000000000 : ℝ)^79
        have hw : |(3881884921/5000000000 : ℝ)|=(3881884921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1643615927/5000000000 : ℝ)|^95 ≤ (2624056547403/10000000000000 : ℝ)^79
        have hw : |(1643615927/5000000000 : ℝ)|=(1643615927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-48059/500000000 : ℝ)|^95 ≤ (1476371171/100000000000000 : ℝ)^79
        have hw : |(-48059/500000000 : ℝ)|=(48059/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329057_s0_20 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1424636463/2000000000 : ℝ)*x 0 + (2966517151/10000000000 : ℝ)*x 1 + (755490631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1424636463/2000000000 : ℝ)^95 ≤ (16625545495417/25000000000000 : ℝ)^79 := by
    have hnat : (1424636463 : ℕ)^95*25000000000000^79 ≤ 16625545495417^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1424636463 2000000000 16625545495417 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2966517151/10000000000 : ℝ)^95 ≤ (5798293049001/25000000000000 : ℝ)^79 := by
    have hnat : (2966517151 : ℕ)^95*25000000000000^79 ≤ 5798293049001^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2966517151 10000000000 5798293049001 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (755490631/5000000000 : ℝ)^95 ≤ (1288080727257/12500000000000 : ℝ)^79 := by
    have hnat : (755490631 : ℕ)^95*12500000000000^79 ≤ 1288080727257^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      755490631 5000000000 1288080727257 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1424636463/2000000000 : ℝ), (2966517151/10000000000 : ℝ), (755490631/5000000000 : ℝ)] ![(16625545495417/25000000000000 : ℝ), (5798293049001/25000000000000 : ℝ), (1288080727257/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1424636463/2000000000 : ℝ)|^95 ≤ (16625545495417/25000000000000 : ℝ)^79
        have hw : |(1424636463/2000000000 : ℝ)|=(1424636463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2966517151/10000000000 : ℝ)|^95 ≤ (5798293049001/25000000000000 : ℝ)^79
        have hw : |(2966517151/10000000000 : ℝ)|=(2966517151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(755490631/5000000000 : ℝ)|^95 ≤ (1288080727257/12500000000000 : ℝ)^79
        have hw : |(755490631/5000000000 : ℝ)|=(755490631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329057_s0_21 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1166162081/2500000000 : ℝ)*x 0 + (460393147/2500000000 : ℝ)*x 1 + (1066639901/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1166162081/2500000000 : ℝ)^95 ≤ (7994186042343/20000000000000 : ℝ)^79 := by
    have hnat : (1166162081 : ℕ)^95*20000000000000^79 ≤ 7994186042343^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1166162081 2500000000 7994186042343 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (460393147/2500000000 : ℝ)^95 ≤ (6536365560973/50000000000000 : ℝ)^79 := by
    have hnat : (460393147 : ℕ)^95*50000000000000^79 ≤ 6536365560973^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460393147 2500000000 6536365560973 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1066639901/2000000000 : ℝ)^95 ≤ (46956338650599/100000000000000 : ℝ)^79 := by
    have hnat : (1066639901 : ℕ)^95*100000000000000^79 ≤ 46956338650599^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066639901 2000000000 46956338650599 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1166162081/2500000000 : ℝ), (460393147/2500000000 : ℝ), (1066639901/2000000000 : ℝ)] ![(7994186042343/20000000000000 : ℝ), (6536365560973/50000000000000 : ℝ), (46956338650599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1166162081/2500000000 : ℝ)|^95 ≤ (7994186042343/20000000000000 : ℝ)^79
        have hw : |(-1166162081/2500000000 : ℝ)|=(1166162081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(460393147/2500000000 : ℝ)|^95 ≤ (6536365560973/50000000000000 : ℝ)^79
        have hw : |(460393147/2500000000 : ℝ)|=(460393147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1066639901/2000000000 : ℝ)|^95 ≤ (46956338650599/100000000000000 : ℝ)^79
        have hw : |(1066639901/2000000000 : ℝ)|=(1066639901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329057_s0_22 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (151366597/2500000000 : ℝ)*x 0 + (-140283797/312500000 : ℝ)*x 1 + (6393739731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (151366597/2500000000 : ℝ)^95 ≤ (1715515847559/50000000000000 : ℝ)^79 := by
    have hnat : (151366597 : ℕ)^95*50000000000000^79 ≤ 1715515847559^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151366597 2500000000 1715515847559 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140283797/312500000 : ℝ)^95 ≤ (19084394219451/50000000000000 : ℝ)^79 := by
    have hnat : (140283797 : ℕ)^95*50000000000000^79 ≤ 19084394219451^79*312500000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140283797 312500000 19084394219451 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6393739731/10000000000 : ℝ)^95 ≤ (5840017985773/10000000000000 : ℝ)^79 := by
    have hnat : (6393739731 : ℕ)^95*10000000000000^79 ≤ 5840017985773^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6393739731 10000000000 5840017985773 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(151366597/2500000000 : ℝ), (-140283797/312500000 : ℝ), (6393739731/10000000000 : ℝ)] ![(1715515847559/50000000000000 : ℝ), (19084394219451/50000000000000 : ℝ), (5840017985773/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(151366597/2500000000 : ℝ)|^95 ≤ (1715515847559/50000000000000 : ℝ)^79
        have hw : |(151366597/2500000000 : ℝ)|=(151366597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-140283797/312500000 : ℝ)|^95 ≤ (19084394219451/50000000000000 : ℝ)^79
        have hw : |(-140283797/312500000 : ℝ)|=(140283797/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6393739731/10000000000 : ℝ)|^95 ≤ (5840017985773/10000000000000 : ℝ)^79
        have hw : |(6393739731/10000000000 : ℝ)|=(6393739731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329057_s0_23 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2995113527/5000000000 : ℝ)*x 0 + (655376707/1250000000 : ℝ)*x 1 + (29357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2995113527/5000000000 : ℝ)^95 ≤ (26998430042561/50000000000000 : ℝ)^79 := by
    have hnat : (2995113527 : ℕ)^95*50000000000000^79 ≤ 26998430042561^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2995113527 5000000000 26998430042561 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655376707/1250000000 : ℝ)^95 ≤ (23001558831311/50000000000000 : ℝ)^79 := by
    have hnat : (655376707 : ℕ)^95*50000000000000^79 ≤ 23001558831311^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655376707 1250000000 23001558831311 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29357/10000000000 : ℝ)^95 ≤ (2224581/10000000000000 : ℝ)^79 := by
    have hnat : (29357 : ℕ)^95*10000000000000^79 ≤ 2224581^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29357 10000000000 2224581 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2995113527/5000000000 : ℝ), (655376707/1250000000 : ℝ), (29357/10000000000 : ℝ)] ![(26998430042561/50000000000000 : ℝ), (23001558831311/50000000000000 : ℝ), (2224581/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2995113527/5000000000 : ℝ)|^95 ≤ (26998430042561/50000000000000 : ℝ)^79
        have hw : |(2995113527/5000000000 : ℝ)|=(2995113527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655376707/1250000000 : ℝ)|^95 ≤ (23001558831311/50000000000000 : ℝ)^79
        have hw : |(655376707/1250000000 : ℝ)|=(655376707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(29357/10000000000 : ℝ)|^95 ≤ (2224581/10000000000000 : ℝ)^79
        have hw : |(29357/10000000000 : ℝ)|=(29357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329057_s0_27 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (980984723/5000000000 : ℝ)*x 0 + (655376707/1250000000 : ℝ)*x 1 + (1164191167/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (980984723/5000000000 : ℝ)^95 ≤ (22571479031/160000000000 : ℝ)^79 := by
    have hnat : (980984723 : ℕ)^95*160000000000^79 ≤ 22571479031^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980984723 5000000000 22571479031 160000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655376707/1250000000 : ℝ)^95 ≤ (23001558831311/50000000000000 : ℝ)^79 := by
    have hnat : (655376707 : ℕ)^95*50000000000000^79 ≤ 23001558831311^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655376707 1250000000 23001558831311 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1164191167/2500000000 : ℝ)^95 ≤ (19944853967429/50000000000000 : ℝ)^79 := by
    have hnat : (1164191167 : ℕ)^95*50000000000000^79 ≤ 19944853967429^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1164191167 2500000000 19944853967429 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(980984723/5000000000 : ℝ), (655376707/1250000000 : ℝ), (1164191167/2500000000 : ℝ)] ![(22571479031/160000000000 : ℝ), (23001558831311/50000000000000 : ℝ), (19944853967429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(980984723/5000000000 : ℝ)|^95 ≤ (22571479031/160000000000 : ℝ)^79
        have hw : |(980984723/5000000000 : ℝ)|=(980984723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655376707/1250000000 : ℝ)|^95 ≤ (23001558831311/50000000000000 : ℝ)^79
        have hw : |(655376707/1250000000 : ℝ)|=(655376707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1164191167/2500000000 : ℝ)|^95 ≤ (19944853967429/50000000000000 : ℝ)^79
        have hw : |(1164191167/2500000000 : ℝ)|=(1164191167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329057_s1_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3204388657/10000000000 : ℝ)*x 0 + (3203427833/10000000000 : ℝ)*x 1 + (553625391/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3204388657/10000000000 : ℝ)^95 ≤ (25447372370797/100000000000000 : ℝ)^79 := by
    have hnat : (3204388657 : ℕ)^95*100000000000000^79 ≤ 25447372370797^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3204388657 10000000000 25447372370797 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3203427833/10000000000 : ℝ)^95 ≤ (25438196972463/100000000000000 : ℝ)^79 := by
    have hnat : (3203427833 : ℕ)^95*100000000000000^79 ≤ 25438196972463^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3203427833 10000000000 25438196972463 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553625391/1000000000 : ℝ)^95 ≤ (2455721532551/5000000000000 : ℝ)^79 := by
    have hnat : (553625391 : ℕ)^95*5000000000000^79 ≤ 2455721532551^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553625391 1000000000 2455721532551 5000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3204388657/10000000000 : ℝ), (3203427833/10000000000 : ℝ), (553625391/1000000000 : ℝ)] ![(25447372370797/100000000000000 : ℝ), (25438196972463/100000000000000 : ℝ), (2455721532551/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3204388657/10000000000 : ℝ)|^95 ≤ (25447372370797/100000000000000 : ℝ)^79
        have hw : |(-3204388657/10000000000 : ℝ)|=(3204388657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3203427833/10000000000 : ℝ)|^95 ≤ (25438196972463/100000000000000 : ℝ)^79
        have hw : |(3203427833/10000000000 : ℝ)|=(3203427833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(553625391/1000000000 : ℝ)|^95 ≤ (2455721532551/5000000000000 : ℝ)^79
        have hw : |(553625391/1000000000 : ℝ)|=(553625391/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329057_s1_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (640681697/2000000000 : ℝ)*x 0 + (-640489591/2000000000 : ℝ)*x 1 + (4326569/7812500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (640681697/2000000000 : ℝ)^95 ≤ (25438012214269/100000000000000 : ℝ)^79 := by
    have hnat : (640681697 : ℕ)^95*100000000000000^79 ≤ 25438012214269^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640681697 2000000000 25438012214269 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (640489591/2000000000 : ℝ)^95 ≤ (12714420095907/50000000000000 : ℝ)^79 := by
    have hnat : (640489591 : ℕ)^95*50000000000000^79 ≤ 12714420095907^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640489591 2000000000 12714420095907 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4326569/7812500 : ℝ)^95 ≤ (122832868957/250000000000 : ℝ)^79 := by
    have hnat : (4326569 : ℕ)^95*250000000000^79 ≤ 122832868957^79*7812500^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326569 7812500 122832868957 250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(640681697/2000000000 : ℝ), (-640489591/2000000000 : ℝ), (4326569/7812500 : ℝ)] ![(25438012214269/100000000000000 : ℝ), (12714420095907/50000000000000 : ℝ), (122832868957/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(640681697/2000000000 : ℝ)|^95 ≤ (25438012214269/100000000000000 : ℝ)^79
        have hw : |(640681697/2000000000 : ℝ)|=(640681697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-640489591/2000000000 : ℝ)|^95 ≤ (12714420095907/50000000000000 : ℝ)^79
        have hw : |(-640489591/2000000000 : ℝ)|=(640489591/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4326569/7812500 : ℝ)|^95 ≤ (122832868957/250000000000 : ℝ)^79
        have hw : |(4326569/7812500 : ℝ)|=(4326569/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329057_s1_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1342013989/2500000000 : ℝ)*x 0 + (2684811723/5000000000 : ℝ)*x 1 + (-174721531/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342013989/2500000000 : ℝ)^95 ≤ (23662816609649/50000000000000 : ℝ)^79 := by
    have hnat : (1342013989 : ℕ)^95*50000000000000^79 ≤ 23662816609649^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342013989 2500000000 23662816609649 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2684811723/5000000000 : ℝ)^95 ≤ (11835562946199/25000000000000 : ℝ)^79 := by
    have hnat : (2684811723 : ℕ)^95*25000000000000^79 ≤ 11835562946199^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684811723 5000000000 11835562946199 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (174721531/2000000000 : ℝ)^95 ≤ (1066422995193/20000000000000 : ℝ)^79 := by
    have hnat : (174721531 : ℕ)^95*20000000000000^79 ≤ 1066422995193^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174721531 2000000000 1066422995193 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342013989/2500000000 : ℝ), (2684811723/5000000000 : ℝ), (-174721531/2000000000 : ℝ)] ![(23662816609649/50000000000000 : ℝ), (11835562946199/25000000000000 : ℝ), (1066422995193/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342013989/2500000000 : ℝ)|^95 ≤ (23662816609649/50000000000000 : ℝ)^79
        have hw : |(1342013989/2500000000 : ℝ)|=(1342013989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2684811723/5000000000 : ℝ)|^95 ≤ (11835562946199/25000000000000 : ℝ)^79
        have hw : |(2684811723/5000000000 : ℝ)|=(2684811723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-174721531/2000000000 : ℝ)|^95 ≤ (1066422995193/20000000000000 : ℝ)^79
        have hw : |(-174721531/2000000000 : ℝ)|=(174721531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329057_s1_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4204528247/10000000000 : ℝ)*x 0 + (4205755983/10000000000 : ℝ)*x 1 + (3616334991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4204528247/10000000000 : ℝ)^95 ≤ (35278337842309/100000000000000 : ℝ)^79 := by
    have hnat : (4204528247 : ℕ)^95*100000000000000^79 ≤ 35278337842309^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204528247 10000000000 35278337842309 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4205755983/10000000000 : ℝ)^95 ≤ (35290725956097/100000000000000 : ℝ)^79 := by
    have hnat : (4205755983 : ℕ)^95*100000000000000^79 ≤ 35290725956097^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205755983 10000000000 35290725956097 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3616334991/10000000000 : ℝ)^95 ≤ (29430936186543/100000000000000 : ℝ)^79 := by
    have hnat : (3616334991 : ℕ)^95*100000000000000^79 ≤ 29430936186543^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3616334991 10000000000 29430936186543 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4204528247/10000000000 : ℝ), (4205755983/10000000000 : ℝ), (3616334991/10000000000 : ℝ)] ![(35278337842309/100000000000000 : ℝ), (35290725956097/100000000000000 : ℝ), (29430936186543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4204528247/10000000000 : ℝ)|^95 ≤ (35278337842309/100000000000000 : ℝ)^79
        have hw : |(4204528247/10000000000 : ℝ)|=(4204528247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4205755983/10000000000 : ℝ)|^95 ≤ (35290725956097/100000000000000 : ℝ)^79
        have hw : |(4205755983/10000000000 : ℝ)|=(4205755983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3616334991/10000000000 : ℝ)|^95 ≤ (29430936186543/100000000000000 : ℝ)^79
        have hw : |(3616334991/10000000000 : ℝ)|=(3616334991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329057 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]]) : False := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (160257/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s0_pow0 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1266528166513657/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(813984837038199/10000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (93/16 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^93 ≤ (1 : ℝ)^16 := by
      have hnat : (1 : ℕ)^93*1^16 ≤ 1^16*1^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (11266528166513657/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (2 : ℝ)^16 ≤ (11266528166513657/10000000000000000 : ℝ)^93 := by
      have hnat : (2 : ℕ)^16*10000000000000000^93 ≤ 11266528166513657^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 11266528166513657 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11266528166513657/10000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (755032062721991/625000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (3 : ℝ)^16 ≤ (755032062721991/625000000000000 : ℝ)^93 := by
      have hnat : (3 : ℕ)^16*625000000000000^93 ≤ 755032062721991^93*1^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 755032062721991 625000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (755032062721991/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1 : ℝ)) (alpha := (1266528166513657/10000000000000000 : ℝ)) (beta := (813984837038199/10000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1266528166513657/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(813984837038199/10000000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-1445994231/5000000000 : ℝ)*X 0 0+(1445994813/5000000000 : ℝ)*X 0 1+(6083679339/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_1 : ((578397693/2000000000 : ℝ)*X 1 0+(-2891989629/10000000000 : ℝ)*X 1 1+(6083679333/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5619139651/10000000000 : ℝ)*X 2 0+(351196149/625000000 : ℝ)*X 2 1+(-3909/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-2432330631/10000000000 : ℝ)*X 0 0+(741351921/10000000000 : ℝ)*X 0 1+(8077430869/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1885965857/10000000000 : ℝ)*X 1 0+(-171745959/1250000000 : ℝ)*X 1 1+(323097161/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((72998077/200000000 : ℝ)*X 2 0+(3727233727/5000000000 : ℝ)*X 2 1+(-947943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((1281970921/5000000000 : ℝ)*X 0 0+(3727233727/5000000000 : ℝ)*X 0 1+(1510287543/10000000000 : ℝ)*X 0 2+(1281970921/5000000000 : ℝ)*X 1 0+(3727233727/5000000000 : ℝ)*X 1 1+(1510287543/10000000000 : ℝ)*X 1 2+(1281970921/5000000000 : ℝ)*X 2 0+(3727233727/5000000000 : ℝ)*X 2 1+(1510287543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-1232642869/10000000000 : ℝ)*X 0 0+(15506517/78125000 : ℝ)*X 0 1+(8101060727/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((417178441/5000000000 : ℝ)*X 1 0+(-2327715031/10000000000 : ℝ)*X 1 1+(4050530393/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((3881884921/5000000000 : ℝ)*X 2 0+(1643615927/5000000000 : ℝ)*X 2 1+(-48059/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1424636463/2000000000 : ℝ)*X 0 0+(2966517151/10000000000 : ℝ)*X 0 1+(755490631/5000000000 : ℝ)*X 0 2+(1424636463/2000000000 : ℝ)*X 1 0+(2966517151/10000000000 : ℝ)*X 1 1+(755490631/5000000000 : ℝ)*X 1 2+(1424636463/2000000000 : ℝ)*X 2 0+(2966517151/10000000000 : ℝ)*X 2 1+(755490631/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-1166162081/2500000000 : ℝ)*X 0 0+(460393147/2500000000 : ℝ)*X 0 1+(1066639901/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((151366597/2500000000 : ℝ)*X 1 0+(-140283797/312500000 : ℝ)*X 1 1+(6393739731/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((2995113527/5000000000 : ℝ)*X 2 0+(655376707/1250000000 : ℝ)*X 2 1+(29357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((980984723/5000000000 : ℝ)*X 0 0+(655376707/1250000000 : ℝ)*X 0 1+(1164191167/2500000000 : ℝ)*X 0 2+(980984723/5000000000 : ℝ)*X 1 0+(655376707/1250000000 : ℝ)*X 1 1+(1164191167/2500000000 : ℝ)*X 1 2+(980984723/5000000000 : ℝ)*X 2 0+(655376707/1250000000 : ℝ)*X 2 1+(1164191167/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((1888/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1888/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (37771525520725917797007/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (114141644709/500000000000 : ℝ)*(base5) + (122225486729/100000000000 : ℝ)*(base7) + (47675028449/1000000000000 : ℝ)*(base59) + (1580252381469/1000000000000 : ℝ)*(major_s0_0) + (1580252381469/1000000000000 : ℝ)*(major_s0_1) + (1580252381469/1000000000000 : ℝ)*(major_s0_2) + (1429581/200000000000 : ℝ)*(sp_s0_0) + (5904347/1000000000000 : ℝ)*(sp_s0_1) + (224610242423/125000000000 : ℝ)*(sp_s0_7) + (1796847886963/1000000000000 : ℝ)*(sp_s0_8) + (2025180949743/1000000000000 : ℝ)*(sp_s0_9) + (852328658359/500000000000 : ℝ)*(sp_s0_13) + (1714607/200000000000 : ℝ)*(sp_s0_14) + (8773803/200000000000 : ℝ)*(sp_s0_15) + (355342869423/500000000000 : ℝ)*(f.failure) + (71875906413/40000000000 : ℝ)*(f.sum) + (1091933727/10000000000000000000000 : ℝ)*base62 + (927423401265669/10000000000000000000000000000 : ℝ)*base65 + (8245026462734331/10000000000000000000000000000 : ℝ)*base67 + (1698441205777867/10000000000000000000000000000 : ℝ)*base69 + (612673509256099/5000000000000000000000000000 : ℝ)*base70 + (457794982734331/10000000000000000000000000000 : ℝ)*base73 + (2414128256222133/10000000000000000000000000000 : ℝ)*base75 + (3468393068222133/10000000000000000000000000000 : ℝ)*base77 + (290438660234331/5000000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (7353/12500000000000000 : ℝ)*base86 + (7353/12500000000000000 : ℝ)*base88 + (7353/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30079/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30079/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3230572834963609098921/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (236552392557/1000000000000 : ℝ)*(base5) + (2440314079/2000000000 : ℝ)*(base7) + (3348063087/200000000000 : ℝ)*(base60) + (62598784569/40000000000 : ℝ)*(major_s0_0) + (62598784569/40000000000 : ℝ)*(major_s0_1) + (62598784569/40000000000 : ℝ)*(major_s0_2) + (156847/20000000000 : ℝ)*(sp_s0_0) + (6684987/1000000000000 : ℝ)*(sp_s0_1) + (51138623/1000000000000 : ℝ)*(sp_s0_7) + (354853308611/200000000000 : ℝ)*(sp_s0_14) + (1774316702403/1000000000000 : ℝ)*(sp_s0_15) + (402175583317/200000000000 : ℝ)*(sp_s0_16) + (84370863907/50000000000 : ℝ)*(sp_s0_20) + (1068319/500000000000 : ℝ)*(sp_s0_22) + (703812631197/1000000000000 : ℝ)*(f.failure) + (443581381007/250000000000 : ℝ)*(f.sum) + (1152039377/2500000000000000000000 : ℝ)*base63 + (35936532871231/400000000000000000000000000 : ℝ)*base64 + (99596276671231/400000000000000000000000000 : ℝ)*base67 + (338702458841167/400000000000000000000000000 : ℝ)*base69 + (74506768136199/200000000000000000000000000 : ℝ)*base70 + (151506445271231/400000000000000000000000000 : ℝ)*base73 + (211025392558833/400000000000000000000000000 : ℝ)*base75 + (182403230158833/400000000000000000000000000 : ℝ)*base77 + (12410377151231/200000000000000000000000000 : ℝ)*base79 + (14967/25000000000000000 : ℝ)*base86 + (14967/25000000000000000 : ℝ)*base88 + (14967/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(23359/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(23359/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (51749094958567300814151/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (937488230037/1000000000000 : ℝ)*(base5) + (408224860519/1000000000000 : ℝ)*(base7) + (5542111/1000000000000 : ℝ)*(base40) + (186888064693/1000000000000 : ℝ)*(base50) + (412578667693/500000000000 : ℝ)*(base59) + (1277336874117/1000000000000 : ℝ)*(major_s0_0) + (1277336874117/1000000000000 : ℝ)*(major_s0_1) + (1277336874117/1000000000000 : ℝ)*(major_s0_2) + (26073/62500000000 : ℝ)*(sp_s0_0) + (131881311/1000000000000 : ℝ)*(sp_s0_2) + (1762144471897/1000000000000 : ℝ)*(sp_s0_21) + (881072444533/500000000000 : ℝ)*(sp_s0_22) + (84359413681/31250000000 : ℝ)*(sp_s0_23) + (2259620073/50000000000 : ℝ)*(sp_s0_27) + (287227885489/500000000000 : ℝ)*(f.failure) + (881072444533/500000000000 : ℝ)*(f.sum) + (159231229/2500000000000000000000 : ℝ)*base62 + (2951547395283/10000000000000000000000000000 : ℝ)*base64 + (4099836966395283/10000000000000000000000000000 : ℝ)*base67 + (2972589061684131/10000000000000000000000000000 : ℝ)*base69 + (1610375754539707/5000000000000000000000000000 : ℝ)*base70 + (137458657395283/10000000000000000000000000000 : ℝ)*base73 + (7812527781315869/10000000000000000000000000000 : ℝ)*base75 + (4343939434315869/10000000000000000000000000000 : ℝ)*base77 + (2885937629604717/5000000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (14479/12500000000000000 : ℝ)*base86 + (14479/12500000000000000 : ℝ)*base88 + (14479/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have s1_pow0 : (1888/3125 : ℝ) ^ (93/16 : ℝ) ≤ (5344976691149605019/100000000000000000000 : ℝ) := by
    have hpowers : (1888/3125 : ℝ)^93 ≤ (5344976691149605019/100000000000000000000 : ℝ)^16 := by
      have hnat : (1888 : ℕ)^93*100000000000000000000^16 ≤ 5344976691149605019^16*3125^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1888 3125 5344976691149605019 100000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1888/3125 : ℝ)) (X := (5344976691149605019/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (105344976691149605019/100000000000000000000 : ℝ) ≤ (2522496430228769/2500000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (105344976691149605019/100000000000000000000 : ℝ)^16 ≤ (2522496430228769/2500000000000000 : ℝ)^93 := by
      have hnat : (105344976691149605019 : ℕ)^16*2500000000000000^93 ≤ 2522496430228769^93*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105344976691149605019 100000000000000000000 2522496430228769 2500000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2522496430228769/2500000000000000 : ℝ)) (X := (105344976691149605019/100000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (55344976691149605019/50000000000000000000 : ℝ) ≤ (1272033419064687/1250000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (55344976691149605019/50000000000000000000 : ℝ)^16 ≤ (1272033419064687/1250000000000000 : ℝ)^93 := by
      have hnat : (55344976691149605019 : ℕ)^16*1250000000000000^93 ≤ 1272033419064687^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55344976691149605019 50000000000000000000 1272033419064687 1250000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1272033419064687/1250000000000000 : ℝ)) (X := (55344976691149605019/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(22496430228769/1510400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(4314081580121/302080000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (1888/3125 : ℝ)) (alpha := (22496430228769/1510400000000000 : ℝ)) (beta := (4314081580121/302080000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1888/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(22496430228769/1510400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(4314081580121/302080000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (30079/50000 : ℝ) ^ (93/16 : ℝ) ≤ (521366143686889837/10000000000000000000 : ℝ) := by
    have hpowers : (30079/50000 : ℝ)^93 ≤ (521366143686889837/10000000000000000000 : ℝ)^16 := by
      have hnat : (30079 : ℕ)^93*10000000000000000000^16 ≤ 521366143686889837^16*50000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30079 50000 521366143686889837 10000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (30079/50000 : ℝ)) (X := (521366143686889837/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (10521366143686889837/10000000000000000000 : ℝ) ≤ (1008782074456291/1000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (10521366143686889837/10000000000000000000 : ℝ)^16 ≤ (1008782074456291/1000000000000000 : ℝ)^93 := by
      have hnat : (10521366143686889837 : ℕ)^16*1000000000000000^93 ≤ 1008782074456291^93*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10521366143686889837 10000000000000000000 1008782074456291 1000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1008782074456291/1000000000000000 : ℝ)) (X := (10521366143686889837/10000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (5521366143686889837/5000000000000000000 : ℝ) ≤ (5086054652256711/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (5521366143686889837/5000000000000000000 : ℝ)^16 ≤ (5086054652256711/5000000000000000 : ℝ)^93 := by
      have hnat : (5521366143686889837 : ℕ)^16*5000000000000000^93 ≤ 5086054652256711^93*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5521366143686889837 5000000000000000000 5086054652256711 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5086054652256711/5000000000000000 : ℝ)) (X := (5521366143686889837/5000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(8782074456291/601580000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(5268034996907/375987500000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (30079/50000 : ℝ)) (alpha := (8782074456291/601580000000000 : ℝ)) (beta := (5268034996907/375987500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (30079/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(8782074456291/601580000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(5268034996907/375987500000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (23359/100000 : ℝ) ^ (93/16 : ℝ) ≤ (21337341534157857/100000000000000000000 : ℝ) := by
    have hpowers : (23359/100000 : ℝ)^93 ≤ (21337341534157857/100000000000000000000 : ℝ)^16 := by
      have hnat : (23359 : ℕ)^93*100000000000000000000^16 ≤ 21337341534157857^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23359 100000 21337341534157857 100000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23359/100000 : ℝ)) (X := (21337341534157857/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (100021337341534157857/100000000000000000000 : ℝ) ≤ (5000183530812981/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (100021337341534157857/100000000000000000000 : ℝ)^16 ≤ (5000183530812981/5000000000000000 : ℝ)^93 := by
      have hnat : (100021337341534157857 : ℕ)^16*5000000000000000^93 ≤ 5000183530812981^93*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100021337341534157857 100000000000000000000 5000183530812981 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000183530812981/5000000000000000 : ℝ)) (X := (100021337341534157857/100000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (50021337341534157857/50000000000000000000 : ℝ) ≤ (5000367029212451/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (50021337341534157857/50000000000000000000 : ℝ)^16 ≤ (5000367029212451/5000000000000000 : ℝ)^93 := by
      have hnat : (50021337341534157857 : ℕ)^16*5000000000000000^93 ≤ 5000367029212451^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021337341534157857 50000000000000000000 5000367029212451 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000367029212451/5000000000000000 : ℝ)) (X := (50021337341534157857/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(183530812981/1167950000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(18349839947/116795000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (23359/100000 : ℝ)) (alpha := (183530812981/1167950000000000 : ℝ)) (beta := (18349839947/116795000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (23359/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(183530812981/1167950000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(18349839947/116795000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-3204388657/10000000000 : ℝ)*X 0 0+(3203427833/10000000000 : ℝ)*X 0 1+(553625391/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((640681697/2000000000 : ℝ)*X 1 0+(-640489591/2000000000 : ℝ)*X 1 1+(4326569/7812500 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1342013989/2500000000 : ℝ)*X 2 0+(2684811723/5000000000 : ℝ)*X 2 1+(-174721531/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4204528247/10000000000 : ℝ)*X 0 0+(4205755983/10000000000 : ℝ)*X 0 1+(3616334991/10000000000 : ℝ)*X 0 2+(4204528247/10000000000 : ℝ)*X 1 0+(4205755983/10000000000 : ℝ)*X 1 1+(3616334991/10000000000 : ℝ)*X 1 2+(4204528247/10000000000 : ℝ)*X 2 0+(4205755983/10000000000 : ℝ)*X 2 1+(3616334991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329057_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have hsep : (-129267/12500 : ℝ) < ((-55589/25000 : ℝ)*P 0+(-55589/25000 : ℝ)*P 1+(-55589/25000 : ℝ)*P 2+(1 : ℝ)*T) := by
    have hcertificate_margin : (-129267/12500 : ℝ) < (-55542841385453693633227785049034157/5414440006400000000000000000000000 : ℝ) := by norm_num
    linear_combination (132389/250000000000 : ℝ)*(base8) + (1352211/1000000000000 : ℝ)*(base19) + (504361/1000000000000 : ℝ)*(base21) + (184641/500000000000 : ℝ)*(base33) + (85717/500000000000 : ℝ)*(base49) + (57213/200000000000 : ℝ)*(base50) + (1414622487463/1000000000000 : ℝ)*(base59) + (353687956951/500000000000 : ℝ)*(base60) + (1111779815359/500000000000 : ℝ)*(major_s1_0) + (55589/25000 : ℝ)*(major_s1_1) + (55589/25000 : ℝ)*(major_s1_2) + (1709713061059/500000000000 : ℝ)*(sp_s1_0) + (3419424930183/1000000000000 : ℝ)*(sp_s1_1) + (213714111127/62500000000 : ℝ)*(sp_s1_2) + (1 : ℝ)*(sp_s1_6) + (136777066067/40000000000 : ℝ)*(f.sum) + (473672526677564651/501868115000000000000000000000 : ℝ)*base62 + (21114980821227/116795000000000000000000000 : ℝ)*base65 + (11453120553549/15039500000000000000000000 : ℝ)*base67 + (46581981910809/46718000000000000000000000 : ℝ)*base68 + (2791338860406310689/17640716800000000000000000000000 : ℝ)*base71 + (104711298267801/151040000000000000000000000 : ℝ)*base72 + (3407235795137/4699843750000000000000000 : ℝ)*base74 + (130746731561631/755200000000000000000000000 : ℝ)*base77 + (2070220019108598041/4543132160000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base83 + hcertificate_margin
  linarith only [hsep,f.failure]

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
namespace HlawkaSchatten.DiagonalCutoff4
theorem coarse_distinct_p029_b027 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 57 ≤ c.val) (hhi : c.val < 58)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  have hc : c=57 := by omega
  rcases hc with rfl
  · exact collision_c329057 p hpa (by linarith only [hpb]) X hX

end HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (c : Fin 88) (hlo : 57 ≤ c.val) (hhi : c.val < 58)
    (hn63 : c ≠ 63) (hn87 : c ≠ 87)
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X (distinctOrders c) (distinctSigns c)) : False := by
  exact HlawkaSchatten.DiagonalCutoff4.coarse_distinct_p029_b027 p hpa hpb c hlo hhi hn63 hn87 X hX

#print axioms solution
